from __future__ import annotations

from dataclasses import dataclass
import re
from typing import NoReturn

from ctac.ast.nodes import (
    ApplyExpr,
    AssertCmd,
    AssignExpCmd,
    AssignHavocCmd,
    AssumeExpCmd,
    ConstExpr,
    JumpCmd,
    JumpiCmd,
    LabelCmd,
    RawCmd,
    SymbolRef,
    TacCmd,
    TacExpr,
)
from ctac.graph import Cfg
from ctac.ir.models import TacBlock, TacFile, TacProgram
from ctac.smt.vc.builder import BlockBuilder, VCBuilder, sanitize_name
from ctac.smt.vc.bytemap import MapTerm
from ctac.smt.vc.terms import (
    Bool,
    Int,
    Sort,
    Term,
    add,
    and_,
    app,
    div,
    eq,
    false,
    ge,
    gt,
    le,
    lt,
    mod,
    mul,
    not_,
    or_,
    sub,
    true,
)


class VCLoweringError(ValueError):
    """TAC construct is not supported by the VC symbolic executor."""


@dataclass(frozen=True)
class TacLoweringOptions:
    inline_defs: bool = False
    block_order: str = "program"  # "program" | "topological"
    skip_command_points: frozenset[tuple[str, int]] = frozenset()


@dataclass(frozen=True)
class BlockControl:
    block: str
    successors: tuple[str, ...]
    edge_conditions: tuple[tuple[str, Term], ...] = ()


@dataclass(frozen=True)
class HavocRangeEvent:
    lhs: str
    lo: int
    hi: int
    source_cmds: tuple[AssignHavocCmd, AssumeExpCmd]

    @property
    def width(self) -> int:
        return len(self.source_cmds)


ScalarOrMap = Term | MapTerm


def lower_tac_file(
    tac: TacFile,
    *,
    vc: VCBuilder | None = None,
    options: TacLoweringOptions | None = None,
) -> tuple[VCBuilder, tuple[BlockControl, ...]]:
    return lower_tac_program(
        tac.program,
        tac.symbol_sorts,
        vc=vc,
        options=options,
    )


def lower_tac_program(
    program: TacProgram,
    symbol_sorts: dict[str, str],
    *,
    vc: VCBuilder | None = None,
    options: TacLoweringOptions | None = None,
) -> tuple[VCBuilder, tuple[BlockControl, ...]]:
    builder = vc or VCBuilder()
    executor = TacBlockExecutor(builder, symbol_sorts, options=options)
    opts = options or TacLoweringOptions()
    blocks = _ordered_blocks(program, opts.block_order)
    controls = tuple(executor.execute_block(block) for block in blocks)
    return builder, controls


class TacExprLowerer:
    def __init__(self, vc: VCBuilder, symbol_sorts: dict[str, str]) -> None:
        self.vc = vc
        self.symbol_sorts = symbol_sorts

    def lower(self, expr: TacExpr) -> ScalarOrMap:
        if isinstance(expr, SymbolRef):
            return self.symbol(expr.name)
        if isinstance(expr, ConstExpr):
            return self.const(expr.value)
        if isinstance(expr, ApplyExpr):
            return self.apply(expr)
        self.unsupported(expr, "expression")

    def lower_scalar(self, expr: TacExpr) -> Term:
        out = self.lower(expr)
        if isinstance(out, MapTerm):
            raise VCLoweringError(f"expected scalar expression, got bytemap {out.name}")
        return out

    def lower_bool(self, expr: TacExpr) -> Term:
        out = self.lower_scalar(expr)
        if out.sort is Bool:
            return out
        return eq(out, self.vc.int_lit(1))

    def symbol(self, name: str) -> ScalarOrMap:
        if self._is_map(name):
            return self.vc.bytemap.ref(name)
        return self.vc.const(name, self._sort(name))

    def const(self, raw: str) -> Term:
        if raw == "true":
            return true()
        if raw == "false":
            return false()
        return self.vc.int_lit(_parse_int(raw))

    def apply(self, expr: ApplyExpr) -> ScalarOrMap:
        op = expr.op
        args = expr.args
        if op == "Apply":
            return self.apply_builtin(args)
        if op == "Select":
            if len(args) != 2:
                self.unsupported(expr, "Select expects two args")
            map_term = self.lower_map(args[0])
            index = self.lower_scalar(args[1])
            return self.vc.bytemap.select(map_term, index)
        if op == "Store":
            self.unsupported(expr, "Store requires assignment context for map name")
        if op == "Ite":
            if len(args) != 3:
                self.unsupported(expr, "Ite expects three args")
            return app(
                "ite",
                [self.lower_bool(args[0]), self.lower_scalar(args[1]), self.lower_scalar(args[2])],
                Int,
            )
        if op in {"Eq", "Ne", "Lt", "Le", "Gt", "Ge"}:
            return self.compare(op, args)
        if op in {"LAnd", "LOr"}:
            items = [self.lower_bool(arg) for arg in args]
            return and_(*items) if op == "LAnd" else or_(*items)
        if op == "LNot":
            if len(args) != 1:
                self.unsupported(expr, "LNot expects one arg")
            return not_(self.lower_bool(args[0]))
        if len(args) != 2:
            self.unsupported(expr, f"{op} expects two args")
        a = self.lower_scalar(args[0])
        b = self.lower_scalar(args[1])
        if op == "Add":
            return self.vc.ops.bv256.add(a, b)
        if op == "Sub":
            return self.vc.ops.bv256.sub(a, b)
        if op == "Mul":
            return self.vc.ops.bv256.mul(a, b)
        if op == "Div":
            return self.vc.ops.bv256.div(a, b)
        if op == "Mod":
            return self.vc.ops.bv256.mod(a, b)
        if op == "IntAdd":
            return add(a, b)
        if op == "IntSub":
            return sub(a, b)
        if op == "IntMul":
            return mul(a, b)
        if op == "IntDiv":
            return div(a, b)
        if op == "IntMod":
            return mod(a, b)
        if op == "ShiftLeft":
            return self.vc.ops.bv256.shl(a, b)
        if op == "ShiftRightLogical":
            return self.vc.ops.bv256.lshr(a, b)
        if op == "BWAnd":
            return self.vc.ops.bv256.and_(a, b)
        if op == "BWXOr":
            return self.vc.ops.bv256.xor(a, b)
        if op == "BWOr":
            return self.vc.ops.bv256.or_(a, b)
        self.unsupported(expr, f"operator {op!r}")

    def compare(self, op: str, args: tuple[TacExpr, ...]) -> Term:
        if len(args) != 2:
            self.unsupported(ApplyExpr(op, args), f"{op} expects two args")
        a = self.lower_scalar(args[0])
        b = self.lower_scalar(args[1])
        if op == "Eq":
            return eq(a, b)
        if op == "Ne":
            return not_(eq(a, b))
        if op == "Lt":
            return lt(a, b)
        if op == "Le":
            return le(a, b)
        if op == "Gt":
            return gt(a, b)
        if op == "Ge":
            return ge(a, b)
        self.unsupported(ApplyExpr(op, args), f"comparison {op!r}")

    def apply_builtin(self, args: tuple[TacExpr, ...]) -> Term:
        if not args:
            raise VCLoweringError("Apply expects a function symbol")
        callee = args[0]
        if not isinstance(callee, SymbolRef):
            raise VCLoweringError("Apply callee must be a symbol")
        if callee.name == "safe_math_narrow_bv256:bif":
            if len(args) != 2:
                raise VCLoweringError("safe_math_narrow_bv256:bif expects one arg")
            return self.vc.ops.narrow.bv256(self.lower_scalar(args[1]))
        raise VCLoweringError(f"unsupported Apply callee {callee.name!r}")

    def lower_map(self, expr: TacExpr) -> MapTerm:
        out = self.lower(expr)
        if not isinstance(out, MapTerm):
            raise VCLoweringError(f"expected bytemap expression, got {out.smt()}")
        return out

    def _sort(self, name: str) -> Sort:
        raw = self.symbol_sorts.get(name)
        return Bool if raw == "bool" else Int

    def _is_map(self, name: str) -> bool:
        return self.symbol_sorts.get(name) in {"bytemap", "ghostmap"}

    def unsupported(self, expr: TacExpr, reason: str) -> NoReturn:
        raise VCLoweringError(f"unsupported TAC {reason}: {expr!r}")


class TacBlockExecutor:
    def __init__(
        self,
        vc: VCBuilder,
        symbol_sorts: dict[str, str],
        *,
        options: TacLoweringOptions | None = None,
    ) -> None:
        self.vc = vc
        self.symbol_sorts = symbol_sorts
        self.options = options or TacLoweringOptions()
        self.expr = TacExprLowerer(vc, symbol_sorts)

    def execute_block(self, block: TacBlock) -> BlockControl:
        guard = self.vc.const(f"BLK_{sanitize_name(block.id)}", Bool)
        edge_conditions = self._edge_conditions(block)
        with self.vc.block(block.id, guard=guard) as builder:
            i = 0
            while i < len(block.commands):
                if (block.id, i) in self.options.skip_command_points:
                    i += 1
                    continue
                event = self._classify_window(block.id, block.commands, i)
                if event is not None:
                    self._emit_havoc_range(event, builder)
                    i += event.width
                    continue
                cmd = block.commands[i]
                with self.vc.stmt(cmd.meta_index, cmd.raw):
                    self.execute_command(cmd, builder)
                i += 1
        return BlockControl(
            block=block.id,
            successors=tuple(block.successors),
            edge_conditions=edge_conditions,
        )

    def execute_command(self, cmd: TacCmd, builder: BlockBuilder) -> None:
        if isinstance(cmd, AssignExpCmd):
            self.assign(cmd, builder)
        elif isinstance(cmd, AssignHavocCmd):
            self.havoc(cmd)
        elif isinstance(cmd, AssumeExpCmd):
            builder.assume(self.expr.lower_bool(cmd.condition))
        elif isinstance(cmd, AssertCmd):
            builder.assert_(self.expr.lower_bool(cmd.predicate))
        elif isinstance(cmd, (JumpCmd, JumpiCmd, LabelCmd)):
            return
        elif isinstance(cmd, RawCmd):
            raise VCLoweringError(f"unsupported raw command {cmd.raw!r}")
        else:
            return

    def assign(self, cmd: AssignExpCmd, builder: BlockBuilder) -> None:
        lhs = cmd.lhs
        if self._is_map(lhs):
            self.assign_map(cmd)
            return
        rhs = self.expr.lower_scalar(cmd.rhs)
        builder.def_(self.vc.const(lhs, self._sort(lhs)), rhs, inline=self.options.inline_defs)

    def assign_map(self, cmd: AssignExpCmd) -> None:
        if not isinstance(cmd.rhs, ApplyExpr) or cmd.rhs.op != "Store" or len(cmd.rhs.args) != 3:
            raise VCLoweringError(f"bytemap assignment {cmd.lhs!r} requires Store RHS")
        base = self.expr.lower_map(cmd.rhs.args[0])
        index = self.expr.lower_scalar(cmd.rhs.args[1])
        value = self.expr.lower_scalar(cmd.rhs.args[2])
        self.vc.bytemap.store(cmd.lhs, base, index, value)

    def havoc(self, cmd: AssignHavocCmd) -> None:
        if self._is_map(cmd.lhs):
            self.vc.bytemap.havoc(cmd.lhs)
        else:
            self.vc.const(cmd.lhs, self._sort(cmd.lhs))

    def _classify_window(
        self, block_id: str, commands: list[TacCmd], index: int
    ) -> HavocRangeEvent | None:
        if index + 1 >= len(commands):
            return None
        first = commands[index]
        second = commands[index + 1]
        if not isinstance(first, AssignHavocCmd) or not isinstance(second, AssumeExpCmd):
            return None
        if (block_id, index + 1) in self.options.skip_command_points:
            return None
        if self._is_map(first.lhs):
            return None
        bounds = _range_bounds_for_symbol(second.condition, first.lhs)
        if bounds is None:
            return None
        lo, hi = bounds
        if lo > hi:
            raise VCLoweringError(f"invalid havoc range for {first.lhs}: {lo} > {hi}")
        return HavocRangeEvent(first.lhs, lo, hi, (first, second))

    def _emit_havoc_range(self, event: HavocRangeEvent, builder: BlockBuilder) -> None:
        lhs = self.vc.const(event.lhs, self._sort(event.lhs))
        raw = " ; ".join(cmd.raw for cmd in event.source_cmds)
        with self.vc.stmt(event.source_cmds[0].meta_index, raw):
            builder.range(lhs, lo=event.lo, hi=event.hi, name=self.vc.auto_name("havoc_range", lhs.text))

    def _edge_conditions(self, block: TacBlock) -> tuple[tuple[str, Term], ...]:
        if not block.commands:
            return ()
        last = block.commands[-1]
        if not isinstance(last, JumpiCmd):
            return ()
        cond = self.vc.const(last.condition, Bool)
        return ((last.then_target, cond), (last.else_target, not_(cond)))

    def _sort(self, name: str) -> Sort:
        raw = self.symbol_sorts.get(name)
        return Bool if raw == "bool" else Int

    def _is_map(self, name: str) -> bool:
        return self.symbol_sorts.get(name) in {"bytemap", "ghostmap"}


_TYPED_CONST = re.compile(r"^(?P<num>(?:-?[0-9]+|0[xX]-?[0-9a-fA-F_]+))\([A-Za-z0-9_]+\)$")


def _parse_int(raw: str) -> int:
    match = _TYPED_CONST.fullmatch(raw)
    if match:
        raw = match.group("num")
    if raw.lower().startswith("0x-"):
        raw = "-0x" + raw[3:]
    try:
        return int(raw, 0)
    except ValueError as e:
        raise VCLoweringError(f"unsupported constant {raw!r}") from e


def _ordered_blocks(program: TacProgram, order: str) -> list[TacBlock]:
    if order == "program":
        return list(program.blocks)
    if order == "topological":
        return Cfg(program).ordered_blocks()
    raise VCLoweringError(f"unknown TAC block order {order!r}")


def _range_bounds_for_symbol(expr: TacExpr, symbol: str) -> tuple[int, int] | None:
    constraints = _flatten_lands(expr)
    lo: int | None = None
    hi: int | None = None
    matched = False
    for constraint in constraints:
        bound = _one_sided_bound(constraint, symbol)
        if bound is None:
            return None
        kind, value = bound
        matched = True
        if kind == "lo":
            lo = value if lo is None else max(lo, value)
        else:
            hi = value if hi is None else min(hi, value)
    if not matched or lo is None or hi is None:
        return None
    return lo, hi


def _flatten_lands(expr: TacExpr) -> list[TacExpr]:
    if isinstance(expr, ApplyExpr) and expr.op == "LAnd":
        out: list[TacExpr] = []
        for arg in expr.args:
            out.extend(_flatten_lands(arg))
        return out
    return [expr]


def _one_sided_bound(expr: TacExpr, symbol: str) -> tuple[str, int] | None:
    if not isinstance(expr, ApplyExpr) or len(expr.args) != 2:
        return None
    left, right = expr.args
    if expr.op == "Le":
        if _is_symbol(left, symbol) and isinstance(right, ConstExpr):
            return ("hi", _parse_int(right.value))
        if isinstance(left, ConstExpr) and _is_symbol(right, symbol):
            return ("lo", _parse_int(left.value))
    if expr.op == "Ge":
        if _is_symbol(left, symbol) and isinstance(right, ConstExpr):
            return ("lo", _parse_int(right.value))
        if isinstance(left, ConstExpr) and _is_symbol(right, symbol):
            return ("hi", _parse_int(left.value))
    return None


def _is_symbol(expr: TacExpr, symbol: str) -> bool:
    return isinstance(expr, SymbolRef) and expr.name == symbol
