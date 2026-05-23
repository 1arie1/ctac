from __future__ import annotations

from dataclasses import dataclass
import re
from typing import NoReturn

from ctac.analysis.symbols import canonical_symbol
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
from ctac.smt.vc.builder import BlockBuilder, IntRange, VCBuilder, sanitize_name
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
    ite,
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
    executor = TacBlockExecutor(builder, _canonical_symbol_sorts(symbol_sorts), options=options)
    opts = options or TacLoweringOptions()
    blocks = _ordered_blocks(program, opts.block_order)
    controls = tuple(executor.execute_block(block) for block in blocks)
    return builder, controls


class TacExprLowerer:
    def __init__(
        self,
        vc: VCBuilder,
        symbol_sorts: dict[str, str],
        *,
        symbol_aliases: dict[str, Term] | None = None,
    ) -> None:
        self.vc = vc
        self.symbol_sorts = _canonical_symbol_sorts(symbol_sorts)
        self.symbol_aliases = {
            _canon(name): term for name, term in (symbol_aliases or {}).items()
        }

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
        self.require_sort(out, Bool, expr)
        return out

    def lower_int(self, expr: TacExpr) -> Term:
        out = self.lower_scalar(expr)
        self.require_sort(out, Int, expr)
        return out

    def require_sort(self, term: Term, expected: Sort, source: TacExpr | str) -> None:
        if term.sort is expected:
            return
        raise VCLoweringError(
            f"expected {expected.smt()} expression, got {term.sort.smt()}: {source!r}"
        )

    def require_same_sort(self, left: Term, right: Term, source: TacExpr | str) -> None:
        if left.sort is right.sort:
            return
        raise VCLoweringError(
            f"sort mismatch: {left.sort.smt()} vs {right.sort.smt()}: {source!r}"
        )

    def require_assignment_sort(self, lhs: Term, rhs: Term, source: TacExpr | str) -> None:
        if lhs.sort is rhs.sort:
            return
        raise VCLoweringError(
            f"assignment sort mismatch for {lhs.text}: expected {lhs.sort.smt()}, "
            f"got {rhs.sort.smt()}: {source!r}"
        )

    def require_int_term(self, term: Term, source: TacExpr | str) -> None:
        if term.sort is Int:
            return
        raise VCLoweringError(f"expected Int expression, got {term.sort.smt()}: {source!r}")

    def symbol(self, name: str) -> ScalarOrMap:
        name = _canon(name)
        if name in self.symbol_aliases:
            return self.symbol_aliases[name]
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
            index = self.lower_int(args[1])
            return self.vc.bytemap.select(map_term, index)
        if op == "Store":
            self.unsupported(expr, "Store requires assignment context for map name")
        if op == "Ite":
            if len(args) != 3:
                self.unsupported(expr, "Ite expects three args")
            cond = self.lower_bool(args[0])
            then_term = self.lower_scalar(args[1])
            else_term = self.lower_scalar(args[2])
            self.require_same_sort(then_term, else_term, expr)
            return ite(cond, then_term, else_term, then_term.sort)
        if op in {"Eq", "Ne", "Lt", "Le", "Gt", "Ge", "Slt", "Sle", "Sgt", "Sge"}:
            return self.compare(op, args)
        if op in {"LAnd", "LOr"}:
            items = [self.lower_bool(arg) for arg in args]
            return and_(*items) if op == "LAnd" else or_(*items)
        if op == "LNot":
            if len(args) != 1:
                self.unsupported(expr, "LNot expects one arg")
            return not_(self.lower_bool(args[0]))
        if op == "IntMulDiv":
            if len(args) != 3:
                self.unsupported(expr, "IntMulDiv expects three args")
            a = self.lower_int(args[0])
            b = self.lower_int(args[1])
            c = self.lower_int(args[2])
            return self.vc.ops.int_mul_div(a, b, c)
        if op == "IntCeilDiv":
            if len(args) != 2:
                self.unsupported(expr, "IntCeilDiv expects two args")
            a = self.lower_int(args[0])
            b = self.lower_int(args[1])
            return self.vc.ops.int_ceil_div(a, b)
        if len(args) != 2:
            self.unsupported(expr, f"{op} expects two args")
        a = self.lower_int(args[0])
        b = self.lower_int(args[1])
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
            self.require_same_sort(a, b, ApplyExpr(op, args))
            return eq(a, b)
        if op == "Ne":
            self.require_same_sort(a, b, ApplyExpr(op, args))
            return not_(eq(a, b))
        self.require_int_term(a, ApplyExpr(op, args))
        self.require_int_term(b, ApplyExpr(op, args))
        if op == "Lt":
            return lt(a, b)
        if op == "Le":
            return le(a, b)
        if op == "Gt":
            return gt(a, b)
        if op == "Ge":
            return ge(a, b)
        # Signed comparisons interpret both operands as bv256 two's-
        # complement values. ``Sgt(a, b) == Slt(b, a)`` and
        # ``Sge(a, b) == Sle(b, a)`` — implement via arg-swap to share
        # the slt/sle define-fun bodies.
        if op == "Slt":
            return self.vc.ops.bv256.slt(a, b)
        if op == "Sle":
            return self.vc.ops.bv256.sle(a, b)
        if op == "Sgt":
            return self.vc.ops.bv256.slt(b, a)
        if op == "Sge":
            return self.vc.ops.bv256.sle(b, a)
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
            return self.vc.ops.narrow.bv256(self.lower_int(args[1]))
        if callee.name == "wrap_twos_complement_256:bif":
            if len(args) != 2:
                raise VCLoweringError("wrap_twos_complement_256:bif expects one arg")
            return self.vc.ops.bv256.wrap_twos_complement(self.lower_int(args[1]))
        if callee.name == "unwrap_twos_complement_256:bif":
            if len(args) != 2:
                raise VCLoweringError("unwrap_twos_complement_256:bif expects one arg")
            return self.vc.ops.bv256.unwrap_twos_complement(self.lower_int(args[1]))
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
        self.symbol_sorts = _canonical_symbol_sorts(symbol_sorts)
        self.expr = TacExprLowerer(vc, self.symbol_sorts)

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
                    self._emit_havoc_range(event, builder, i)
                    i += event.width
                    continue
                cmd = block.commands[i]
                with self.vc.stmt(_stmt_id(cmd, i), cmd.raw):
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
            self.havoc(cmd, builder)
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
        lhs = _canon(cmd.lhs)
        if self._is_map(lhs):
            self.assign_map(cmd)
            return
        rhs = self.expr.lower_scalar(cmd.rhs)
        lhs_term = self.vc.const(lhs, self._sort(lhs))
        self.expr.require_assignment_sort(lhs_term, rhs, cmd.rhs)
        builder.def_(lhs_term, rhs, inline=self.options.inline_defs)

    def assign_map(self, cmd: AssignExpCmd) -> None:
        lhs = _canon(cmd.lhs)
        self.vc.bytemap.define(lhs, lambda idx: _lower_map_body(self.expr, cmd.rhs, idx, lhs))

    def havoc(self, cmd: AssignHavocCmd, builder: BlockBuilder) -> None:
        lhs = _canon(cmd.lhs)
        if self._is_map(lhs):
            self.vc.bytemap.havoc(lhs)
        else:
            lhs_term = self.vc.const(lhs, self._sort(lhs))
            if lhs_term.sort is Int:
                builder.range(lhs_term, IntRange.bv256(), name=self.vc.auto_name("havoc_range", lhs))

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
        lhs = _canon(first.lhs)
        if self._is_map(lhs):
            return None
        lo, hi = _range_refinement_for_symbol(second.condition, lhs)
        if lo is None and hi is None:
            return None
        lo = max(0, lo) if lo is not None else 0
        hi = min(_BV256_MAX, hi) if hi is not None else _BV256_MAX
        if lo > hi:
            raise VCLoweringError(f"invalid havoc range for {first.lhs}: {lo} > {hi}")
        return HavocRangeEvent(lhs, lo, hi, (first, second))

    def _emit_havoc_range(
        self, event: HavocRangeEvent, builder: BlockBuilder, cmd_index: int
    ) -> None:
        lhs = self.vc.const(event.lhs, self._sort(event.lhs))
        self.expr.require_sort(lhs, Int, event.lhs)
        raw = " ; ".join(cmd.raw for cmd in event.source_cmds)
        with self.vc.stmt(_stmt_id(event.source_cmds[0], cmd_index), raw):
            builder.range(lhs, lo=event.lo, hi=event.hi, name=self.vc.auto_name("havoc_range", lhs.text))

    def _edge_conditions(self, block: TacBlock) -> tuple[tuple[str, Term], ...]:
        if not block.commands:
            return ()
        last = block.commands[-1]
        if not isinstance(last, JumpiCmd):
            return ()
        cond = self.vc.const(_canon(last.condition), Bool)
        return ((last.then_target, cond), (last.else_target, not_(cond)))

    def _sort(self, name: str) -> Sort:
        raw = self.symbol_sorts.get(name)
        return Bool if raw == "bool" else Int

    def _is_map(self, name: str) -> bool:
        return self.symbol_sorts.get(name) in {"bytemap", "ghostmap"}


_TYPED_CONST = re.compile(r"^(?P<num>(?:-?[0-9]+|0[xX]-?[0-9a-fA-F_]+))\([A-Za-z0-9_]+\)$")
_BV256_MAX = (1 << 256) - 1


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


def _canon(symbol: str) -> str:
    return canonical_symbol(symbol, strip_var_suffixes=True)


def _canonical_symbol_sorts(symbol_sorts: dict[str, str]) -> dict[str, str]:
    return {_canon(name): sort for name, sort in symbol_sorts.items()}


def _unsupported_bytemap_assignment_message(lhs: str, rhs: TacExpr) -> str:
    shape = _bytemap_rhs_shape(rhs)
    rhs_text = _brief_expr(rhs)
    message = (
        f"unsupported bytemap assignment {_canon(lhs)!r}: expected RHS "
        f"Store(base_map, index, value) or Ite(cond, then_map, else_map), "
        f"but got {shape} RHS {rhs_text}. "
        "The sea encoder currently supports bytemap havoc, Store updates, "
        "and map-valued Ite/phi merges."
    )
    return message


def _bytemap_rhs_shape(rhs: TacExpr) -> str:
    if isinstance(rhs, ApplyExpr):
        if rhs.op == "Ite":
            return "map-valued Ite/phi merge"
        if rhs.op == "Store":
            return f"Store with {len(rhs.args)} argument(s)"
        return f"{rhs.op} application"
    if isinstance(rhs, SymbolRef):
        return "bytemap alias"
    if isinstance(rhs, ConstExpr):
        return "constant"
    return type(rhs).__name__


def _brief_expr(expr: TacExpr, *, max_len: int = 220) -> str:
    text = _format_expr(expr)
    if len(text) <= max_len:
        return text
    return text[: max_len - 3] + "..."


def _format_expr(expr: TacExpr) -> str:
    if isinstance(expr, SymbolRef):
        return _canon(expr.name)
    if isinstance(expr, ConstExpr):
        return expr.value
    if isinstance(expr, ApplyExpr):
        args = ", ".join(_format_expr(arg) for arg in expr.args)
        return f"{expr.op}({args})"
    return repr(expr)


def _lower_map_body(expr: TacExprLowerer, source: TacExpr, idx: Term, lhs: str) -> Term:
    if isinstance(source, SymbolRef):
        map_term = expr.lower_map(source)
        return app(map_term.name, [idx], Int)
    if isinstance(source, ApplyExpr) and source.op == "Store" and len(source.args) == 3:
        base, key, value = source.args
        return app(
            "ite",
            [
                eq(idx, expr.lower_int(key)),
                expr.lower_int(value),
                _lower_map_body(expr, base, idx, lhs),
            ],
            Int,
        )
    if isinstance(source, ApplyExpr) and source.op == "Ite" and len(source.args) == 3:
        cond, then_map, else_map = source.args
        return app(
            "ite",
            [
                expr.lower_bool(cond),
                _lower_map_body(expr, then_map, idx, lhs),
                _lower_map_body(expr, else_map, idx, lhs),
            ],
            Int,
        )
    raise VCLoweringError(_unsupported_bytemap_assignment_message(lhs, source))


def _ordered_blocks(program: TacProgram, order: str) -> list[TacBlock]:
    if order == "program":
        return list(program.blocks)
    if order == "topological":
        return Cfg(program).ordered_blocks()
    raise VCLoweringError(f"unknown TAC block order {order!r}")


def _range_bounds_for_symbol(expr: TacExpr, symbol: str) -> tuple[int, int] | None:
    lo, hi = _range_refinement_for_symbol(expr, symbol)
    if lo is None or hi is None:
        return None
    return lo, hi


def _range_refinement_for_symbol(expr: TacExpr, symbol: str) -> tuple[int | None, int | None]:
    symbol = _canon(symbol)
    constraints = _flatten_lands(expr)
    lo: int | None = None
    hi: int | None = None
    matched = False
    for constraint in constraints:
        bound = _one_sided_bound(constraint, symbol)
        if bound is None:
            return None, None
        kind, value = bound
        matched = True
        if kind == "lo":
            lo = value if lo is None else max(lo, value)
        else:
            hi = value if hi is None else min(hi, value)
    if not matched:
        return None, None
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
    return isinstance(expr, SymbolRef) and _canon(expr.name) == _canon(symbol)


def _stmt_id(cmd: TacCmd, index: int) -> str | int:
    return cmd.meta_index if cmd.meta_index is not None else index
