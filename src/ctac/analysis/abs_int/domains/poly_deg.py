"""Polynomial-degree domain.

Estimates the polynomial degree of TAC variables. `deg(const) = 0`,
`deg(symbol) = 1`, `deg(a * b) = deg(a) + deg(b)`, division and bitwise
ops add 1 (treated as non-linear), comparisons and boolean ops take
the max of operand degrees.

Storage strategy 1 (global): all frontier entries share a single
`dict[var, AbsVal]`. The per-block key is ignored — degree is path-
monotone, so the global map's lattice join handles dynamic-var merges
naturally.
"""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass, field

from ctac.analysis.abs_int.framework import Frontier, run
from ctac.ast.nodes import (
    ApplyExpr,
    AssertCmd,
    AssignExpCmd,
    AssignHavocCmd,
    AssumeExpCmd,
    ConstExpr,
    JumpCmd,
    JumpiCmd,
    SymbolRef,
    TacCmd,
    TacExpr,
)
from ctac.ir.models import TacBlock, TacProgram


# Lattice element: an integer degree, BOT (unreachable / no def yet),
# or TOP (degree-unknown / unrecognized op).
class _Sentinel:
    __slots__ = ("name",)

    def __init__(self, name: str) -> None:
        self.name = name

    def __repr__(self) -> str:
        return self.name


BOT = _Sentinel("BOT")
TOP = _Sentinel("TOP")

AbsVal = int | _Sentinel  # int >= 0, BOT, or TOP


def join_val(a: AbsVal, b: AbsVal) -> AbsVal:
    if a is BOT:
        return b
    if b is BOT:
        return a
    if a is TOP or b is TOP:
        return TOP
    assert isinstance(a, int) and isinstance(b, int)
    return max(a, b)


def add_deg(a: AbsVal, b: AbsVal) -> AbsVal:
    if a is BOT or b is BOT:
        return BOT
    if a is TOP or b is TOP:
        return TOP
    assert isinstance(a, int) and isinstance(b, int)
    return a + b


def bump(a: AbsVal) -> AbsVal:
    if a is BOT:
        return BOT
    if a is TOP:
        return TOP
    assert isinstance(a, int)
    return a + 1


_LINEAR_OPS = frozenset({"Add", "IntAdd", "Sub", "IntSub"})
_MUL_OPS = frozenset({"Mul", "IntMul"})
_DIV_OPS = frozenset({"Div", "IntDiv", "Mod", "IntMod", "IntCeilDiv", "SDiv", "SMod"})
_BITWISE_BIN_OPS = frozenset({"BWAnd", "BWOr", "BWXor"})
_SHIFT_OPS = frozenset(
    {"ShiftLeft", "ShiftRightLogical", "ShiftRightArithmetical"}
)
_BITWISE_UN_OPS = frozenset({"BWNot"})
_REL_OPS = frozenset(
    {
        "Eq",
        "Ne",
        "Lt",
        "Le",
        "Gt",
        "Ge",
        "Slt",
        "Sle",
        "Sgt",
        "Sge",
    }
)
_BOOL_BIN_OPS = frozenset({"LAnd", "LOr"})
_BOOL_UN_OPS = frozenset({"LNot"})


def _is_safe_math_narrow(op: str) -> bool:
    # `safe_math_narrow_bv256:bif`, `safe_math_narrow_bv64:bif`, etc.
    return op.startswith("safe_math_narrow_bv") and op.endswith(":bif")


def evaluate_degree(expr: TacExpr, vals: Mapping[str, AbsVal]) -> AbsVal:
    """Compute the polynomial degree of an expression given a var→AbsVal map.

    Symbols not present in `vals` default to degree 1 (a fresh
    indeterminate, same as a plain havoc).
    """
    if isinstance(expr, ConstExpr):
        return 0
    if isinstance(expr, SymbolRef):
        return vals.get(expr.name, 1)
    if isinstance(expr, ApplyExpr):
        return _eval_apply(expr, vals)
    return TOP


def _is_constant_degree(v: AbsVal) -> bool:
    """Proxy for 'this operand is a literal constant'.

    A ConstExpr has degree 0; combinations of constants (Add of two
    consts, Mul of two consts, etc.) also yield degree 0 via the lattice
    rules. Symbolic refs are degree >= 1, so degree-0 == const-valued is
    a sound proxy in this analysis.
    """
    return isinstance(v, int) and v == 0


def _eval_apply(expr: ApplyExpr, vals: Mapping[str, AbsVal]) -> AbsVal:
    op = expr.op
    arg_exprs = list(expr.args)

    # TAC `Apply(callee, a1, a2, ...)` is parsed with op == "Apply" and
    # the callee held in args[0] (a SymbolRef). Unwrap so the operator
    # table sees the real function name.
    if op == "Apply" and arg_exprs and isinstance(arg_exprs[0], SymbolRef):
        op = arg_exprs[0].name
        arg_exprs = arg_exprs[1:]

    args = [evaluate_degree(a, vals) for a in arg_exprs]

    if _is_safe_math_narrow(op) and len(args) == 1:
        return args[0]

    if op == "Select":
        return 1

    if op in _LINEAR_OPS and len(args) == 2:
        return join_val(args[0], args[1])

    if op in _MUL_OPS and len(args) == 2:
        # Mul is degree-additive; deg(c) = 0 already gives the
        # mul-by-constant linear case for free (deg(x) + 0 = deg(x)).
        return add_deg(args[0], args[1])

    if op in _DIV_OPS and len(args) == 2:
        # Div / Mod / IntCeilDiv by a constant divisor is linear scaling
        # (same degree as the numerator) — `x / c = (1/c) * x`. Only a
        # symbolic divisor introduces 1/x and bumps the degree.
        if _is_constant_degree(args[1]):
            return args[0]
        return bump(join_val(args[0], args[1]))

    if op in _BITWISE_BIN_OPS and len(args) == 2:
        # Bitwise op against a constant mask is linear in the other
        # operand; only symbolic-on-both-sides genuinely introduces
        # bit-level nonlinearity.
        if _is_constant_degree(args[0]) or _is_constant_degree(args[1]):
            return join_val(args[0], args[1])
        return bump(join_val(args[0], args[1]))

    if op in _BITWISE_UN_OPS and len(args) == 1:
        # BWNot is bit-complement: ~x = -x - 1 in two's complement,
        # linear in x.
        return args[0]

    if op in _SHIFT_OPS and len(args) == 2:
        # Shift by a constant amount is multiplication / division by a
        # power of two — linear. A variable shift count is genuinely
        # nonlinear.
        if _is_constant_degree(args[1]):
            return args[0]
        return bump(join_val(args[0], args[1]))

    if op in _REL_OPS and len(args) == 2:
        return join_val(args[0], args[1])

    if op in _BOOL_BIN_OPS and len(args) == 2:
        return join_val(args[0], args[1])

    if op in _BOOL_UN_OPS and len(args) == 1:
        return args[0]

    if op == "Ite" and len(args) == 3:
        return join_val(args[1], args[2])

    return TOP


@dataclass
class _State:
    """Wrapper around the shared global var → AbsVal map.

    Every frontier entry holds the *same* `_State` instance: storage
    strategy 1 ignores per-block keys. Mutations are visible across the
    frontier, which is correct because degree is path-monotone — the
    join is just `max`, and a later-visited block can only raise a
    degree, never lower it.
    """

    vals: dict[str, AbsVal] = field(default_factory=dict)
    saw_top: bool = False

    def get(self, name: str) -> AbsVal:
        return self.vals.get(name, 1)

    def update(self, name: str, val: AbsVal) -> None:
        prev = self.vals.get(name, BOT)
        new = join_val(prev, val)
        self.vals[name] = new
        if new is TOP:
            self.saw_top = True


class PolynomialDegreeDomain:
    """Estimate polynomial degree per variable across a DSA program."""

    def init(self, entry: TacBlock) -> _State:
        return _State()

    def transfer(self, state: _State, cmd: TacCmd, *, block: TacBlock) -> _State:
        if isinstance(cmd, AssignExpCmd):
            val = evaluate_degree(cmd.rhs, state.vals)
            state.update(cmd.lhs, val)
            return state
        if isinstance(cmd, AssignHavocCmd):
            state.update(cmd.lhs, 1)
            return state
        if isinstance(cmd, (AssumeExpCmd, AssertCmd, JumpCmd, JumpiCmd)):
            return state
        return state

    def propagate(
        self,
        state: _State,
        *,
        src: TacBlock,
        dst: TacBlock,
        edge_cond: TacExpr | None,
    ) -> _State:
        return state

    def join(self, states: list[_State], *, dst: TacBlock) -> _State:
        if not states:
            return _State()
        return states[0]

    def refine_assume(
        self, state: _State, cond: TacExpr, *, block: TacBlock
    ) -> _State:
        return state


def _format_val(v: AbsVal) -> int | str:
    if v is TOP:
        return "TOP"
    if v is BOT:
        return "BOT"
    assert isinstance(v, int)
    return v


@dataclass(frozen=True)
class ExprDegree:
    """One AssignExpCmd's degree as evaluated from the final state.

    `degree` is an int (>= 0) or the string "TOP" when the RHS contains
    an unrecognized operator.
    """

    block_id: str
    cmd_index: int
    lhs: str
    raw: str
    degree: int | str


@dataclass(frozen=True)
class PolyDegResult:
    final_state: dict[str, int | str]
    program_max_degree: int
    saw_top: bool
    top_symbols: list[str]
    expression_degrees: list[ExprDegree]


def _expression_degrees(
    program: TacProgram, vals: Mapping[str, AbsVal]
) -> list[ExprDegree]:
    out: list[ExprDegree] = []
    for block in program.blocks:
        for idx, cmd in enumerate(block.commands):
            if isinstance(cmd, AssignExpCmd):
                deg = evaluate_degree(cmd.rhs, vals)
                out.append(
                    ExprDegree(
                        block_id=block.id,
                        cmd_index=idx,
                        lhs=cmd.lhs,
                        raw=cmd.raw,
                        degree=_format_val(deg),
                    )
                )
    return out


def analyze_polynomial_degree(program: TacProgram) -> PolyDegResult:
    domain = PolynomialDegreeDomain()
    frontier: Frontier = run(program, domain)

    state: _State | None = None
    for s in frontier.values():
        state = s
        break
    if state is None:
        state = _State()

    final: dict[str, int | str] = {k: _format_val(v) for k, v in state.vals.items()}
    int_degrees = [v for v in state.vals.values() if isinstance(v, int)]
    program_max = max(int_degrees) if int_degrees else 0
    top_symbols = sorted(k for k, v in state.vals.items() if v is TOP)
    expr_degrees = _expression_degrees(program, state.vals)
    return PolyDegResult(
        final_state=final,
        program_max_degree=program_max,
        saw_top=state.saw_top,
        top_symbols=top_symbols,
        expression_degrees=expr_degrees,
    )
