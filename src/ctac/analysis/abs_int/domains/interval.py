"""Interval analysis domain.

Forward sweep over a DSA, loop-free TAC program. Produces an interval
``[lo, hi]`` (with ``None`` denoting ±infinity) for every variable.

Storage: DSA-aware split (``analysis/abs_int/storage/dsa_split.py``).
DSA-static vars live in a shared ``static`` map written once at the
def site. DSA-dynamic vars and refinements from ``refine_assume``
live in a per-block ``local`` map. Lookup precedence at block B:
``local`` → ``static`` → sort-derived default → TOP.

The per-op math is shared with the rewriter's ``range_infer`` via
``analysis/abs_int/interval_ops.py``.
"""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass, field

from ctac.analysis.abs_int import interval_ops as iv
from ctac.analysis.abs_int.framework import Frontier, run
from ctac.analysis.abs_int.interval_ops import Interval
from ctac.analysis.abs_int.storage import DsaSplitState, DsaSplitStorage, Lattice
from ctac.analysis.passes import analyze_dsa
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
from ctac.ir.models import NBId, TacBlock, TacProgram
from ctac.rewrite.rules.common import const_to_int

State = DsaSplitState[Interval]

_BV_SORT_PREFIX = "bv"
_NARROW_WIDTHS = {
    "safe_math_narrow_bv64": 64,
    "safe_math_narrow_bv128": 128,
    "safe_math_narrow_bv256": 256,
}


def _sort_width(sort: str | None) -> int | None:
    if sort is None or not sort.startswith(_BV_SORT_PREFIX):
        return None
    rest = sort[len(_BV_SORT_PREFIX):]
    if not rest.isdigit():
        return None
    return int(rest)


def _narrow_width(fn_name: str) -> int | None:
    core = fn_name[:-4] if fn_name.endswith(":bif") else fn_name
    for prefix, width in _NARROW_WIDTHS.items():
        if core.startswith(prefix):
            return width
    return None


def _interval_lattice() -> Lattice[Interval]:
    return Lattice(top=iv.TOP, meet=iv.meet, join=iv.join)


def _bv_clamp(interval: Interval, width: int) -> Interval:
    """If ``interval`` fits in ``[0, 2^width - 1]`` (i.e. the
    un-wrapped result does not overflow bv``width``), return it
    unchanged — the bv result equals the un-wrapped interval.
    Otherwise return the full bv range, the smallest sound
    overapproximation across the wraparound."""
    bound = (1 << width) - 1
    if (
        interval.lo is not None
        and interval.lo >= 0
        and interval.hi is not None
        and interval.hi <= bound
    ):
        return interval
    return iv.bv_width_iv(width)


class IntervalDomain:
    """Plug into ``abs_int.run`` to compute per-variable intervals."""

    def __init__(
        self,
        program: TacProgram,
        *,
        symbol_sorts: Mapping[str, str] | None = None,
    ) -> None:
        self._program = program
        self._sorts: dict[str, str] = dict(symbol_sorts or {})
        dsa = analyze_dsa(program)
        self._storage: DsaSplitStorage[Interval] = DsaSplitStorage(
            dsa, _interval_lattice()
        )
        # Entry block: every refinement that arises during entry's
        # transfer is universally true (entry dominates every reachable
        # block). The refinement chain promotes such facts directly
        # into ``static`` instead of duplicating them into every
        # downstream block's ``local``.
        self._entry_id: str | None = (
            program.blocks[0].id if program.blocks else None
        )

    @property
    def storage(self) -> DsaSplitStorage[Interval]:
        return self._storage

    def init(self, entry: TacBlock) -> State:
        return self._storage.initial_state()

    # ----------------------------------------------------------------
    # Domain protocol

    def transfer(self, state: State, cmd: TacCmd, *, block: TacBlock) -> State:
        if isinstance(cmd, AssignHavocCmd):
            self._storage.write_def(state, cmd.lhs, self._default(cmd.lhs))
            return state
        if isinstance(cmd, AssignExpCmd):
            # The lhs sort gives the result's bv width, which the bv
            # op transfer functions need to detect wraparound.
            width = _sort_width(self._sorts.get(cmd.lhs))
            value = self._eval(cmd.rhs, state, result_width=width)
            self._storage.write_def(state, cmd.lhs, value)
            return state
        if isinstance(cmd, AssumeExpCmd):
            return self.refine_assume(state, cmd.condition, block=block)
        if isinstance(cmd, (AssertCmd, JumpCmd, JumpiCmd)):
            return state
        return state

    def propagate(
        self,
        state: State,
        *,
        src: TacBlock,
        dst: TacBlock,
        edge_cond: TacExpr | None,
    ) -> State:
        next_state = self._storage.propagate(state)
        if edge_cond is not None:
            return self.refine_assume(next_state, edge_cond, block=dst)
        return next_state

    def join(self, states: list[State], *, dst: TacBlock) -> State:
        return self._storage.join(states)

    def refine_assume(
        self, state: State, cond: TacExpr, *, block: TacBlock
    ) -> State:
        self._refine(state, cond, negate=False, block=block)
        return state

    # ----------------------------------------------------------------
    # Lookup with sort fallback

    def _default(self, var: str) -> Interval:
        width = _sort_width(self._sorts.get(var))
        if width is not None:
            return iv.bv_width_iv(width)
        return iv.TOP

    def _lookup(self, state: State, var: str) -> Interval:
        v = self._storage.get(state, var)
        if v.is_top():
            return self._default(var)
        return v

    def _infer_bv_width_from_operand_sorts(
        self, args: list[TacExpr]
    ) -> int | None:
        """Fallback width inference for raw bv ops without a
        surrounding ``result_width``: if every SymbolRef operand has
        a bv-N sort and they agree on N, return N. Otherwise return
        ``None`` (and the bv op falls back to TOP)."""
        widths: set[int] = set()
        for a in args:
            if isinstance(a, SymbolRef):
                w = _sort_width(self._sorts.get(a.name))
                if w is not None:
                    widths.add(w)
        if len(widths) == 1:
            return next(iter(widths))
        return None

    # ----------------------------------------------------------------
    # Expression evaluation
    #
    # ``result_width`` carries the bv width of the surrounding context
    # (set by ``transfer`` from the AssignExpCmd's lhs sort). It flows
    # *through* every op — int ops ignore it for their own arithmetic,
    # but a bv op nested inside an int op (e.g. ``IntMul(Mod(R, K), C)``
    # with a bv256 lhs) needs it to compute its modular result.
    #
    # The width context resets to ``None`` inside ``Apply(narrow_bvN, ...)``:
    # narrow's argument is int-typed, so anything underneath is in the
    # int domain. Bv ops without a width context fall back to inferring
    # one from operand sorts (all SymbolRef operands sharing bv-N →
    # use N); without either signal, bv ops return TOP.

    def _eval(
        self, expr: TacExpr, state: State, *, result_width: int | None = None
    ) -> Interval:
        if isinstance(expr, ConstExpr):
            c = const_to_int(expr)
            return iv.point(c) if c is not None else iv.TOP
        if isinstance(expr, SymbolRef):
            return self._lookup(state, expr.name)
        if isinstance(expr, ApplyExpr):
            return self._eval_apply(expr, state, result_width=result_width)
        return iv.TOP

    def _eval_apply(
        self, expr: ApplyExpr, state: State, *, result_width: int | None
    ) -> Interval:
        op = expr.op
        args = list(expr.args)

        # TAC `Apply(callee, ...)` wrapping. Inside a narrow_bvN call
        # the inner is int-typed, so width context resets to None.
        if op == "Apply" and args and isinstance(args[0], SymbolRef):
            width = _narrow_width(args[0].name)
            if width is not None and len(args) == 2:
                inner = self._eval(args[1], state, result_width=None)
                clamped = iv.narrow_clamp(inner, width)
                return clamped if clamped is not None else iv.TOP
            return iv.TOP

        # Int-domain (unbounded) arithmetic — interval math is sound
        # directly. ``result_width`` flows through to operands so a bv
        # op nested inside (e.g. ``Mod`` inside an ``IntMul`` whose
        # surrounding lhs is bv256) can compute its modular result.
        if op == "IntAdd" and len(args) == 2:
            return iv.add(
                self._eval(args[0], state, result_width=result_width),
                self._eval(args[1], state, result_width=result_width),
            )
        if op == "IntSub" and len(args) == 2:
            return iv.sub(
                self._eval(args[0], state, result_width=result_width),
                self._eval(args[1], state, result_width=result_width),
            )
        if op == "IntMul" and len(args) == 2:
            result = iv.mul_nonneg(
                self._eval(args[0], state, result_width=result_width),
                self._eval(args[1], state, result_width=result_width),
            )
            return result if result is not None else iv.TOP
        if op == "IntDiv" and len(args) == 2:
            k = const_to_int(args[1]) if isinstance(args[1], ConstExpr) else None
            if k is not None and k > 0:
                a = self._eval(args[0], state, result_width=result_width)
                result = iv.floor_div_by_pos_const(a, k)
                if result is not None:
                    return result
            return iv.TOP
        if op == "IntCeilDiv" and len(args) == 2:
            a = self._eval(args[0], state, result_width=result_width)
            b = self._eval(args[1], state, result_width=result_width)
            result = iv.ceil_div_nonneg(a, b)
            return result if result is not None else iv.TOP
        if op == "IntMod" and len(args) == 2:
            k = const_to_int(args[1]) if isinstance(args[1], ConstExpr) else None
            if k is not None and k > 0:
                a = self._eval(args[0], state, result_width=result_width)
                result = iv.mod_by_pos_const(a, k)
                if result is not None:
                    return result
            return iv.TOP

        # Raw bv ops — modular interval semantics. Width comes from
        # the surrounding context first, then from operand SymbolRef
        # sorts when they agree (e.g. ``Add(R_bv256, R_bv256)`` is
        # bv256-modular even when the assignment's lhs sort is
        # missing). Without either signal, return TOP.
        if op in {"Add", "Sub", "Mul", "Div", "Mod"} and len(args) == 2:
            width = result_width
            if width is None:
                width = self._infer_bv_width_from_operand_sorts(args)
            if width is None:
                return iv.TOP
            a = self._eval(args[0], state, result_width=width)
            b = self._eval(args[1], state, result_width=width)
            return self._eval_bv_binop(op, a, b, width)
        if op == "Ite" and len(args) == 3:
            # Branches are values of the same type as the Ite result —
            # carry the width context through so nested bv ops in the
            # arms get a width.
            return iv.join(
                self._eval(args[1], state, result_width=result_width),
                self._eval(args[2], state, result_width=result_width),
            )
        if op in _REL_OPS and len(args) == 2:
            return iv.bool_iv()
        if op in _BOOL_BIN_OPS and len(args) == 2:
            return iv.bool_iv()
        if op in _BOOL_UN_OPS and len(args) == 1:
            return iv.bool_iv()
        return iv.TOP

    # ----------------------------------------------------------------
    # Modular bv binop helpers

    def _eval_bv_binop(
        self, op: str, a: Interval, b: Interval, width: int
    ) -> Interval:
        """Modular bv binop on operand intervals ``a``, ``b`` at width
        ``width``. Strategy: compute the un-wrapped int-domain result;
        if it fits in ``[0, 2^width - 1]`` the bv op didn't wrap and
        the precise interval is sound; otherwise return the full bv
        range (overapproximation across the wrap)."""
        if op == "Add":
            return _bv_clamp(iv.add(a, b), width)
        if op == "Sub":
            # Result is non-negative (no wrap) iff a >= b. ``iv.sub``
            # alone gives the unwrapped interval; clamping checks the
            # non-negativity at the lower bound.
            return _bv_clamp(iv.sub(a, b), width)
        if op == "Mul":
            unwrapped = iv.mul_nonneg(a, b)
            if unwrapped is None:
                return iv.bv_width_iv(width)
            return _bv_clamp(unwrapped, width)
        if op == "Div":
            # Bv unsigned div by positive const: floor(a/k) <= a, so
            # never grows beyond the dividend's bv range. Symbolic /
            # zero divisors fall through to the bv range.
            k = None
            if b.lo is not None and b.lo == b.hi and b.lo > 0:
                k = b.lo
            if k is not None:
                result = iv.floor_div_by_pos_const(a, k)
                if result is not None:
                    return _bv_clamp(result, width)
            return iv.bv_width_iv(width)
        if op == "Mod":
            # Bv unsigned mod by positive const: result < k <= 2^width,
            # so the result always fits.
            k = None
            if b.lo is not None and b.lo == b.hi and b.lo > 0:
                k = b.lo
            if k is not None:
                result = iv.mod_by_pos_const(a, k)
                if result is not None:
                    return _bv_clamp(result, width)
            return iv.bv_width_iv(width)
        return iv.bv_width_iv(width)

    # ----------------------------------------------------------------
    # Refinement

    def _refine(
        self, state: State, cond: TacExpr, *, negate: bool, block: TacBlock
    ) -> None:
        if not isinstance(cond, ApplyExpr):
            return
        op = cond.op
        args = list(cond.args)

        if op == "LNot" and len(args) == 1:
            self._refine(state, args[0], negate=not negate, block=block)
            return
        # Conjunction under positive polarity refines both. Under
        # negation, ¬(P ∧ Q) = ¬P ∨ ¬Q — too weak to refine soundly,
        # so skip.
        if op == "LAnd" and len(args) == 2 and not negate:
            for sub in args:
                if isinstance(sub, TacExpr):
                    self._refine(state, sub, negate=False, block=block)
            return
        # ¬(P ∨ Q) = ¬P ∧ ¬Q.
        if op == "LOr" and len(args) == 2 and negate:
            for sub in args:
                if isinstance(sub, TacExpr):
                    self._refine(state, sub, negate=True, block=block)
            return

        # Comparison patterns: handle X op K and K op X for constant K.
        if op in _REL_OPS and len(args) == 2:
            self._refine_relation(state, op, args[0], args[1], negate=negate, block=block)

    def _refine_relation(
        self,
        state: State,
        op: str,
        lhs: TacExpr,
        rhs: TacExpr,
        *,
        negate: bool,
        block: TacBlock,
    ) -> None:
        # Effective op after negation.
        eff_op = _NEG_OP[op] if negate else op

        # Symbol-vs-constant.
        if isinstance(lhs, SymbolRef) and isinstance(rhs, ConstExpr):
            k = const_to_int(rhs)
            if k is not None:
                self._refine_var_const(state, lhs.name, eff_op, k, block=block)
            return
        if isinstance(lhs, ConstExpr) and isinstance(rhs, SymbolRef):
            k = const_to_int(lhs)
            if k is not None:
                self._refine_var_const(state, rhs.name, _SWAP_OP[eff_op], k, block=block)
            return

        # Symbol-vs-symbol equality refines both to the intersection.
        if eff_op == "Eq" and isinstance(lhs, SymbolRef) and isinstance(rhs, SymbolRef):
            inter = iv.meet(self._lookup(state, lhs.name), self._lookup(state, rhs.name))
            self._apply_refinement(state, lhs.name, inter, block=block)
            self._apply_refinement(state, rhs.name, inter, block=block)

    def _refine_var_const(
        self, state: State, var: str, eff_op: str, k: int, *, block: TacBlock
    ) -> None:
        if eff_op == "Eq":
            self._apply_refinement(state, var, iv.point(k), block=block)
        elif eff_op == "Ne":
            # No tightening — a single excluded value doesn't shrink the box.
            return
        elif eff_op == "Le" or eff_op == "Sle":
            self._apply_refinement(state, var, Interval(None, k), block=block)
        elif eff_op == "Lt" or eff_op == "Slt":
            self._apply_refinement(state, var, Interval(None, k - 1), block=block)
        elif eff_op == "Ge" or eff_op == "Sge":
            self._apply_refinement(state, var, Interval(k, None), block=block)
        elif eff_op == "Gt" or eff_op == "Sgt":
            self._apply_refinement(state, var, Interval(k + 1, None), block=block)

    def _apply_refinement(
        self, state: State, var: str, refinement: Interval, *, block: TacBlock
    ) -> None:
        """Route a refinement: entry-block + DSA-static var → ``static``
        (universal); else → ``local`` (block-scoped). DSA-dynamic vars
        always go to ``local``: their value is per-block by definition,
        and a refinement on a dynamic var doesn't promote across blocks.
        """
        if (
            block.id == self._entry_id
            and not self._storage.is_dsa_dynamic(var)
        ):
            self._storage.refine_static(state, var, refinement)
            return
        self._storage.refine(state, var, refinement)


_REL_OPS = frozenset(
    {"Eq", "Ne", "Lt", "Le", "Gt", "Ge", "Slt", "Sle", "Sgt", "Sge"}
)
_BOOL_BIN_OPS = frozenset({"LAnd", "LOr"})
_BOOL_UN_OPS = frozenset({"LNot"})

# Negation table for relational ops.
_NEG_OP = {
    "Eq": "Ne",
    "Ne": "Eq",
    "Lt": "Ge",
    "Le": "Gt",
    "Gt": "Le",
    "Ge": "Lt",
    "Slt": "Sge",
    "Sle": "Sgt",
    "Sgt": "Sle",
    "Sge": "Slt",
}

# Swap table for relational ops (swap lhs/rhs).
_SWAP_OP = {
    "Eq": "Eq",
    "Ne": "Ne",
    "Lt": "Gt",
    "Le": "Ge",
    "Gt": "Lt",
    "Ge": "Le",
    "Slt": "Sgt",
    "Sle": "Sge",
    "Sgt": "Slt",
    "Sge": "Sle",
}


# --------------------------------------------------------------------
# Top-level analyze function + result types

@dataclass(frozen=True)
class ExprInterval:
    """One ``AssignExpCmd``'s rhs interval evaluated in its block's
    pre-transfer state."""

    block_id: str
    cmd_index: int
    lhs: str
    raw: str
    interval: Interval


@dataclass(frozen=True)
class IntervalResult:
    static: dict[str, Interval]
    per_block_local: dict[NBId, dict[str, Interval]] = field(default_factory=dict)
    expression_intervals: list[ExprInterval] = field(default_factory=list)


def analyze_intervals(
    program: TacProgram,
    *,
    symbol_sorts: Mapping[str, str] | None = None,
) -> IntervalResult:
    domain = IntervalDomain(program, symbol_sorts=symbol_sorts)
    frontier: Frontier = run(program, domain)

    static: dict[str, Interval] = dict(domain.storage.initial_state().static)
    # `static` is shared across all states; pulling it from any frontier
    # entry would also work, but the storage's reference is canonical.
    if frontier:
        # Replace with the actually-mutated dict from any state (they
        # all point to the same object).
        any_state = next(iter(frontier.values()))
        static = dict(any_state.static)

    per_block_local: dict[NBId, dict[str, Interval]] = {
        bid: dict(state.local) for bid, state in frontier.items()
    }

    expression_intervals = _collect_expression_intervals(program, domain, frontier)

    return IntervalResult(
        static=static,
        per_block_local=per_block_local,
        expression_intervals=expression_intervals,
    )


def _collect_expression_intervals(
    program: TacProgram,
    domain: IntervalDomain,
    frontier: Frontier,
) -> list[ExprInterval]:
    """Re-evaluate every ``AssignExpCmd`` against the *exit* state of
    its block. The framework's frontier returns each block's
    post-transfer state, which is exactly the right context to resolve
    constituent operands' final intervals."""
    out: list[ExprInterval] = []
    for block in program.blocks:
        state = frontier.get(block.id)
        if state is None:
            continue
        for idx, cmd in enumerate(block.commands):
            if isinstance(cmd, AssignExpCmd):
                value = domain._eval(cmd.rhs, state)
                out.append(
                    ExprInterval(
                        block_id=block.id,
                        cmd_index=idx,
                        lhs=cmd.lhs,
                        raw=cmd.raw,
                        interval=value,
                    )
                )
    return out
