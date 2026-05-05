"""Interval analysis domain.

Forward sweep over a DSA, loop-free TAC program. Produces an interval
``[lo, hi]`` (with ``None`` denoting ±infinity) for every variable.

Storage: DSA-aware split (``analysis/abs_int/storage/dsa_split.py``).
DSA-static vars live in a shared ``static`` map written once at the
def site. DSA-dynamic vars and refinements from ``refine_assume``
live in a per-block ``local`` map. Lookup precedence at block B:
``local`` → ``static`` → sort-derived default → TOP.

The per-op transfer functions are shared with the rewriter's
``range_infer`` via ``analysis/abs_int/expr_eval.py``.
"""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass, field

from ctac.analysis.abs_int import interval_ops as iv
from ctac.analysis.abs_int.expr_eval import _sort_width, eval_expr_iv
from ctac.analysis.abs_int.framework import Frontier, run
from ctac.analysis.abs_int.interval_ops import Interval
from ctac.analysis.abs_int.storage import DsaSplitState, DsaSplitStorage, Lattice
from ctac.analysis.passes import analyze_dsa
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
    SymbolRef,
    TacCmd,
    TacExpr,
)
from ctac.ir.models import NBId, TacBlock, TacProgram
from ctac.rewrite.rules.common import const_to_int

State = DsaSplitState[Interval]


def _interval_lattice() -> Lattice[Interval]:
    return Lattice(top=iv.TOP, meet=iv.meet, join=iv.join)


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
            width = _sort_width(self._sort_for(cmd.lhs))
            # Evaluate using the normal lookup (local + static + sort
            # default). Operand refinements within the same block are
            # sequentially valid at the def site under program
            # semantics — and program semantics are what the
            # materialization+rw-eq pipeline checks. The materializer
            # is responsible for only emitting the resulting facts at
            # blocks dominated by the def, which is where dominance
            # transitively guarantees the operand refinements fired.
            value = self._eval(cmd.rhs, state, result_width=width)
            # The lhs sort's default is a sound upper bound on the
            # value regardless of how the rhs evaluated — for any
            # bv-typed lhs, the actual runtime value is in
            # ``[0, 2^width - 1]``. Meet ensures an unhandled or
            # imprecise transfer function (e.g. shifts, bitwise
            # binops returning TOP) still yields the sort default
            # rather than collapsing to TOP.
            value = iv.meet(value, self._default(cmd.lhs))
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
        sort = self._sort_for(var)
        if sort == "bool":
            return iv.bool_iv()
        width = _sort_width(sort)
        if width is not None:
            return iv.bv_width_iv(width)
        return iv.TOP

    def _sort_for(self, var: str) -> str | None:
        """TAC parallel-assignment sites mint per-instance suffixed
        names like ``B1487:0`` that aren't keys in the symbol table —
        only the canonical ``B1487`` is. Strip suffixes before lookup
        so the suffixed instances inherit the canonical sort."""
        s = self._sorts.get(var)
        if s is not None:
            return s
        canon = canonical_symbol(var)
        if canon != var:
            return self._sorts.get(canon)
        return None

    def _lookup(self, state: State, var: str) -> Interval:
        v = self._storage.get(state, var)
        if v.is_top():
            return self._default(var)
        return v

    # ----------------------------------------------------------------
    # Expression evaluation
    #
    # Thin wrapper over the shared ``eval_expr_iv`` (per-op transfer
    # functions live in ``analysis/abs_int/expr_eval.py``).
    # ``result_width`` carries the bv width of the surrounding context
    # (set by ``transfer`` from the AssignExpCmd's lhs sort) and flows
    # through int ops down to nested bv ops.

    def _eval(
        self,
        expr: TacExpr,
        state: State,
        *,
        result_width: int | None = None,
    ) -> Interval:
        return eval_expr_iv(
            expr,
            lookup=lambda s: self._lookup(state, s),
            sort_of=self._sort_for,
            result_width=result_width,
        )

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
