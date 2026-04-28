"""Materialize interval-domain results as TAC ``assume`` commands.

For each block, emit one assume per var whose interval at the block's
exit is non-trivial (tighter than the var's sort default). Emissions
go right before the block's terminator.

**Dominance gate.** An emission of ``X`` at block ``B`` is sound only
when ``B`` is dominated by some def block of ``X``. Reason: in the
original program, ``X`` is "live" only at blocks reachable from a def
of ``X``, and DSA additionally guarantees the def dominates uses. At
a non-dominated block, the var's value is undefined on some
incoming paths — sea_vc encodes def equalities unconditionally, so
introducing a *new* read at a non-dominated block forces z3 to
consider models where the def block is off-path and the analysis's
operand refinements at the def haven't fired. Materialization
without the dominance gate produces SAT counter-examples on rw-eq.

Soundness contract: every emitted assume follows from the original
program's reachable state at the emission point. Validated
end-to-end via ``rw_eq.emit_equivalence_program`` + z3 — see
``tests/test_interval_materialize.py``.
"""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass

import networkx as nx

from ctac.analysis.abs_int.domains.interval import analyze_intervals
from ctac.analysis.abs_int.interval_ops import Interval
from ctac.analysis.defuse import extract_def_use
from ctac.ast.nodes import (
    ApplyExpr,
    AssertCmd,
    AssumeExpCmd,
    ConstExpr,
    JumpCmd,
    JumpiCmd,
    SymbolRef,
    TacCmd,
    TacExpr,
)
from ctac.graph.cfg import Cfg
from ctac.ir.models import NBId, TacBlock, TacProgram


@dataclass(frozen=True)
class MaterializeReport:
    blocks_with_emissions: int
    assumes_emitted: int


_TERMINATOR_TYPES = (JumpCmd, JumpiCmd, AssertCmd)


def materialize_intervals(
    program: TacProgram,
    *,
    symbol_sorts: Mapping[str, str] | None = None,
) -> tuple[TacProgram, MaterializeReport]:
    """Run interval analysis on ``program`` and return a copy with
    inferred bounds inserted as ``assume`` commands at the end of each
    block's static section (before any DSA-dynamic assignment and
    before the terminator).

    The original commands are preserved verbatim — the augmented
    program is the original plus fresh assumes. Soundness of every
    emitted assume rests on two contracts:

    1. **Dominance gate.** An assume on var ``X`` is emitted at block
       ``B`` only when ``B`` is dominated by some def block of ``X``.
       In a DSA program every actual use of ``X`` is dominated by a
       def, so emissions at dominated blocks correspond to legitimate
       reads — the analysis's claim, plus dominance, plus the
       sequential semantics of the def block, gives the soundness
       story directly. Without this, materialization would create
       fake reads of ``X`` outside its live range, and sea_vc's
       unconditional def encoding would let z3 construct
       counter-models.
    2. **Placement.** Materialized assumes go *after* every other
       command in the block but before the terminator. ``rw-eq``'s
       ``_hoist_statics_above_dynamics`` only reorders static
       AssignExpCmds (LHS not in DSA-dynamic), not AssumeExpCmds, so
       sea_vc's ``(static)*(dynamic)*terminator`` shape rule doesn't
       constrain assume placement. Putting the assumes after all
       defs in the block also avoids use-before-def for any var
       defined dynamically in the same block.
    """
    result = analyze_intervals(program, symbol_sorts=symbol_sorts)
    sorts = dict(symbol_sorts or {})

    def sort_default(var: str) -> Interval:
        sort = sorts.get(var)
        if sort == "bool":
            return Interval(0, 1)
        if sort and sort.startswith("bv"):
            rest = sort[2:]
            if rest.isdigit():
                w = int(rest)
                return Interval(0, (1 << w) - 1)
        return Interval(None, None)

    def is_emittable(var: str, interval: Interval) -> bool:
        if interval.is_top() or interval.is_bot():
            return False
        return interval != sort_default(var)

    # Def sites, keyed by canonical name (parallel-assignment SSA
    # renames like ``R1048:26`` resolve to the canonical's defs).
    du = extract_def_use(program)

    def_blocks_by_var: dict[str, set[NBId]] = {
        var: {d.block_id for d in defs}
        for var, defs in du.definitions_by_symbol.items()
        if defs
    }

    # Dominance scope per var: the set of blocks dominated by at least
    # one of the var's def blocks. An emission of ``var`` at block B
    # is sound iff B ∈ dominance_scope[var]. (For DSA-static vars this
    # is the dominator subtree of the single def; for DSA-dynamic
    # vars it's the union over all defs.)
    dominators = _compute_dominators(program)
    dominance_scope: dict[str, frozenset[NBId]] = {}
    for var, def_blocks in def_blocks_by_var.items():
        scope = {
            b for b, dom_set in dominators.items() if dom_set & def_blocks
        }
        dominance_scope[var] = frozenset(scope)

    new_blocks: list[TacBlock] = []
    total_assumes = 0
    blocks_with_emissions = 0

    for block in program.blocks:
        local = result.per_block_local.get(block.id, {})
        emissions: list[tuple[str, Interval]] = []

        # Block-local refinements (apply only at this block onward).
        for var, interval in sorted(local.items()):
            if not is_emittable(var, interval):
                continue
            scope = dominance_scope.get(var)
            if scope is None or block.id not in scope:
                continue
            emissions.append((var, interval))

        # Static facts: emit at the var's def block, after the def
        # has been processed in the original. The def block is itself
        # in the var's dominance scope, so the gate is automatically
        # satisfied. Skip if a local entry at this block already
        # covers it (local shadows static).
        for var, interval in sorted(result.static.items()):
            def_blocks = def_blocks_by_var.get(var)
            if def_blocks is None or block.id not in def_blocks:
                continue
            if var in local:
                continue
            if is_emittable(var, interval):
                emissions.append((var, interval))

        new_cmds = _insert_assumes_before_terminator(
            block.commands, emissions
        )
        new_blocks.append(
            TacBlock(
                id=block.id,
                successors=list(block.successors),
                commands=new_cmds,
            )
        )
        if emissions:
            blocks_with_emissions += 1
            total_assumes += len(emissions)

    return TacProgram(blocks=new_blocks), MaterializeReport(
        blocks_with_emissions=blocks_with_emissions,
        assumes_emitted=total_assumes,
    )


def _compute_dominators(
    program: TacProgram,
) -> dict[NBId, frozenset[NBId]]:
    """Block-level dominator sets via networkx. Each block's set
    includes the block itself. Mirrors
    ``ctac.rewrite.context._compute_dominators`` — duplicated here to
    avoid making this module depend on the rewriter; promote when a
    third caller wants it."""
    if not program.blocks:
        return {}
    entry = program.blocks[0].id
    digraph = Cfg(program).to_digraph()
    idom = nx.immediate_dominators(digraph, entry)
    dom: dict[NBId, frozenset[NBId]] = {}

    def dominators_of(node: NBId) -> frozenset[NBId]:
        if node in dom:
            return dom[node]
        parent = idom.get(node, node)
        if parent == node:
            result = frozenset({node})
        else:
            result = frozenset({node}) | dominators_of(parent)
        dom[node] = result
        return result

    for node in idom:
        dominators_of(node)
    return dom


def _insert_assumes_before_terminator(
    cmds: list[TacCmd],
    emissions: list[tuple[str, Interval]],
) -> list[TacCmd]:
    """Insert materialized assumes immediately before the block's
    terminator (last ``JumpCmd``/``JumpiCmd``/``AssertCmd``), placing
    them after every other command in the block. This is after all
    defs (so no use-before-def for vars defined in this block) and
    before the terminator (so they fire on the way out)."""
    if not emissions:
        return list(cmds)
    insert_at = len(cmds)
    for i in range(len(cmds) - 1, -1, -1):
        if isinstance(cmds[i], _TERMINATOR_TYPES):
            insert_at = i
            break
    new_assumes = [_assume_for(var, interval) for var, interval in emissions]
    return list(cmds[:insert_at]) + new_assumes + list(cmds[insert_at:])


def _assume_for(var: str, interval: Interval) -> AssumeExpCmd:
    cond = _interval_to_cond(var, interval)
    return AssumeExpCmd(raw=f"AssumeExpCmd {_render(cond)}", condition=cond)


def _interval_to_cond(var: str, interval: Interval) -> TacExpr:
    sym = SymbolRef(name=var)
    # Point interval: emit Eq.
    if (
        interval.lo is not None
        and interval.hi is not None
        and interval.lo == interval.hi
    ):
        return ApplyExpr(op="Eq", args=(sym, _const(interval.lo)))
    parts: list[TacExpr] = []
    if interval.lo is not None:
        parts.append(ApplyExpr(op="Ge", args=(sym, _const(interval.lo))))
    if interval.hi is not None:
        parts.append(ApplyExpr(op="Le", args=(sym, _const(interval.hi))))
    if not parts:
        # TOP — caller filtered these out, but defensively emit a tautology.
        return ApplyExpr(op="Eq", args=(_const(0), _const(0)))
    if len(parts) == 1:
        return parts[0]
    return ApplyExpr(op="LAnd", args=tuple(parts))


def _const(k: int) -> ConstExpr:
    return ConstExpr(value=hex(k) if k >= 0 else str(k))


def _render(cond: TacExpr) -> str:
    if isinstance(cond, ConstExpr):
        return str(cond.value)
    if isinstance(cond, SymbolRef):
        return cond.name
    if isinstance(cond, ApplyExpr):
        return f"{cond.op}({' '.join(_render(a) for a in cond.args)})"
    return "?"
