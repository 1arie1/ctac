"""Materialize interval-domain results as TAC ``assume`` commands.

For each block, emit one assume per var whose interval at the block's
exit is non-trivial (tighter than the var's sort default). Emissions
go right before the block's terminator. For the entry block we also
emit static facts (universally true). Other blocks emit only their
local refinements (block-scoped).

Soundness contract: every emitted assume must follow from the
original program's reachable state at the emission point. Validated
end-to-end by feeding (orig, materialized) to
``ctac.rw_eq.emit_equivalence_program`` and discharging every
emitted CHK assertion via z3 — see ``tests/test_interval_materialize.py``.
"""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass

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
    block (immediately before the terminator).

    The original commands are preserved verbatim — the augmented
    program is the original plus fresh assumes. Soundness of every
    emitted assume is the analysis's contract.
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

    # Each DSA-static var has a single def block; emit its static fact
    # at that block's end (after the def has fired in the original).
    # Emitting at entry's end is wrong for vars defined downstream —
    # the assume would reference an undefined symbol, which the SMT
    # encoder (correctly) rejects as use-before-def.
    du = extract_def_use(program)
    static_emit_block: dict[str, NBId] = {}
    for var, defs in du.definitions_by_symbol.items():
        if defs:
            static_emit_block[var] = defs[0].block_id

    new_blocks: list[TacBlock] = []
    total_assumes = 0
    blocks_with_emissions = 0

    for block in program.blocks:
        local = result.per_block_local.get(block.id, {})
        emissions: list[tuple[str, Interval]] = []

        # Block-local refinements (apply only at this block onward).
        for var, interval in sorted(local.items()):
            if is_emittable(var, interval):
                emissions.append((var, interval))

        # Static facts: emit at the var's def block, after the def
        # has been processed in the original. Skip if a local entry
        # at this block already covers it (local shadows static).
        for var, interval in sorted(result.static.items()):
            if static_emit_block.get(var) != block.id:
                continue
            if var in local:
                continue
            if is_emittable(var, interval):
                emissions.append((var, interval))

        new_cmds = _insert_assumes_before_terminator(block.commands, emissions)
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


def _insert_assumes_before_terminator(
    cmds: list[TacCmd], emissions: list[tuple[str, Interval]]
) -> list[TacCmd]:
    if not emissions:
        return list(cmds)
    term_idx = len(cmds)
    for i in range(len(cmds) - 1, -1, -1):
        if isinstance(cmds[i], _TERMINATOR_TYPES):
            term_idx = i
            break
    new_assumes = [_assume_for(var, interval) for var, interval in emissions]
    return list(cmds[:term_idx]) + new_assumes + list(cmds[term_idx:])


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
