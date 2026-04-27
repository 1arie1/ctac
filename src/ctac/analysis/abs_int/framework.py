"""Frontier-based forward sweep over a DSA, loop-free TAC program.

The framework is just orchestration: walks blocks in topological order,
maintaining a `pending` frontier of in-flight states (entries to be
processed) and an `exit_states` map (state at the exit of each block
whose commands have been transferred). Domains plug into a uniform
protocol; storage representation is the domain's choice.
"""

from __future__ import annotations

from ctac.analysis.abs_int.protocol import Domain, State
from ctac.ast.nodes import (
    AnnotationCmd,
    ApplyExpr,
    JumpiCmd,
    LabelCmd,
    SymbolRef,
    TacExpr,
)
from ctac.graph.cfg import Cfg
from ctac.ir.models import NBId, TacBlock, TacProgram

# Alias kept for clarity: the result type of `run()` is a per-block
# exit-state map. Storage strategy 1 domains have all entries point to
# the same instance; per-block-full domains have distinct entries.
Frontier = dict[NBId, State]

_NOISE_TYPES = (AnnotationCmd, LabelCmd)


def edge_condition(src: TacBlock, dst: TacBlock) -> TacExpr | None:
    """Return the boolean condition that must hold to traverse src → dst.

    For an unconditional `JumpCmd` (or no terminator) the condition is
    `None`. For a `JumpiCmd`, the framework returns `SymbolRef(condition)`
    on the then-edge and `LNot(SymbolRef(condition))` on the else-edge.
    """
    terminator = _terminator(src)
    if isinstance(terminator, JumpiCmd):
        cond = SymbolRef(name=terminator.condition)
        if dst.id == terminator.then_target:
            return cond
        if dst.id == terminator.else_target:
            return ApplyExpr(op="LNot", args=(cond,))
        # Block lists dst as a successor but the terminator doesn't —
        # treat as unconditional.
        return None
    return None


def _terminator(block: TacBlock):
    for cmd in reversed(block.commands):
        if isinstance(cmd, _NOISE_TYPES):
            continue
        return cmd
    return None


def run(program: TacProgram, domain: Domain[State]) -> Frontier:
    """Execute the analysis. Returns a `dict[NBId, State]` mapping each
    reachable block to its exit state (state after all of the block's
    commands have been transferred)."""
    if not program.blocks:
        return {}

    cfg = Cfg(program)
    by_id = program.block_by_id()
    entry = program.blocks[0]

    pending: dict[NBId, State] = {entry.id: domain.init(entry)}
    exit_states: dict[NBId, State] = {}

    for B in cfg.ordered_blocks():
        if B.id not in pending:
            # Unreachable from entry under the topological traversal.
            continue
        state = pending.pop(B.id)
        for cmd in B.commands:
            if isinstance(cmd, _NOISE_TYPES):
                continue
            state = domain.transfer(state, cmd, block=B)
        exit_states[B.id] = state
        for succ_id in B.successors:
            succ = by_id.get(succ_id)
            if succ is None:
                continue
            cond = edge_condition(B, succ)
            outgoing = domain.propagate(state, src=B, dst=succ, edge_cond=cond)
            if succ_id in pending:
                pending[succ_id] = domain.join(
                    [pending[succ_id], outgoing], dst=succ
                )
            else:
                pending[succ_id] = outgoing

    return exit_states
