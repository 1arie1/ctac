"""CFG simplification: drop annotation-only fall-through blocks.

The post-rw TAC from the Solana frontend retains "fall-through" basic
blocks — blocks whose body is purely ``AnnotationCmd`` /
``LabelCmd`` (DSA-assignment breadcrumbs) with no executable cmd and
no explicit terminator, single declared successor in ``Succ [...]``.
``ctac rw`` doesn't touch CFG shape, so these blocks are preserved
through the rewriter even though no real computation lives in them.

This pass drops such blocks and rewires their predecessor
terminators directly to the dropped block's successor. Soundness
under the rw-eq **stuttering-simulation walker** (see
``ctac.rw_eq.sim_precheck``): dropped blocks become stutter, rewired
predecessors become divergence points, the successor becomes a sync
point. Joint-post-dom is trivial (the fall-through has a single
successor that is its unique matched frontier); disjoint-stutter-
region holds because each dropped block has a unique LHS predecessor
by our restriction.

Scope: this pass is **not** a rewrite rule — it's a CFG-shape
transform, distinct from the rule-based rewriter in
``ctac.rewrite``. It can be invoked standalone via the
``ctac cfg-simplify`` CLI or as the optional final step of
``ctac rw`` (``--simplify-cfg``).
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from typing import Final

from ctac.ast.nodes import (
    AnnotationCmd,
    JumpCmd,
    JumpiCmd,
    LabelCmd,
    TacCmd,
)
from ctac.ir.models import NBId, TacBlock, TacProgram
from ctac.rewrite.unparse import canonicalize_cmd


# Cmd types whose presence does NOT disqualify a block from being a
# fall-through candidate. Anything else (assignments, assumes, asserts,
# jumps) marks the block as load-bearing.
_PASSTHROUGH_BODY_TYPES: Final = (AnnotationCmd, LabelCmd)


@dataclass(frozen=True)
class CfgSimplifyReport:
    """Per-invocation summary of what the simplifier did."""

    dropped_blocks: tuple[NBId, ...]
    # (pred_id, dropped_block, new_target) — one entry per
    # individual target replacement, regardless of whether multiple
    # replacements happened in the same JumpiCmd.
    rewires: tuple[tuple[NBId, NBId, NBId], ...]
    # Fall-through candidates skipped because they had more than one
    # LHS predecessor (would violate the rw-eq stuttering walker's
    # disjoint-stutter-region invariant).
    skipped_multipred: tuple[NBId, ...]

    @property
    def n_dropped(self) -> int:
        return len(self.dropped_blocks)

    @property
    def is_noop(self) -> bool:
        return not self.dropped_blocks


def simplify_cfg(program: TacProgram) -> tuple[TacProgram, CfgSimplifyReport]:
    """Drop annotation-only fall-through blocks with unique predecessors;
    rewire each predecessor's terminator to skip the dropped block.

    The pass collapses chains transparently: if ``A → X → Y → Z`` and
    both ``X`` and ``Y`` are droppable fall-throughs, the result is
    ``A → Z`` with both blocks removed in one invocation.

    Idempotent: re-running on the result is a no-op (the report's
    ``is_noop`` property holds).

    Raises:
        ValueError: a fall-through candidate's terminator-free shape
            is inconsistent with its successors list (defensive guard
            against malformed input).
    """
    # Step 1: identify candidates (annotation-only body, single succ,
    # not a self-loop).
    candidate_succ: dict[NBId, NBId] = {}
    for b in program.blocks:
        if not _is_fall_through_candidate(b):
            continue
        succ = b.successors[0]
        if succ == b.id:
            # Annotation-only self-loop — degenerate, skip.
            continue
        candidate_succ[b.id] = succ

    # Step 2: build LHS predecessor index from the original program.
    preds = _build_pred_index(program)

    # Step 3: restrict to unique-predecessor candidates (the safe
    # subset for the rw-eq stuttering walker).
    droppable_succ: dict[NBId, NBId] = {}
    skipped: list[NBId] = []
    for bid, succ in candidate_succ.items():
        pred_set = preds.get(bid, frozenset())
        if len(pred_set) > 1:
            skipped.append(bid)
            continue
        if not pred_set:
            # No predecessors (entry block or already-orphan). Not
            # interesting; leave it alone.
            continue
        droppable_succ[bid] = succ

    if not droppable_succ:
        return program, CfgSimplifyReport(
            dropped_blocks=(),
            rewires=(),
            skipped_multipred=tuple(sorted(skipped)),
        )

    # Step 4: collapse drop chains. If X drops to Y and Y drops to Z,
    # X's effective successor is Z (and both X and Y are removed).
    drop_set = frozenset(droppable_succ.keys())
    transitive_target: dict[NBId, NBId] = {
        bid: _follow_drop_chain(succ, droppable_succ)
        for bid, succ in droppable_succ.items()
    }

    # Step 5: rewrite each surviving block. If its terminator (when
    # present) references a dropped block, redirect to the transitive
    # successor.
    rewires: list[tuple[NBId, NBId, NBId]] = []
    new_blocks: list[TacBlock] = []
    for b in program.blocks:
        if b.id in drop_set:
            continue

        new_term, block_rewires = _rewire_block_terminator(
            b, transitive_target, drop_set
        )
        rewires.extend(block_rewires)
        # Successors derive from the (possibly rewritten) terminator.
        new_cmds = list(b.commands)
        if new_term is not None and new_cmds:
            new_cmds[-1] = new_term

        new_successors = _successors_from_block(new_cmds, b, transitive_target, drop_set)

        if new_term is not None or new_successors != b.successors:
            new_blocks.append(
                TacBlock(id=b.id, successors=new_successors, commands=new_cmds)
            )
        else:
            new_blocks.append(b)

    new_program = TacProgram(blocks=new_blocks)
    return new_program, CfgSimplifyReport(
        dropped_blocks=tuple(sorted(drop_set)),
        rewires=tuple(rewires),
        skipped_multipred=tuple(sorted(skipped)),
    )


def _is_fall_through_candidate(block: TacBlock) -> bool:
    """A block qualifies if it has exactly one declared successor and
    its body contains only passthrough (annotation / label) cmds."""
    if len(block.successors) != 1:
        return False
    return all(isinstance(c, _PASSTHROUGH_BODY_TYPES) for c in block.commands)


def _build_pred_index(program: TacProgram) -> dict[NBId, frozenset[NBId]]:
    preds: dict[NBId, set[NBId]] = {b.id: set() for b in program.blocks}
    for b in program.blocks:
        for s in b.successors:
            preds.setdefault(s, set()).add(b.id)
    return {k: frozenset(v) for k, v in preds.items()}


def _follow_drop_chain(start: NBId, drop_succ: dict[NBId, NBId]) -> NBId:
    """If ``start`` itself is a dropped block, follow the chain of
    drops to the first surviving block. Cycle-safe."""
    current = start
    visited: set[NBId] = set()
    while current in drop_succ and current not in visited:
        visited.add(current)
        current = drop_succ[current]
    return current


def _rewire_block_terminator(
    block: TacBlock,
    transitive_target: dict[NBId, NBId],
    drop_set: frozenset[NBId],
) -> tuple[TacCmd | None, list[tuple[NBId, NBId, NBId]]]:
    """Inspect ``block``'s last command. If it's a JumpCmd/JumpiCmd
    referencing a dropped block, return a new canonicalized
    terminator and the list of (pred, dropped, new_target) rewires
    performed. Otherwise return (None, [])."""
    if not block.commands:
        return None, []
    last = block.commands[-1]
    if not isinstance(last, (JumpCmd, JumpiCmd)):
        return None, []

    rewires: list[tuple[NBId, NBId, NBId]] = []

    if isinstance(last, JumpCmd):
        if last.target not in drop_set:
            return None, []
        new_target = transitive_target[last.target]
        rewires.append((block.id, last.target, new_target))
        new_term = canonicalize_cmd(replace(last, target=new_target))
        return new_term, rewires

    # JumpiCmd
    new_then = last.then_target
    new_else = last.else_target
    if last.then_target in drop_set:
        new_then = transitive_target[last.then_target]
        rewires.append((block.id, last.then_target, new_then))
    if last.else_target in drop_set:
        new_else = transitive_target[last.else_target]
        rewires.append((block.id, last.else_target, new_else))
    if not rewires:
        return None, []
    if new_then == new_else:
        # Both arms collapse to one target; emit JumpCmd directly.
        new_term = canonicalize_cmd(
            JumpCmd(raw="", target=new_then, meta_index=last.meta_index)
        )
    else:
        new_term = canonicalize_cmd(
            replace(last, then_target=new_then, else_target=new_else)
        )
    return new_term, rewires


def _successors_from_block(
    new_cmds: list[TacCmd],
    block: TacBlock,
    transitive_target: dict[NBId, NBId],
    drop_set: frozenset[NBId],
) -> list[NBId]:
    """Compute the surviving block's new successors list.

    If a terminator is present (after rewrite), successors derive
    from it. If there's no terminator (annotation-only block that
    wasn't dropped — e.g., a multi-pred skipped candidate), keep
    the declared successors but redirect any drop-set entries to
    their transitive targets."""
    if new_cmds:
        last = new_cmds[-1]
        if isinstance(last, JumpCmd):
            return [last.target]
        if isinstance(last, JumpiCmd):
            return [last.then_target, last.else_target]
    # No terminator: rewrite declared successors directly.
    return [
        transitive_target[s] if s in drop_set else s
        for s in block.successors
    ]


__all__ = ["CfgSimplifyReport", "simplify_cfg"]
