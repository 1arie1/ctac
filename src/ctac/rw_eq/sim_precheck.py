"""Structural pre-check for the rw-eq stuttering-simulation walker.

Verifies that an ``(orig, rw)`` pair fits the **weak (forward)
simulation with one-sided τ** shape — RHS's block-id set is a subset
of LHS's, every divergence point's stutter region reaches exactly
RHS's target set (joint-post-dominator), and stutter regions of
distinct divergence points are pairwise disjoint.

The check is pure-structural: runs on the two CFGs before any SMT
work. The output :class:`SimDecomposition` carries the data the
walker needs to emit per-A ``DEST_A`` ghost defs and per-B
``IN_DEST_B`` RC-gated ITE phi-merges.

References
----------

See ``ctac-research/journal/2026-05/2026-05-24-rw-eq-stuttering-simulation-theory-and-per-a-witness.md``
for the design rationale and bibliography. The structural property
is a special instance of "asymmetric product programs" with bounded
stuttering (Barthe-Crespo-Kunz 2013; Browne-Clarke-Grumberg 1988).
"""

from __future__ import annotations

from dataclasses import dataclass

from ctac.graph.cfg import Cfg
from ctac.ir.models import TacProgram
from ctac.rw_eq.model import BlockRef, StructuralSimError


@dataclass(frozen=True)
class SimDecomposition:
    """Decomposition of an ``(orig, rw)`` pair into the categories the
    stuttering-simulation walker dispatches on.

    All blocks are referenced via :class:`BlockRef`. The decomposition
    is closed under the following invariants when produced by
    :func:`analyze_simulation`:

    - ``stutter ⊆ orig.block_ids``, ``stutter ∩ rw.block_ids == ∅``.
    - ``matched == rw.block_ids ⊆ orig.block_ids``.
    - ``divergence_points ⊆ matched``.
    - ``sync_points ⊆ matched``.
    - ``stutter_owner.keys() == stutter`` and each value is in
      ``divergence_points``.
    """

    matched: frozenset[BlockRef]
    stutter: frozenset[BlockRef]
    divergence_points: frozenset[BlockRef]
    sync_points: frozenset[BlockRef]
    stutter_owner: dict[BlockRef, BlockRef]


def analyze_simulation(orig: TacProgram, rw: TacProgram) -> SimDecomposition:
    """Compute the matched / stutter / divergence / sync decomposition
    and verify both structural properties.

    Raises:
        StructuralSimError: ``rw`` is not a structural sub-CFG of
            ``orig`` (some rw block id is missing in orig), the
            joint-post-dominator condition fails at some divergence
            point, or two divergence points share a stutter block.

    The function is pure: no side effects, no SMT, no rewriter
    invocation. Cost is O(|orig| + |orig.edges|) for the partition +
    one BFS per divergence point through the stutter subgraph; for
    realistic post-rw CFGs (tens of blocks), this is microseconds.
    """
    orig_blocks_by_id = orig.block_by_id()
    rw_blocks_by_id = rw.block_by_id()

    matched_ids = set(rw_blocks_by_id) & set(orig_blocks_by_id)
    if set(rw_blocks_by_id) - matched_ids:
        missing = sorted(set(rw_blocks_by_id) - matched_ids)
        raise StructuralSimError(
            f"rw program has block id(s) {missing!r} not present in orig; "
            f"stuttering simulation requires rw's block ids to be a subset "
            f"of orig's"
        )
    stutter_ids = set(orig_blocks_by_id) - matched_ids

    matched = frozenset(BlockRef(id=bid) for bid in matched_ids)
    stutter = frozenset(BlockRef(id=bid) for bid in stutter_ids)

    # Divergence points: matched blocks where orig's successor list
    # differs from rw's. (Equal as ordered lists ⇒ same shape; differ
    # as sets or order ⇒ structural divergence at the terminator.)
    divergence_set: set[BlockRef] = set()
    for bid in matched_ids:
        ob = orig_blocks_by_id[bid]
        rb = rw_blocks_by_id[bid]
        if list(ob.successors) != list(rb.successors):
            divergence_set.add(BlockRef(id=bid))
    divergence_points = frozenset(divergence_set)

    # Sync points: matched blocks whose LHS predecessor set differs
    # from their RHS predecessor set. Predecessors are computed by
    # inverting the CFG once per program.
    sync_set: set[BlockRef] = set()
    orig_preds = _pred_index(orig)
    rw_preds = _pred_index(rw)
    for bid in matched_ids:
        if orig_preds.get(bid, frozenset()) != rw_preds.get(bid, frozenset()):
            sync_set.add(BlockRef(id=bid))
    sync_points = frozenset(sync_set)

    # Joint-post-dominator + disjoint-stutter-region check, fused into
    # one per-A pass. From A, walk through stutter blocks only (stop
    # at any matched successor). The matched frontier reached this way
    # must equal T = rw's target set at A.
    orig_dg = Cfg(orig).to_digraph()
    stutter_owner: dict[BlockRef, BlockRef] = {}
    for A in divergence_points:
        rb = rw_blocks_by_id[A.id]
        # T = rw's target set at A — what divergence A "commits" to.
        T = set(rb.successors)

        # Stutter-region BFS from A: a node n is expanded only if it's
        # A itself (the seed) or a stutter block. Successors that are
        # matched blocks are recorded as frontier targets; successors
        # that are stutter blocks get queued for further expansion.
        reachable_stutter: set[str] = set()
        frontier: set[str] = set()
        queue: list[str] = [A.id]
        seen: set[str] = {A.id}
        while queue:
            n = queue.pop(0)
            for succ in orig_dg.successors(n):
                if succ in matched_ids:
                    frontier.add(succ)
                elif succ in stutter_ids:
                    if succ not in seen:
                        seen.add(succ)
                        reachable_stutter.add(succ)
                        queue.append(succ)

        if frontier != T:
            extra = sorted(frontier - T)
            missing = sorted(T - frontier)
            raise StructuralSimError(
                f"joint-post-dominator violation at divergence point {A.id!r}: "
                f"rw targets are {sorted(T)!r}, "
                f"orig τ-frontier is {sorted(frontier)!r} "
                f"(extra={extra!r}, missing={missing!r})"
            )
        # Each stutter block in A's region must be uniquely owned across
        # all divergence points.
        for s_id in reachable_stutter:
            s_ref = BlockRef(id=s_id)
            existing = stutter_owner.get(s_ref)
            if existing is not None and existing != A:
                raise StructuralSimError(
                    f"stutter block {s_id!r} is reachable from divergence "
                    f"points {existing.id!r} and {A.id!r}; per-A DEST "
                    f"witness picker is ambiguous (cleanup overlaps two "
                    f"divergence regions). Either narrow the cleanup, or "
                    f"escalate to full SSA at dominance frontiers."
                )
            stutter_owner[s_ref] = A

    # Every stutter block must be owned by *some* divergence point —
    # otherwise it's unreachable from any divergence, which means the
    # rw doesn't drop any structure here; rw should have kept the block.
    orphan_stutters = stutter - frozenset(stutter_owner.keys())
    if orphan_stutters:
        names = sorted(s.id for s in orphan_stutters)
        raise StructuralSimError(
            f"orig has stutter block(s) {names!r} not reachable from any "
            f"divergence point; the (orig, rw) pair is not a valid "
            f"stuttering rewrite (rw is missing these blocks but no "
            f"divergence point hands off control to them)"
        )

    return SimDecomposition(
        matched=matched,
        stutter=stutter,
        divergence_points=divergence_points,
        sync_points=sync_points,
        stutter_owner=stutter_owner,
    )


def _pred_index(program: TacProgram) -> dict[str, frozenset[str]]:
    """Inverse of ``block.successors``: ``bid -> {predecessor_bids}``."""
    preds: dict[str, set[str]] = {b.id: set() for b in program.blocks}
    for b in program.blocks:
        for s in b.successors:
            preds.setdefault(s, set()).add(b.id)
    return {k: frozenset(v) for k, v in preds.items()}


__all__ = ["SimDecomposition", "analyze_simulation"]
