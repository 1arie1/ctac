"""Random-path selection for ``ctac pin --path BLKS``.

Given a list of anchor block ids, returns a single linear path
through the program's CFG that visits every anchor. When more than
one path is feasible, one is chosen uniformly over the local
successor choice at each branch.

The result feeds the pin drop pipeline as
``drop = all_blocks \\ chosen_path`` — branch terminators along the
chosen path are then folded by ``_drop_cfg_surgery`` as usual.
"""

from __future__ import annotations

import random

import networkx as nx

from ctac.ir.models import TacProgram
from ctac.transform.pin import BlockId, _cfg_digraph, _entry_block_id


def _dedup_preserving_order(anchors: tuple[BlockId, ...]) -> list[BlockId]:
    seen: set[BlockId] = set()
    out: list[BlockId] = []
    for a in anchors:
        if a not in seen:
            seen.add(a)
            out.append(a)
    return out


def _topo_sort_anchors(
    cfg: nx.DiGraph, anchors: tuple[BlockId, ...]
) -> tuple[BlockId, ...]:
    """Sort anchors by the CFG's topological order. Loop-free
    precondition is enforced by ``nx.topological_sort`` (raises on
    cycles)."""
    topo = {bid: i for i, bid in enumerate(nx.topological_sort(cfg))}
    uniq = _dedup_preserving_order(anchors)
    return tuple(sorted(uniq, key=lambda a: topo[a]))


def _validate_anchors(
    cfg: nx.DiGraph, entry: BlockId, anchors: tuple[BlockId, ...]
) -> None:
    unknown = [a for a in anchors if a not in cfg]
    if unknown:
        raise ValueError(
            "anchor block(s) not in program: "
            + ", ".join(repr(a) for a in unknown)
        )
    prev = entry
    for a in anchors:
        if a == prev:
            continue
        if a not in nx.descendants(cfg, prev):
            raise ValueError(
                f"anchor {a!r} is not reachable from {prev!r} in the CFG"
            )
        prev = a


def choose_random_path(
    program: TacProgram,
    anchors: tuple[BlockId, ...],
    *,
    seed: int | None = None,
) -> tuple[BlockId, ...]:
    """Sample one linear path through ``program`` that visits every
    block in ``anchors``.

    Anchors are auto-topologically sorted; the user-supplied order
    need not match the CFG's topo order. Branch choices at each
    step are uniform over feasible immediate successors — where
    "feasible" means "can still reach the next remaining anchor"
    (or "can reach a terminal" once all anchors are consumed).

    Returns an ordered tuple of block ids starting at the program
    entry and ending at a terminal (no-successors) block.

    Raises ``ValueError`` when an anchor isn't in the CFG, when the
    anchor chain ``entry → A_0 → A_1 → ...`` is unreachable, or
    when the walk dead-ends before consuming every anchor (a
    safety net; validation should rule it out)."""
    if not program.blocks:
        raise ValueError("program has no blocks")
    cfg = _cfg_digraph(program)
    entry = _entry_block_id(program)

    # Existence check first — topo-sort would KeyError on unknown
    # anchors and produce a confusing trace.
    unknown = tuple(a for a in anchors if a not in cfg)
    if unknown:
        raise ValueError(
            "anchor block(s) not in program: "
            + ", ".join(repr(a) for a in unknown)
        )
    sorted_anchors = _topo_sort_anchors(cfg, anchors)
    _validate_anchors(cfg, entry, sorted_anchors)

    # back_reach[a] = a + every block that can reach a. Used to
    # filter successors at each step to ones still consistent with
    # the next remaining anchor.
    back_reach: dict[BlockId, set[BlockId]] = {
        a: {a} | set(nx.ancestors(cfg, a)) for a in sorted_anchors
    }

    rng = random.Random(seed)
    path: list[BlockId] = [entry]
    remaining = list(sorted_anchors)
    while remaining and path[-1] == remaining[0]:
        remaining.pop(0)

    current = entry
    while True:
        successors = list(cfg.successors(current))
        if not successors:
            break
        if remaining:
            target = remaining[0]
            feasible = [s for s in successors if s in back_reach[target]]
        else:
            feasible = successors
        if not feasible:
            raise ValueError(
                f"random-path walker dead-ended at {current!r} "
                f"with anchors remaining: {remaining}"
            )
        # Sort first so the seed reproduces the same choice across
        # runs regardless of dict / set iteration order.
        feasible.sort()
        nxt = rng.choice(feasible)
        path.append(nxt)
        while remaining and nxt == remaining[0]:
            remaining.pop(0)
        current = nxt

    if remaining:
        raise ValueError(
            "random-path walker terminated without visiting anchors: "
            + ", ".join(repr(a) for a in remaining)
        )

    return tuple(path)


def drop_set_for_path(
    program: TacProgram, chosen: tuple[BlockId, ...]
) -> tuple[BlockId, ...]:
    """Return blocks in ``program`` not on ``chosen``, in source
    order. Suitable for ``PinPlan.drops``."""
    on_path = set(chosen)
    return tuple(b.id for b in program.blocks if b.id not in on_path)
