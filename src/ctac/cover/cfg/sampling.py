"""Random path sampling over a TAC CFG.

Two operations:

- `random_path(info, seed)`: random walk from entry to assert. DAG
  assumption (cover requires loop-free TAC), so once we visit a
  block we never revisit it; the walk may get stuck if every
  feasible successor leads only to non-assert sinks. Returns the
  ordered block list or None on stuck.

- `path_through_block(info, target)`: shortest path
  `entry -> target -> assert`, useful for *block-level saturation*
  — when a block hasn't been covered by any sample, ensure at least
  one path goes through it.

Output is the *block list in visit order*. Callers convert to a
`frozenset(path)` (the "keep set") for clustering.
"""
from __future__ import annotations

import random
from collections.abc import Sequence

import networkx as nx

from ctac.cover.cfg.cfg_graph import CfgInfo
from ctac.ir.models import NBId


def random_path(info: CfgInfo, seed: int, *,
                  max_steps: int = 10_000) -> list[NBId] | None:
    """Random walk entry → assert. None if walk gets stuck (no feasible
    next block, where 'feasible' = unvisited)."""
    g = info.graph
    rng = random.Random(seed)
    path = [info.entry]
    seen = {info.entry}
    cur = info.entry
    while cur != info.assert_block:
        succs = list(g.successors(cur))
        if not succs:
            return None
        feasible = [s for s in succs if s not in seen]
        if not feasible:
            return None
        nxt = rng.choice(feasible)
        path.append(nxt)
        seen.add(nxt)
        cur = nxt
        if len(path) > max_steps:
            return None
    return path


def path_through_block(info: CfgInfo, target: NBId) -> list[NBId] | None:
    """Concatenated `entry -> target -> assert` shortest path, or None
    if either leg is unreachable."""
    g = info.graph
    try:
        a = nx.shortest_path(g, info.entry, target)
        b = nx.shortest_path(g, target, info.assert_block)
    except nx.NetworkXNoPath:
        return None
    return list(a) + list(b[1:])


def sample_paths(info: CfgInfo, *, n: int,
                   seed: int = 0,
                   dedupe: bool = True) -> list[list[NBId]]:
    """Sample up to `n` distinct random paths.

    Walks may fail (return None) — those are skipped, but the call
    still tries up to `n * 4` seeds to fill the budget. With dedupe
    on, identical block-sequences are collapsed (so coverage is what
    matters, not raw sample count)."""
    out: list[list[NBId]] = []
    seen: set[tuple[NBId, ...]] = set()
    tries_budget = n * 4
    s = seed
    while len(out) < n and tries_budget > 0:
        p = random_path(info, s)
        s += 1
        tries_budget -= 1
        if p is None:
            continue
        key = tuple(p)
        if dedupe and key in seen:
            continue
        seen.add(key)
        out.append(p)
    return out


def uncovered_blocks(info: CfgInfo,
                      paths: Sequence[Sequence[NBId]]) -> list[NBId]:
    """Blocks reachable from entry-to-assert that no sampled path
    visits. The saturation step uses this to push more paths through
    rare blocks."""
    from ctac.cover.cfg.cfg_graph import blocks_on_entry_to_assert_paths
    target = blocks_on_entry_to_assert_paths(info)
    covered: set[NBId] = set()
    for p in paths:
        covered.update(p)
    return sorted(target - covered)


def saturate_paths(info: CfgInfo,
                    paths: list[list[NBId]],
                    *, max_added: int = 64) -> list[list[NBId]]:
    """For each uncovered block, find a path through it (deterministic
    shortest path) and add it. Returns the augmented list.

    Bounded by `max_added` so a very wide CFG doesn't blow up the
    sample set; the user can re-run with larger `--samples` if they
    really want more coverage."""
    added = 0
    out = list(paths)
    seen_keys = {tuple(p) for p in out}
    for b in uncovered_blocks(info, out):
        if added >= max_added:
            break
        p = path_through_block(info, b)
        if p is None:
            continue
        key = tuple(p)
        if key in seen_keys:
            continue
        out.append(p)
        seen_keys.add(key)
        added += 1
    return out
