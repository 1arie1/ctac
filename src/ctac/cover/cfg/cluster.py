"""K-medoid clustering over path keep-sets with Hamming distance.

Each sampled path is converted to a *keep set* — the unordered set of
blocks it visits. We cluster keep-sets so that paths in the same
cluster have similar block content; the cluster's *keep* is the
union of its member keep-sets, and the cluster's *drop* (for `ctac
pin --drop`) is the complement against the entry-to-assert block
universe.

K-medoid is preferred over K-means here because:
- Distance is set-Hamming (size of symmetric difference), not L2.
- Medoids are actual sample paths — useful as cluster representatives.
- Standalone implementation (no sklearn dependency) keeps the
  install footprint of `ctac` small.

The K-medoid loop is deterministic given the seed.
"""
from __future__ import annotations

import random
from collections.abc import Sequence
from dataclasses import dataclass

from ctac.ir.models import NBId


# Type aliases for readability — a "keep set" is the set of blocks
# along one path. Internally we use frozensets for hashing / cheap
# equality, with sorted tuples when stable iteration is needed.
KeepSet = frozenset[NBId]


@dataclass(frozen=True)
class Cluster:
    """One K-medoid cluster.

    `members` are indices into the input `keep_sets` list, NOT into
    any other indexing — keeps this trivially serializable. `medoid`
    is the index of the cluster's representative path. `keep_union`
    is the union of all member keep-sets (used as `ctac pin --drop`'s
    *kept* set, hence the name)."""

    id: str                       # "cluster_0", "cluster_1", ...
    members: tuple[int, ...]
    medoid: int
    keep_union: KeepSet


def hamming_set_distance(a: KeepSet, b: KeepSet) -> int:
    """Symmetric-difference cardinality: |a △ b| = |a∪b| - |a∩b|."""
    return len(a ^ b)


def cluster_paths(paths: Sequence[Sequence[NBId]], *,
                    k: int,
                    seed: int = 0,
                    max_iters: int = 50) -> list[Cluster]:
    """K-medoid clustering of path keep-sets.

    Returns one `Cluster` per medoid; the cluster ids are
    ``cluster_0``, ``cluster_1``, ...  in the order medoids were
    selected. Empty input or `k=0` returns an empty list."""
    if not paths or k <= 0:
        return []
    keeps: list[KeepSet] = [frozenset(p) for p in paths]
    n = len(keeps)
    k_eff = min(k, n)

    rng = random.Random(seed)

    # Initialize medoids: deterministic random sample of `k_eff` indices
    medoids = sorted(rng.sample(range(n), k_eff))

    for _ in range(max_iters):
        # Assign each point to the nearest medoid (ties → smaller idx).
        assignments = _assign(keeps, medoids)
        # Recompute medoid per cluster: point minimizing intra-cluster
        # distance sum.
        new_medoids = _recompute_medoids(keeps, assignments, medoids)
        if new_medoids == medoids:
            break
        medoids = new_medoids

    final_assignments = _assign(keeps, medoids)
    out: list[Cluster] = []
    for ci, m in enumerate(medoids):
        members = tuple(i for i, c in enumerate(final_assignments) if c == ci)
        if not members:
            continue
        keep_union: set[NBId] = set()
        for idx in members:
            keep_union.update(keeps[idx])
        out.append(Cluster(
            id=f'cluster_{ci}',
            members=members,
            medoid=m,
            keep_union=frozenset(keep_union),
        ))
    return out


def _assign(keeps: Sequence[KeepSet],
              medoids: Sequence[int]) -> list[int]:
    """Return the cluster index (into `medoids`) for each point."""
    out: list[int] = []
    for i, ks in enumerate(keeps):
        best_ci = 0
        best_d = hamming_set_distance(ks, keeps[medoids[0]])
        for ci in range(1, len(medoids)):
            d = hamming_set_distance(ks, keeps[medoids[ci]])
            if d < best_d:
                best_d = d
                best_ci = ci
        out.append(best_ci)
    return out


def _recompute_medoids(keeps: Sequence[KeepSet],
                         assignments: Sequence[int],
                         medoids: Sequence[int]) -> list[int]:
    """For each cluster, pick the member that minimizes sum of
    distances to all other members."""
    by_cluster: dict[int, list[int]] = {}
    for i, c in enumerate(assignments):
        by_cluster.setdefault(c, []).append(i)
    out: list[int] = []
    for ci, m in enumerate(medoids):
        members = by_cluster.get(ci, [m])  # cluster never goes empty in PAM
        best = members[0]
        best_cost = _cost(keeps, best, members)
        for cand in members[1:]:
            cost = _cost(keeps, cand, members)
            if cost < best_cost:
                best = cand
                best_cost = cost
        out.append(best)
    return out


def _cost(keeps: Sequence[KeepSet], center: int,
            members: Sequence[int]) -> int:
    """Sum of Hamming distances from `center` to every member."""
    cks = keeps[center]
    return sum(hamming_set_distance(cks, keeps[m]) for m in members)


def auto_k(num_paths: int) -> int:
    """Default = singleton-per-path: each sampled path is its own cluster.

    The strategy doc's original heuristic was ``max(3, samples/4)`` —
    aggressive top-down clustering. That bet failed in practice on
    bad_ua_rw (6/8 wider clusters timed out), and it inverts the actual
    workflow: solve a single path, get an unsat-core, use the core to
    diversify future probes. Clustering wider sub-problems is a
    follow-on optimization, not the baseline.

    With singleton-per-path: each cluster has a single linear path
    (`pin --drop` of its block-complement folds JumpiCmds), so each
    cluster's smt2 is a single-path slice — exactly the path-level
    workflow."""
    return max(0, num_paths)
