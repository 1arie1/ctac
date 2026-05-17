"""Cluster absorption: widen a near-by cluster to swallow an escape path.

When the completeness probe finds an escape path π, two refinements
apply:

1. **Absorb (UNSAT-only refinement):** if π differs from some
   existing cluster K_j by at most `--absorb-threshold` blocks
   (Hamming distance), widen K_j to `K_j ∪ π` and re-solve at a
   *short* budget. If the widened cluster still closes UNSAT, the
   widening is geometric and cheap; update `K_j` in place and
   continue. If widened SAT → first-SAT-wins exits the cover.
2. **Singleton + core:** if no nearby cluster absorbs cheaply,
   materialize π as its own cluster and solve with `--unsat-core`
   (handled by the caller).

Absorption is what keeps the cluster count bounded on UNSAT-heavy
VCs. Without it, every escape spawns a singleton, and the loop
stacks pessimistic singletons until cores cover the CFG — slow.

Per the user's first-SAT clarification: **on SAT verdicts the cover
returns immediately; absorption only applies in the UNSAT path** —
we never widen a cluster around a SAT escape.
"""
from __future__ import annotations

from collections.abc import Sequence
from pathlib import Path
from typing import TYPE_CHECKING

from ctac.cover.cfg.cluster import Cluster
from ctac.cover.cfg.materialize import (
    MaterializeError,
    materialize_cluster,
)
from ctac.ir.models import NBId

if TYPE_CHECKING:
    # ClusterState lives in run.py; forward-reference to avoid an
    # import cycle (absorb is imported from run).
    from ctac.cover.cfg.run import ClusterState


def _short_solve(smt2: Path, *, budget_s: int,
                   z3_bin: Path) -> tuple[str, float, list[str]]:
    """Light z3 invocation used by absorption-probe; mirrors run.py's
    `_solve_one` but local-only (avoids the import cycle)."""
    import subprocess
    import time

    argv = [str(z3_bin), f'-T:{budget_s}', '-st', '-smt2', str(smt2)]
    t0 = time.time()
    proc = subprocess.run(argv, capture_output=True, text=True,
                            timeout=budget_s + 10)
    wall = time.time() - t0
    first = proc.stdout.strip().split('\n', 1)[0] if proc.stdout else ''
    verdict = first if first in ('sat', 'unsat', 'unknown') else 'unknown'
    return verdict, wall, argv


def try_absorb(*,
                 states: 'list[ClusterState]',
                 escape: Sequence[NBId],
                 absorb_threshold: int,
                 absorb_budget_s: int,
                 universe: Sequence[NBId],
                 input_tac: Path,
                 output_dir: Path,
                 ctac_bin: str,
                 z3_bin: Path,
                 ) -> 'ClusterState | None':
    """Try to absorb `escape` into the nearest cluster.

    Returns the (possibly updated) `ClusterState` if absorption ran
    to a definitive verdict:
    - `.verdict == 'unsat'`: cluster was widened in place; caller
      should treat the cover as still consistent and continue.
    - `.verdict == 'sat'`: first-SAT-wins; caller should exit.

    Returns None if no cluster was close enough to attempt absorption,
    or if the widened solve was unknown/timeout — in that case the
    caller falls through to singleton+core."""
    if not states:
        return None
    escape_set = frozenset(escape)

    # Find the closest cluster by |π \ K_j|.
    best_j = None
    best_diff: int | None = None
    for j, st in enumerate(states):
        diff = len(escape_set - st.cluster.keep_union)
        if best_diff is None or diff < best_diff:
            best_diff = diff
            best_j = j
    if best_j is None or best_diff is None or best_diff > absorb_threshold:
        return None

    target_state = states[best_j]
    widened_keep = target_state.cluster.keep_union | escape_set

    # Materialize the widened cluster in a fresh dir (don't overwrite
    # the original cluster dir until we know the widened verdict).
    widened_dir = output_dir / f'{target_state.cluster.id}_widen'
    try:
        widened_arts = materialize_cluster(
            input_tac=input_tac,
            cluster_dir=widened_dir,
            keep=widened_keep,
            universe=universe,
            ctac_bin=ctac_bin,
        )
    except MaterializeError:
        return None  # caller falls through

    verdict, wall, argv = _short_solve(
        widened_arts.smt2, budget_s=absorb_budget_s, z3_bin=z3_bin)

    if verdict == 'unknown':
        # Widening didn't close; fall through to singleton path.
        return None

    # Definitive verdict — update the cluster in place.
    new_cluster = Cluster(
        id=target_state.cluster.id,
        members=target_state.cluster.members,
        medoid=target_state.cluster.medoid,
        keep_union=frozenset(widened_keep),
    )
    target_state.cluster = new_cluster
    target_state.artifacts = widened_arts
    target_state.verdict = verdict
    target_state.wall_s = wall
    target_state.z3_argv = tuple(argv)
    return target_state
