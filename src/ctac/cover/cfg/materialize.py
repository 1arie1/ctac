"""Materialize one cluster: pin → rw → smt → smt2 on disk.

Each cluster's keep-set determines a `ctac pin --drop` argument list
(the *complement* of the keep against the entry-to-assert universe).
We shell out to the ctac CLI for pin / rw / smt: each step is a
well-tested standalone command, and the cover doesn't need to track
internal API churn across rewrite / encoding phases.

Output layout under `<cluster_dir>/`:

```
cluster_<i>/
  pinned.tac         # ctac pin --drop ...
  pinned.rw.tac      # ctac rw
  v.smt2             # ctac smt --encoding sea --cfg-encoding fwd-edg
                     #          --guard-statics [--unsat-core]
  pin.cmd            # ready-to-run pin command
  rw.cmd             # ready-to-run rw command
  smt.cmd            # ready-to-run smt command
```

The `.cmd` text files are part of the reproducibility contract — a
user (or future agent) can re-derive the cluster's artifacts from
the original TAC + the cluster's drop set.
"""
from __future__ import annotations

import shlex
import subprocess
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

from ctac.ir.models import NBId


# Default rw is intentionally bare. `--interval-select` is path-sensitive:
# it specializes Selects using upstream range info, which makes a block's
# encoded content depend on the path through it. The cover's unsat-core
# block-projection forbid mechanism requires block content to be
# path-stable (so a core extracted from path π_1 transfers to any path
# π_2 containing π_1's core blocks). Path-stable encoding ⇒ sound forbids.
# Cost: ~12% wall-time hit on the bad_ua_rw sample. Tradeoff accepted.
DEFAULT_RW_FLAGS = ()
# `--inline-scalars` is path-sensitive in the same way `--interval-select`
# is: a static def in a path-specific block may be inlined into uses,
# changing the named-assert content at the use site between paths.
# Cores extracted from one path's smt2 then don't transfer cleanly.
# Off by default; the cover's UNSAT verdict relies on the core
# forbid mechanism being sound across paths.
DEFAULT_SMT_FLAGS = (
    '--encoding', 'sea',
    '--cfg-encoding', 'fwd-edg',
    # `--guard-statics` is REQUIRED for soundness here. Without it,
    # sea_vc emits each block's static defs as bare top-level
    # equalities — they fire even when the defining block isn't on
    # the chosen path. On the full VC this can over-constrain
    # (forcing a register to a value from an unreached block) and
    # turn a real-SAT instance into spurious UNSAT. The cover's
    # pipeline relies on cluster verdicts and the baseline smt2
    # being faithful to the original TAC's semantics; guarded
    # statics restore that. Confirmed on lopu (2026-05-17):
    # without the flag, the full rw'd TAC's smt2 returns UNSAT
    # despite an existing assertion-failing model; with it, SAT.
    '--guard-statics',
)


@dataclass(frozen=True)
class ClusterArtifacts:
    """Files produced by `materialize_cluster` for one cluster.

    `trail` is the rw-trail JSON sidecar — maps havoc'd variables back
    to expressions over surviving ones, so `ctac run --model` can
    resolve SAT-model values for rewritten variables when replaying."""

    cluster_dir: Path
    pinned_tac: Path
    rw_tac: Path
    smt2: Path
    drops: tuple[NBId, ...]
    keep: tuple[NBId, ...]
    trail: Path | None = None


class MaterializeError(RuntimeError):
    """A pin / rw / smt invocation failed; stderr is on the exception."""

    def __init__(self, step: str, argv: list[str], stderr: str) -> None:
        super().__init__(
            f'{step} failed: {" ".join(shlex.quote(a) for a in argv)}\n'
            f'stderr:\n{stderr}')
        self.step = step
        self.argv = argv
        self.stderr = stderr


def _drops_from_keep(keep: Iterable[NBId],
                       universe: Iterable[NBId]) -> list[NBId]:
    """Complement: blocks in universe but NOT in keep."""
    return sorted(set(universe) - set(keep))


def materialize_cluster(*,
                          input_tac: Path,
                          cluster_dir: Path,
                          keep: Iterable[NBId],
                          universe: Iterable[NBId],
                          ctac_bin: str = 'ctac',
                          rw_flags: Iterable[str] = DEFAULT_RW_FLAGS,
                          smt_flags: Iterable[str] = DEFAULT_SMT_FLAGS,
                          unsat_core: bool = False,
                          ) -> ClusterArtifacts:
    """Pin / rw / smt one cluster.

    `keep` defines the cluster (blocks we *retain*). `universe` is the
    block set the cover operates over (typically
    `blocks_on_entry_to_assert_paths(info)`). The drop set is
    `universe \\ keep` and is passed to `ctac pin --drop`.

    On any subprocess failure, raises `MaterializeError` with the
    failing step's stderr; the caller decides whether to skip the
    cluster, log, or abort the cover."""
    cluster_dir.mkdir(parents=True, exist_ok=True)
    drops = _drops_from_keep(keep, universe)
    keep_t = tuple(sorted(set(keep)))

    pinned_tac = cluster_dir / 'pinned.tac'
    rw_tac = cluster_dir / 'pinned.rw.tac'
    rw_trail = cluster_dir / 'pinned.rw.trail.json'
    smt2 = cluster_dir / 'v.smt2'

    # 1. pin --drop
    pin_argv = [ctac_bin, 'pin', str(input_tac),
                 '-o', str(pinned_tac), '--plain']
    if drops:
        pin_argv += ['--drop', ','.join(drops)]
    _run(pin_argv, step='pin', cmd_file=cluster_dir / 'pin.cmd')

    # 2. rw + trail (the trail maps havoc'd variables back to
    # expressions over surviving ones; `ctac run --model` needs it
    # to resolve SAT model values when replaying against INPUT_TAC).
    rw_argv = [ctac_bin, 'rw', str(pinned_tac),
                '-o', str(rw_tac), '--plain',
                '--trail', str(rw_trail)]
    rw_argv += list(rw_flags)
    _run(rw_argv, step='rw', cmd_file=cluster_dir / 'rw.cmd')

    # 3. smt
    smt_argv = [ctac_bin, 'smt', str(rw_tac),
                  '-o', str(smt2), '--plain']
    smt_argv += list(smt_flags)
    if unsat_core:
        smt_argv += ['--unsat-core']
    _run(smt_argv, step='smt', cmd_file=cluster_dir / 'smt.cmd')

    return ClusterArtifacts(
        cluster_dir=cluster_dir,
        pinned_tac=pinned_tac,
        rw_tac=rw_tac,
        trail=rw_trail if rw_trail.exists() else None,
        smt2=smt2,
        drops=tuple(drops),
        keep=keep_t,
    )


def _run(argv: list[str], *, step: str, cmd_file: Path) -> None:
    cmd_file.write_text(' '.join(shlex.quote(a) for a in argv) + '\n')
    proc = subprocess.run(argv, capture_output=True, text=True)
    if proc.returncode != 0:
        raise MaterializeError(step, argv, proc.stderr)
