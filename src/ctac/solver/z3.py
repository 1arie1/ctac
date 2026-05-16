"""Low-level z3 invocation.

One-shot solve API for when you just need a verdict + final stats.
For streaming progress observation see `ctac.solver.runner`.

Z3 binary resolution order:
  1. explicit `z3_bin` argument
  2. CTAC_Z3 environment variable
  3. `z3` on PATH
"""
from __future__ import annotations

import os
import re
import shutil
import subprocess
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Literal, Sequence


def resolve_z3_bin(explicit: Path | str | None = None) -> Path:
    """Resolve which z3 binary to use, by precedence."""
    if explicit:
        p = Path(explicit)
        if not p.exists():
            raise FileNotFoundError(f'z3 binary not found: {p}')
        return p
    env = os.environ.get('CTAC_Z3')
    if env:
        p = Path(env)
        if not p.exists():
            raise FileNotFoundError(f'CTAC_Z3={env!r} but file does not exist')
        return p
    on_path = shutil.which('z3')
    if on_path:
        return Path(on_path)
    raise FileNotFoundError(
        'no z3 found; pass --z3 PATH, set CTAC_Z3, or put z3 on PATH')


@dataclass
class Z3Result:
    """Result of a one-shot z3 invocation."""
    verdict: Literal['sat', 'unsat', 'unknown', 'timeout', 'error']
    wall_s: float
    stats: dict[str, float]           # parsed -st block
    model: dict[str, str] | None      # parsed (get-value) responses
    unsat_core: list[str] | None      # parsed (get-unsat-core) response
    stdout: str
    stderr: str
    argv: list[str]                   # exact command for rerun

    @property
    def rerun_command(self) -> str:
        """Shell command line to reproduce this invocation."""
        import shlex
        return ' '.join(shlex.quote(a) for a in self.argv)


_FINAL_STATS_RE = re.compile(r':([a-zA-Z][-a-zA-Z0-9_.:]*)\s+([-+0-9.eE]+)')


def parse_final_stats(stdout: str) -> dict[str, float]:
    """Parse the `(:k v :k v ...)` block z3 emits with `-st`."""
    out: dict[str, float] = {}
    start = stdout.find('(:')
    if start < 0:
        return out
    depth = 0
    end = start
    for i in range(start, len(stdout)):
        c = stdout[i]
        if c == '(':
            depth += 1
        elif c == ')':
            depth -= 1
            if depth == 0:
                end = i + 1
                break
    block = stdout[start:end]
    for m in _FINAL_STATS_RE.finditer(block):
        try:
            v = float(m.group(2))
        except ValueError:
            continue
        out[m.group(1)] = v
    return out


def _parse_verdict(stdout: str, stderr: str, returncode: int) -> str:
    first_line = stdout.strip().split('\n', 1)[0] if stdout else ''
    if first_line == 'sat':
        return 'sat'
    if first_line == 'unsat':
        return 'unsat'
    if 'timeout' in stdout or returncode in (-9, 137):
        return 'timeout'
    if 'unknown' in first_line:
        return 'unknown'
    if returncode != 0:
        return 'error'
    return 'unknown'


def solve(smt2: Path | str, *,
           timeout_s: int,
           seed: int = 0,
           tactic: str | None = None,
           extra_args: Sequence[str] = (),
           z3_bin: Path | str | None = None,
           ) -> Z3Result:
    """One-shot z3 solve. Captures stdout + stderr, parses final stats.

    For streaming progress + signature inference, use `Z3Runner` instead.
    """
    z3 = resolve_z3_bin(z3_bin)
    argv = [str(z3), f'-T:{timeout_s}', '-st', '-smt2', str(smt2),
             f'smt.random_seed={seed}', f'sat.random_seed={seed}']
    if tactic is not None:
        argv += [f'tactic.default_tactic={tactic}']
    argv += list(extra_args)

    t0 = time.time()
    proc = subprocess.run(argv, capture_output=True, text=True,
                           timeout=timeout_s + 10)
    wall_s = time.time() - t0
    stdout = proc.stdout
    stderr = proc.stderr
    verdict = _parse_verdict(stdout, stderr, proc.returncode)
    return Z3Result(
        verdict=verdict, wall_s=wall_s,
        stats=parse_final_stats(stdout),
        model=None, unsat_core=None,
        stdout=stdout, stderr=stderr, argv=argv,
    )
