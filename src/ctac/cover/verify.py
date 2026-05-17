"""Independent re-verifier for cover certificates.

Loads a `Certificate` JSON file and re-runs every recorded z3
invocation, asserting the verdicts match. Soundness is a property of
this re-verification: if `verify()` returns a passing `VerifyReport`,
the certificate is sound regardless of the cover loop that produced it.

The verifier mirrors `rerun.sh` but is typed (returns a `VerifyReport`)
and integrates cleanly with `ctac verify-cover`. The bash script is
the audit artifact for humans / external CI; the Python API here is
what `ctac verify-cover` uses internally.

Paths recorded in the certificate are taken to be relative to the
certificate file's parent directory; the verifier uses `cwd=cert_dir`
on each subprocess so paths resolve consistently.
"""
from __future__ import annotations

import shlex
import subprocess
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Literal

from ctac.cover.certificate import (
    SatCertificate,
    UnsatCertificate,
    load_certificate,
)
from ctac.solver.z3 import resolve_z3_bin


# ---------------------------------- Report types -----------------------------


@dataclass(frozen=True)
class VerifyCheck:
    """One re-verification step's outcome."""

    label: str
    expected: str
    got: str
    wall_s: float
    passed: bool
    detail: str = ''           # extra diagnostic (truncated stdout / explanation)


@dataclass
class VerifyReport:
    cert_kind: Literal['sat', 'unsat']
    checks: list[VerifyCheck] = field(default_factory=list)

    @property
    def passed(self) -> bool:
        return all(c.passed for c in self.checks)

    def summary(self) -> str:
        ok = sum(1 for c in self.checks if c.passed)
        return f'{ok}/{len(self.checks)} checks passed'


# ------------------------------- subprocess helper ---------------------------


def _resolve_argv(recorded: tuple[str, ...], z3_bin: Path | None) -> list[str]:
    """Honor a `--z3` override by substituting argv[0]."""
    a = list(recorded)
    if z3_bin and a:
        a[0] = str(z3_bin)
    return a


def _parse_first_line_verdict(stdout: str) -> str:
    """Match the awk pattern in rerun.sh: first non-empty stdout line."""
    for line in stdout.splitlines():
        line = line.strip()
        if line:
            return line
    return ''


@dataclass(frozen=True)
class _RunResult:
    verdict: str
    wall_s: float
    stdout: str
    stderr: str


def _run(argv: list[str], *, cwd: Path, timeout_s: int) -> _RunResult:
    """Subprocess wrapper that returns a typed `_RunResult`."""
    t0 = time.time()
    try:
        proc = subprocess.run(argv, capture_output=True, text=True,
                                cwd=cwd, timeout=timeout_s + 10)
    except subprocess.TimeoutExpired as e:
        return _RunResult(verdict='timeout', wall_s=time.time() - t0,
                           stdout=(e.stdout.decode() if isinstance(e.stdout, bytes)
                                    else (e.stdout or '')),
                           stderr=(e.stderr.decode() if isinstance(e.stderr, bytes)
                                    else (e.stderr or '')))
    wall_s = time.time() - t0
    verdict = _parse_first_line_verdict(proc.stdout)
    return _RunResult(verdict=verdict, wall_s=wall_s,
                       stdout=proc.stdout, stderr=proc.stderr)


# --------------------------------- Verify SAT --------------------------------


def verify_sat(cert: SatCertificate, *,
                cert_dir: Path,
                z3_bin: Path | None = None,
                timeout_s: int = 300,
                ctac_bin: str = 'ctac') -> VerifyReport:
    """Re-verify a SAT certificate.

    Two checks:
    1. Re-solve `sat_smt2` with the recorded argv; expect `sat`.
    2. Run `ctac run <tac> --model <model> --validate` and confirm
       the model triggers `assert_fail=1`.

    For (2), the certificate's `program_replay.model_text_path` must
    exist on disk relative to `cert_dir` — the cover is responsible
    for writing the model file when it emits the certificate."""
    report = VerifyReport(cert_kind='sat')

    # Check 1: SAT confirm
    argv = _resolve_argv(cert.z3_invocation, z3_bin)
    res = _run(argv, cwd=cert_dir, timeout_s=timeout_s)
    report.checks.append(VerifyCheck(
        label=f'z3 SAT confirm: {cert.sat_smt2}',
        expected='sat',
        got=res.verdict,
        wall_s=res.wall_s,
        passed=(res.verdict == 'sat'),
        detail=_short(res.stdout, res.stderr),
    ))

    # Check 2: program replay (ctac run --validate)
    replay = cert.program_replay
    replay_argv = [ctac_bin, 'run', replay.tac_path,
                    '--model', replay.model_text_path]
    replay_argv += list(replay.ctac_run_args)
    if '--plain' not in replay_argv:
        replay_argv.append('--plain')
    res = _run(replay_argv, cwd=cert_dir, timeout_s=timeout_s)
    # Look for "assert_fail: 1" (or "assert_fail    : 1") in stdout.
    got_assert_fail = _ctac_run_asserts_failed(res.stdout)
    report.checks.append(VerifyCheck(
        label=f'program replay: {replay.tac_path}',
        expected='assert_fail=1',
        got=f'assert_fail={got_assert_fail}',
        wall_s=res.wall_s,
        passed=(got_assert_fail >= 1),
        detail=_short(res.stdout, res.stderr),
    ))
    return report


def _ctac_run_asserts_failed(stdout: str) -> int:
    """Parse `assert_fail: N` from `ctac run --validate --plain` output."""
    for line in stdout.splitlines():
        s = line.strip()
        if s.startswith('assert_fail'):
            # match "assert_fail: 1" or "assert_fail    : 1"
            parts = s.split(':', 1)
            if len(parts) == 2:
                tail = parts[1].strip()
                try:
                    return int(tail.split()[0])
                except (ValueError, IndexError):
                    continue
    return 0


# --------------------------------- Verify UNSAT ------------------------------


def verify_unsat(cert: UnsatCertificate, *,
                  cert_dir: Path,
                  z3_bin: Path | None = None,
                  timeout_s: int = 300) -> VerifyReport:
    """Re-verify an UNSAT certificate.

    For each `SubProof`: re-solve and confirm `unsat`. Then re-solve
    the completeness probe and confirm `unsat`. All checks must pass."""
    report = VerifyReport(cert_kind='unsat')

    for sp in cert.sub_proofs:
        argv = _resolve_argv(sp.z3_invocation, z3_bin)
        res = _run(argv, cwd=cert_dir, timeout_s=timeout_s)
        report.checks.append(VerifyCheck(
            label=f'sub {sp.sub_id}: {sp.smt2}',
            expected='unsat',
            got=res.verdict,
            wall_s=res.wall_s,
            passed=(res.verdict == 'unsat'),
            detail=_short(res.stdout, res.stderr),
        ))

    probe = cert.completeness_proof
    argv = _resolve_argv(probe.z3_invocation, z3_bin)
    res = _run(argv, cwd=cert_dir, timeout_s=timeout_s)
    report.checks.append(VerifyCheck(
        label=f'completeness probe: {probe.probe_smt2}',
        expected='unsat',
        got=res.verdict,
        wall_s=res.wall_s,
        passed=(res.verdict == 'unsat'),
        detail=_short(res.stdout, res.stderr),
    ))
    return report


# --------------------------------- Top-level verify --------------------------


def verify(cert_path: Path | str, *,
            z3_bin: Path | str | None = None,
            timeout_s: int = 300,
            ctac_bin: str = 'ctac') -> VerifyReport:
    """Load a certificate from disk and re-verify it.

    Returns a `VerifyReport` carrying one check per recorded run.
    `report.passed` is True iff every check passed. Callers (the CLI,
    test harnesses) decide what to print and what exit code to use."""
    p = Path(cert_path)
    cert = load_certificate(p)
    z3 = resolve_z3_bin(z3_bin) if z3_bin else None
    cert_dir = p.parent if p.parent != Path('') else Path.cwd()
    if cert.kind == 'sat':
        return verify_sat(cert, cert_dir=cert_dir, z3_bin=z3,
                           timeout_s=timeout_s, ctac_bin=ctac_bin)
    return verify_unsat(cert, cert_dir=cert_dir, z3_bin=z3,
                         timeout_s=timeout_s)


def _short(stdout: str, stderr: str, *, maxlen: int = 200) -> str:
    """Build a one-shot diagnostic blob (truncated) for failed checks."""
    tail = (stdout or stderr or '').strip().splitlines()
    if not tail:
        return ''
    last = tail[-1][:maxlen]
    return f'stdout-tail: {last!r}'


def fmt_argv(argv: tuple[str, ...] | list[str]) -> str:
    """Shell-quote an argv for diagnostic display."""
    return ' '.join(shlex.quote(a) for a in argv)


__all__ = [
    'VerifyCheck', 'VerifyReport',
    'verify', 'verify_sat', 'verify_unsat', 'fmt_argv',
]
