"""Independent re-verifier for cover certificates (v2 audit chain).

Loads a `Certificate` JSON file and re-derives every cluster's smt2
from `metadata.input_tac` (via `ctac pin --drop`, then `rw`, then
`smt`), then re-solves with z3. For SAT, replays the model against
INPUT_TAC. Catches bugs anywhere in pin / rw / smt / z3.

Soundness is a property of this re-verification: if `verify()`
returns a passing `VerifyReport`, the certificate is sound regardless
of any bugs in the cover loop that produced it.

The verifier and `rerun.sh` audit the same chain; the bash script is
the artifact-for-humans, the Python here is the structured-result
artifact for testing + CI integration.

Paths recorded in the certificate are taken to be relative to the
certificate file's parent directory; `metadata.input_tac` is absolute.
The verifier uses `cwd=cert_dir` so relative paths resolve.
"""
from __future__ import annotations

import shlex
import subprocess
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Literal

from ctac.cover.certificate import (
    CoverMetadata,
    PartialResult,
    SatCertificate,
    UnsatCertificate,
    load_certificate,
)
from ctac.solver.z3 import resolve_z3_bin


# ---------------------------------- Report types -----------------------------


@dataclass(frozen=True)
class VerifyCheck:
    """One re-verification step's outcome.

    `kind` distinguishes re-derivation steps (pin/rw/smt) from
    verdict checks (z3 / replay) so the report can format them
    separately."""

    label: str
    expected: str
    got: str
    wall_s: float
    passed: bool
    kind: Literal['rederive', 'verdict', 'replay', 'warn'] = 'verdict'
    detail: str = ''


@dataclass
class VerifyReport:
    cert_kind: Literal['sat', 'unsat', 'partial']
    checks: list[VerifyCheck] = field(default_factory=list)
    warnings: list[str] = field(default_factory=list)

    @property
    def passed(self) -> bool:
        return all(c.passed for c in self.checks)

    def summary(self) -> str:
        ok = sum(1 for c in self.checks if c.passed)
        return f'{ok}/{len(self.checks)} checks passed'


# ------------------------------- subprocess helper ---------------------------


@dataclass(frozen=True)
class _RunResult:
    rc: int
    wall_s: float
    stdout: str
    stderr: str

    @property
    def first_line(self) -> str:
        for line in self.stdout.splitlines():
            line = line.strip()
            if line:
                return line
        return ''


def _run(argv: list[str], *, cwd: Path,
          timeout_s: int) -> _RunResult:
    t0 = time.time()
    try:
        proc = subprocess.run(argv, capture_output=True, text=True,
                                cwd=cwd, timeout=timeout_s + 10)
    except subprocess.TimeoutExpired as e:
        return _RunResult(
            rc=-1, wall_s=time.time() - t0,
            stdout=(e.stdout.decode() if isinstance(e.stdout, bytes)
                     else (e.stdout or '')),
            stderr=(e.stderr.decode() if isinstance(e.stderr, bytes)
                     else (e.stderr or '')))
    return _RunResult(
        rc=proc.returncode, wall_s=time.time() - t0,
        stdout=proc.stdout, stderr=proc.stderr)


def _z3_budget(recorded_wall_s: float, *,
                 multiplier: float = 2.0,
                 slack_s: float = 5.0,
                 minimum_s: int = 10) -> int:
    """Per-z3-invocation timeout derived from the cover's recorded
    wall time. If the cover claims a cluster solved in 2.5s, the
    audit budget should be ~10s (2.5 * 2 + 5). If the audit can't
    reproduce within that, the recording is suspect — either bug
    or environmental drift worth flagging.

    Clamped below by `minimum_s` so a 0.01s recording doesn't get a
    1s budget (z3 startup overhead alone can be hundreds of ms)."""
    return max(int(recorded_wall_s * multiplier + slack_s + 0.999),
                minimum_s)


# -------------------------- z3 version comparison ----------------------------


def _check_z3_version(meta: CoverMetadata,
                       z3_bin: Path) -> str | None:
    """Run `z3 --version` and compare to the recorded version.

    Returns a warning string on mismatch, or None on match / no
    recorded version. Never fails the audit — version drift is a
    soft signal."""
    if not meta.z3_version:
        return None
    try:
        proc = subprocess.run(
            [str(z3_bin), '--version'],
            capture_output=True, text=True, timeout=10)
    except (subprocess.SubprocessError, OSError):
        return f'could not run `{z3_bin} --version`'
    got = proc.stdout.strip().split('\n', 1)[0]
    if got != meta.z3_version:
        return (f'z3 version mismatch: recorded `{meta.z3_version}`, '
                  f'current `{got}`')
    return None


# --------------------------- pin / rw / smt re-derive ------------------------


def _rederive_cluster(cert_dir: Path, *,
                        sub_dir: str,
                        drops: tuple[str, ...],
                        meta: CoverMetadata,
                        ctac_bin: str,
                        timeout_s: int,
                        report: VerifyReport) -> bool:
    """Re-run pin / rw / smt for one cluster.

    Writes to `cert_dir/<sub_dir>/pinned.tac`, `pinned.rw.tac`,
    `v.smt2` (overwriting any prior contents). Returns True on
    success, False if any step failed (and appends a failing
    `VerifyCheck` to `report.checks`)."""
    sub = cert_dir / sub_dir
    sub.mkdir(parents=True, exist_ok=True)
    drop_args = ['--drop', ','.join(drops)] if drops else []

    pin_argv = [ctac_bin, 'pin', meta.input_tac,
                 '-o', str(sub / 'pinned.tac'), '--plain', *drop_args]
    res = _run(pin_argv, cwd=cert_dir, timeout_s=timeout_s)
    if res.rc != 0:
        report.checks.append(VerifyCheck(
            label=f'pin {sub_dir}', expected='ok', got=f'rc={res.rc}',
            wall_s=res.wall_s, passed=False, kind='rederive',
            detail=_short(res.stdout, res.stderr)))
        return False

    rw_argv = [ctac_bin, 'rw', str(sub / 'pinned.tac'),
                '-o', str(sub / 'pinned.rw.tac'), '--plain',
                *meta.rw_flags]
    res = _run(rw_argv, cwd=cert_dir, timeout_s=timeout_s)
    if res.rc != 0:
        report.checks.append(VerifyCheck(
            label=f'rw {sub_dir}', expected='ok', got=f'rc={res.rc}',
            wall_s=res.wall_s, passed=False, kind='rederive',
            detail=_short(res.stdout, res.stderr)))
        return False

    smt_argv = [ctac_bin, 'smt', str(sub / 'pinned.rw.tac'),
                  '-o', str(sub / 'v.smt2'), '--plain',
                  *meta.smt_flags]
    res = _run(smt_argv, cwd=cert_dir, timeout_s=timeout_s)
    if res.rc != 0:
        report.checks.append(VerifyCheck(
            label=f'smt {sub_dir}', expected='ok', got=f'rc={res.rc}',
            wall_s=res.wall_s, passed=False, kind='rederive',
            detail=_short(res.stdout, res.stderr)))
        return False

    return True


# --------------------------------- Verify SAT --------------------------------


def verify_sat(cert: SatCertificate, *,
                cert_dir: Path,
                z3_bin: Path | None = None,
                rederive_timeout_s: int = 60,
                timeout_multiplier: float = 2.0,
                timeout_slack_s: float = 5.0,
                ctac_bin: str = 'ctac',
                strict_validation: bool = False) -> VerifyReport:
    """Re-verify a SAT certificate via full re-derivation.

    Steps:
    1. Re-derive the winner cluster: pin/rw/smt from INPUT_TAC with
       `winner_drops`.
    2. Solve the re-derived smt2; expect `sat`.
    3. Replay the captured model against INPUT_TAC with `ctac run
       --validate`; expect `assert_fail >= 1`. With
       `strict_validation`, additionally require zero havoc fallbacks
       (i.e. the model fully determines execution)."""
    report = VerifyReport(cert_kind='sat')
    z3 = z3_bin or resolve_z3_bin(cert.metadata.z3_bin or None)

    if (w := _check_z3_version(cert.metadata, z3)):
        report.warnings.append(w)

    winner_id = cert.witness_cluster or 'winner'
    ok = _rederive_cluster(cert_dir,
                             sub_dir=winner_id,
                             drops=cert.winner_drops,
                             meta=cert.metadata,
                             ctac_bin=ctac_bin,
                             timeout_s=rederive_timeout_s,
                             report=report)
    if not ok:
        return report

    # Per-z3 budget derived from recorded wall_s.
    z3_budget = _z3_budget(cert.wall_s,
                             multiplier=timeout_multiplier,
                             slack_s=timeout_slack_s)

    # Solve the re-derived smt2.
    re_smt2 = cert_dir / winner_id / 'v.smt2'
    argv = [str(z3), f'-T:{z3_budget}', '-smt2', str(re_smt2),
             *cert.z3_args]
    res = _run(argv, cwd=cert_dir, timeout_s=z3_budget)
    report.checks.append(VerifyCheck(
        label=f'z3 SAT confirm: {winner_id}/v.smt2',
        expected='sat', got=res.first_line, wall_s=res.wall_s,
        passed=(res.first_line == 'sat'), kind='verdict',
        detail=_short(res.stdout, res.stderr)))
    if res.first_line != 'sat':
        return report

    # Capture model + replay against INPUT_TAC.
    argv_model = [str(z3), f'-T:{z3_budget}', '-smt2', str(re_smt2),
                    *cert.z3_args, '-model']
    res_m = _run(argv_model, cwd=cert_dir, timeout_s=z3_budget)
    model_path = cert_dir / winner_id / 'model.smt'
    model_path.write_text(res_m.stdout)

    replay = cert.program_replay
    replay_argv = [ctac_bin, 'run', replay.tac_path,
                    '--model', str(model_path.relative_to(cert_dir)),
                    *replay.ctac_run_args]
    if '--plain' not in replay_argv:
        replay_argv.append('--plain')
    res_r = _run(replay_argv, cwd=cert_dir, timeout_s=rederive_timeout_s)
    asserts_failed, havoc_hits = _parse_ctac_run_result(res_r.stdout)
    if strict_validation:
        passed = asserts_failed >= 1 and havoc_hits == 0
        got = f'assert_fail={asserts_failed} havoc={havoc_hits}'
        expected = 'assert_fail>=1 havoc=0'
    else:
        passed = asserts_failed >= 1
        got = f'assert_fail={asserts_failed}'
        expected = 'assert_fail>=1'
    report.checks.append(VerifyCheck(
        label=f'program replay: {replay.tac_path}',
        expected=expected, got=got, wall_s=res_r.wall_s,
        passed=passed, kind='replay',
        detail=_short(res_r.stdout, res_r.stderr)))
    return report


def _parse_ctac_run_result(stdout: str) -> tuple[int, int]:
    """Parse `assert_fail: N` and `model havoc: hits=M` from
    `ctac run --validate --plain` output. Returns (asserts, havoc)."""
    asserts = 0
    havoc = 0
    for line in stdout.splitlines():
        s = line.strip()
        if s.startswith('assert_fail'):
            parts = s.split(':', 1)
            if len(parts) == 2:
                tail = parts[1].strip()
                try:
                    asserts = int(tail.split()[0])
                except (ValueError, IndexError):
                    pass
        elif 'havoc' in s and 'hits=' in s:
            m_idx = s.find('hits=')
            try:
                havoc = int(s[m_idx + len('hits='):].split()[0])
            except (ValueError, IndexError):
                pass
    return asserts, havoc


# --------------------------------- Verify UNSAT ------------------------------


def verify_unsat(cert: UnsatCertificate, *,
                  cert_dir: Path,
                  z3_bin: Path | None = None,
                  rederive_timeout_s: int = 60,
                  timeout_multiplier: float = 2.0,
                  timeout_slack_s: float = 5.0,
                  ctac_bin: str = 'ctac') -> VerifyReport:
    """Re-verify an UNSAT certificate via full re-derivation.

    For each `SubProof`: re-derive pin/rw/smt + re-solve; expect
    `unsat`. Then re-solve the completeness probe (recorded smt2 used
    as-is — the probe emitter is pure Python and re-emitting wouldn't
    catch its own bugs)."""
    report = VerifyReport(cert_kind='unsat')
    z3 = z3_bin or resolve_z3_bin(cert.metadata.z3_bin or None)

    if (w := _check_z3_version(cert.metadata, z3)):
        report.warnings.append(w)

    for sp in cert.sub_proofs:
        sub_dir = Path(sp.smt2).parent.as_posix() or sp.sub_id
        ok = _rederive_cluster(
            cert_dir, sub_dir=sub_dir, drops=sp.drops, meta=cert.metadata,
            ctac_bin=ctac_bin, timeout_s=rederive_timeout_s, report=report)
        if not ok:
            continue
        re_smt2 = cert_dir / sub_dir / 'v.smt2'
        budget = _z3_budget(sp.wall_s,
                              multiplier=timeout_multiplier,
                              slack_s=timeout_slack_s)
        argv = [str(z3), f'-T:{budget}', '-smt2', str(re_smt2),
                 *sp.z3_args]
        res = _run(argv, cwd=cert_dir, timeout_s=budget)
        report.checks.append(VerifyCheck(
            label=f'sub {sp.sub_id}: {sp.smt2} (recorded {sp.wall_s:.2f}s, '
                    f'budget {budget}s)',
            expected='unsat', got=res.first_line, wall_s=res.wall_s,
            passed=(res.first_line == 'unsat'), kind='verdict',
            detail=_short(res.stdout, res.stderr)))

    probe = cert.completeness_proof
    budget = _z3_budget(probe.wall_s,
                          multiplier=timeout_multiplier,
                          slack_s=timeout_slack_s)
    argv = [str(z3), f'-T:{budget}', '-smt2', probe.probe_smt2,
             *probe.z3_args]
    res = _run(argv, cwd=cert_dir, timeout_s=budget)
    report.checks.append(VerifyCheck(
        label=f'completeness probe: {probe.probe_smt2} '
                f'(recorded {probe.wall_s:.2f}s, budget {budget}s)',
        expected='unsat', got=res.first_line, wall_s=res.wall_s,
        passed=(res.first_line == 'unsat'), kind='verdict',
        detail=_short(res.stdout, res.stderr)))
    return report


# --------------------------------- Verify Partial -----------------------------


def verify_partial(cert: PartialResult, *,
                    cert_dir: Path,
                    z3_bin: Path | None = None,
                    rederive_timeout_s: int = 60,
                    timeout_multiplier: float = 2.0,
                    timeout_slack_s: float = 5.0,
                    ctac_bin: str = 'ctac') -> VerifyReport:
    """Re-verify the CLOSED parts of a partial result.

    Partial is by definition not sound — `report.passed` is always
    False (we mark the top-level verdict as a failed check). But the
    closed sub-proofs (UNSAT clusters) and the probe (if it ran) are
    re-derived/re-solved like a normal cert, so the user can confirm
    those parts haven't regressed."""
    report = VerifyReport(cert_kind='partial')
    z3 = z3_bin or resolve_z3_bin(cert.metadata.z3_bin or None)

    if (w := _check_z3_version(cert.metadata, z3)):
        report.warnings.append(w)

    # Top-level partial marker — always counts as a failed verdict.
    report.checks.append(VerifyCheck(
        label=f'partial verdict: {cert.verdict}',
        expected='sat|unsat',
        got=cert.verdict,
        wall_s=0.0,
        passed=False,
        kind='warn',
        detail=(f'clusters_need_closure={cert.clusters_need_closure} '
                  f'probe_needs_closure={cert.probe_needs_closure} '
                  f'cover_is_incomplete={cert.cover_is_incomplete}'),
    ))

    # Re-verify closed sub-proofs the same way verify_unsat does.
    for sp in cert.closed_sub_proofs:
        sub_dir = Path(sp.smt2).parent.as_posix() or sp.sub_id
        ok = _rederive_cluster(
            cert_dir, sub_dir=sub_dir, drops=sp.drops, meta=cert.metadata,
            ctac_bin=ctac_bin, timeout_s=rederive_timeout_s, report=report)
        if not ok:
            continue
        re_smt2 = cert_dir / sub_dir / 'v.smt2'
        budget = _z3_budget(sp.wall_s,
                              multiplier=timeout_multiplier,
                              slack_s=timeout_slack_s)
        argv = [str(z3), f'-T:{budget}', '-smt2', str(re_smt2),
                 *sp.z3_args]
        res = _run(argv, cwd=cert_dir, timeout_s=budget)
        report.checks.append(VerifyCheck(
            label=f'closed sub {sp.sub_id}: {sp.smt2} '
                    f'(recorded {sp.wall_s:.2f}s, budget {budget}s)',
            expected='unsat', got=res.first_line, wall_s=res.wall_s,
            passed=(res.first_line == 'unsat'), kind='verdict',
            detail=_short(res.stdout, res.stderr)))

    # Probe (if recorded): re-solve and confirm verdict matches.
    if cert.probe_outcome is not None:
        probe = cert.probe_outcome
        budget = _z3_budget(probe.wall_s,
                              multiplier=timeout_multiplier,
                              slack_s=timeout_slack_s)
        argv = [str(z3), f'-T:{budget}', '-smt2', probe.probe_smt2,
                 *probe.z3_args]
        res = _run(argv, cwd=cert_dir, timeout_s=budget)
        # Probe match is informational for partial; pass iff recorded
        # verdict reproduces (so deltas surface).
        report.checks.append(VerifyCheck(
            label=f'probe ({probe.probe_smt2}): '
                    f'recorded={probe.verdict}, budget={budget}s',
            expected=probe.verdict, got=res.first_line, wall_s=res.wall_s,
            passed=(res.first_line == probe.verdict), kind='verdict',
            detail=_short(res.stdout, res.stderr)))

    # Open clusters: surface them without re-running (they were open
    # by definition; re-running would just timeout again).
    open_outcomes = [c for c in cert.cluster_outcomes
                      if c.verdict not in ('sat', 'unsat')]
    for c in open_outcomes:
        report.checks.append(VerifyCheck(
            label=f'open cluster {c.sub_id} (recorded {c.verdict}, '
                    f'{c.wall_s:.2f}s)',
            expected='unsat',
            got=c.verdict,
            wall_s=0.0,
            passed=False,
            kind='warn',
            detail='unresolved; needs more compute or analysis',
        ))
    return report


# --------------------------------- Top-level verify --------------------------


def verify(cert_path: Path | str, *,
            z3_bin: Path | str | None = None,
            rederive_timeout_s: int = 60,
            timeout_multiplier: float = 2.0,
            timeout_slack_s: float = 5.0,
            ctac_bin: str = 'ctac',
            strict_validation: bool = False) -> VerifyReport:
    """Load a certificate from disk and re-verify it.

    Per-z3 timeout is derived from each recorded `wall_s`:
    `max(wall_s * multiplier + slack, 10s)`. The recording is the
    soundness anchor — if z3 needs much more than the cover claimed,
    something is wrong (bug, environmental drift, or a non-reproducible
    cover). `rederive_timeout_s` is a separate budget for pin/rw/smt,
    which the cover doesn't record per step.

    Returns a `VerifyReport` carrying one check per recorded run.
    `report.passed` is True iff every check passed. Callers (the CLI,
    test harnesses) decide what to print and what exit code to use."""
    p = Path(cert_path)
    cert = load_certificate(p)
    z3 = resolve_z3_bin(z3_bin) if z3_bin else None
    cert_dir = p.parent if p.parent != Path('') else Path.cwd()
    if cert.kind == 'sat':
        return verify_sat(cert, cert_dir=cert_dir, z3_bin=z3,
                           rederive_timeout_s=rederive_timeout_s,
                           timeout_multiplier=timeout_multiplier,
                           timeout_slack_s=timeout_slack_s,
                           ctac_bin=ctac_bin,
                           strict_validation=strict_validation)
    if cert.kind == 'unsat':
        return verify_unsat(cert, cert_dir=cert_dir, z3_bin=z3,
                             rederive_timeout_s=rederive_timeout_s,
                             timeout_multiplier=timeout_multiplier,
                             timeout_slack_s=timeout_slack_s,
                             ctac_bin=ctac_bin)
    return verify_partial(cert, cert_dir=cert_dir, z3_bin=z3,
                            rederive_timeout_s=rederive_timeout_s,
                            timeout_multiplier=timeout_multiplier,
                            timeout_slack_s=timeout_slack_s,
                            ctac_bin=ctac_bin)


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
    'verify', 'verify_sat', 'verify_unsat', 'verify_partial', 'fmt_argv',
]
