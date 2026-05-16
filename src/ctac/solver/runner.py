"""Streaming z3 runner with progress observation and abort hooks.

The Z3Runner spawns z3 with `-v:2 -st`, parses stderr line-by-line into
ProgressEvents, groups nlsat-line events into calls by user-validated
heuristic ("conflicts strictly grows + clauses change < 50"), and
optionally aborts early based on AbortPolicy.

After the run, `infer_signature` (in ctac.solver.signature) produces a
DiagnosticSignature with label, confidence (from signal strength), and
runner-up.
"""
from __future__ import annotations

import os
import re
import select
import signal as _signal
import subprocess
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import TYPE_CHECKING, Any, Callable, Sequence

from ctac.solver.z3 import (
    parse_final_stats,
    resolve_z3_bin,
)

if TYPE_CHECKING:
    from ctac.solver.signature import DiagnosticSignature


@dataclass
class ProgressEvent:
    """Single event observed on z3's stderr."""
    wall_s: float
    kind: str
    payload: dict[str, Any] = field(default_factory=dict)


@dataclass
class NlsatCall:
    """Sequence of nlsat lines we believe belong to one call.

    Same call iff `conflicts` strictly grows AND `clauses` changes < 50.
    A 'stuck' call has ≥3 lines with monotonically growing conflicts."""
    started_wall_s: float
    ended_wall_s: float
    lines: list[dict] = field(default_factory=list)

    @property
    def n_lines(self) -> int:
        return len(self.lines)

    @property
    def conflicts(self) -> int:
        return max((ln['conflicts'] for ln in self.lines), default=0)

    @property
    def propagations(self) -> int:
        return sum(ln['propagations'] for ln in self.lines)

    @property
    def is_stuck(self) -> bool:
        if self.n_lines < 3:
            return False
        confs = [ln['conflicts'] for ln in self.lines]
        return max(confs) >= 3 and confs[-1] > confs[0]


_SMT_STATS_DATA_RE = re.compile(
    r'^\(smt\.stats'
    r'\s+(\d+)'                          # restarts
    r'\s+(\d+)'                          # conflicts
    r'\s+(\d+)'                          # decisions
    r'\s+(\d+)'                          # propagations
    r'\s+(\d+)/(\d+)/(\d+)'              # clauses/bin/units
    r'\s+(\d+)/(\d+)'                    # lemmas total/bin
    r'\s+(\d+)'                          # simplify
    r'\s+(\d+)'                          # deletions
    r'\s+([\d.]+)\)$'                    # memory MB
)

_NLSAT_RE = re.compile(
    r'^\(nlsat'
    r'\s+:conflicts\s+(\d+)'
    r'\s+:decisions\s+(\d+)'
    r'\s+:propagations\s+(\d+)'
    r'\s+:clauses\s+(\d+)'
    r'\s+:learned\s+(\d+)\)$'
)

_TACTIC_MARKER_RE = re.compile(r'^\(([\w.-]+)\)$')

_HEADER_RE = re.compile(r'^\(smt\.stats\s+:')


def parse_line(line: str) -> dict | None:
    """Parse one z3 stderr line into a structured dict (or None to ignore).

    Header re-emissions are returned as `{'kind': 'header'}` for
    diagnostic purposes; callers usually filter them out."""
    s = line.strip()
    if not s:
        return None
    if _HEADER_RE.match(s):
        return {'kind': 'header'}
    m = _SMT_STATS_DATA_RE.match(s)
    if m:
        g = m.groups()
        return {
            'kind': 'smt-stats',
            'restarts': int(g[0]),
            'conflicts': int(g[1]),
            'decisions': int(g[2]),
            'propagations': int(g[3]),
            'clauses_total': int(g[4]),
            'clauses_bin': int(g[5]),
            'clauses_units': int(g[6]),
            'lemmas_total': int(g[7]),
            'lemmas_bin': int(g[8]),
            'simplify': int(g[9]),
            'deletions': int(g[10]),
            'memory_mb': float(g[11]),
        }
    m = _NLSAT_RE.match(s)
    if m:
        g = m.groups()
        return {
            'kind': 'nlsat-line',
            'conflicts': int(g[0]),
            'decisions': int(g[1]),
            'propagations': int(g[2]),
            'clauses': int(g[3]),
            'learned': int(g[4]),
        }
    m = _TACTIC_MARKER_RE.match(s)
    if m:
        return {'kind': 'tactic-start', 'tactic': m.group(1)}
    return {'kind': 'unknown', 'raw': s}


def group_nlsat_calls(events: list[ProgressEvent]) -> list[NlsatCall]:
    """Group nlsat-line events into calls."""
    calls: list[NlsatCall] = []
    current: NlsatCall | None = None
    CLAUSES_JUMP = 50
    for e in events:
        if e.kind != 'nlsat-line':
            continue
        ln = e.payload
        if current is None:
            current = NlsatCall(started_wall_s=e.wall_s, ended_wall_s=e.wall_s,
                                 lines=[ln])
            continue
        prev = current.lines[-1]
        conflicts_grew_strict = ln['conflicts'] > prev['conflicts']
        clauses_close = abs(ln['clauses'] - prev['clauses']) < CLAUSES_JUMP
        if conflicts_grew_strict and clauses_close:
            current.lines.append(ln)
            current.ended_wall_s = e.wall_s
        else:
            calls.append(current)
            current = NlsatCall(started_wall_s=e.wall_s, ended_wall_s=e.wall_s,
                                 lines=[ln])
    if current is not None:
        calls.append(current)
    return calls


@dataclass
class AbortPolicy:
    """Heuristic abort hooks. Each fires when its condition holds for the
    configured duration."""
    min_wall_s: float = 2.0
    no_progress_window_s: float | None = None
    nlsat_stuck_window_s: float | None = None
    preprocessing_max_s: float | None = None


def _should_abort(events: list[ProgressEvent], policy: AbortPolicy,
                   wall_s: float) -> tuple[bool, str]:
    if wall_s < policy.min_wall_s:
        return False, ''
    if policy.preprocessing_max_s is not None:
        if not any(e.kind == 'tactic-start' and
                    e.payload.get('tactic') == 'smt.searching'
                    for e in events):
            if wall_s >= policy.preprocessing_max_s:
                return True, 'preprocessing exceeded budget'
    if policy.no_progress_window_s is not None and events:
        last = events[-1]
        if wall_s - last.wall_s >= policy.no_progress_window_s:
            return True, f'no progress for {wall_s - last.wall_s:.1f}s'
    if policy.nlsat_stuck_window_s is not None:
        calls = group_nlsat_calls(events)
        if calls and calls[-1].is_stuck:
            duration = wall_s - calls[-1].started_wall_s
            if duration >= policy.nlsat_stuck_window_s:
                return True, f'nlsat call stuck for {duration:.1f}s'
    return False, ''


@dataclass
class Z3RunResult:
    """Output of Z3Runner.run() — verdict + timeline + signature.

    Distinct from `ctac.solver.z3.Z3Result` (the simple one-shot output);
    this is the richer streaming result."""
    smt2_path: Path
    argv: list[str]
    verdict: str                          # sat | unsat | unknown | timeout | error | aborted
    wall_s: float
    final_stats: dict[str, float]
    timeline: list[ProgressEvent]
    nlsat_calls: list[NlsatCall]
    signature: 'DiagnosticSignature'      # filled in by infer_signature
    early_aborted: bool
    abort_reason: str
    stdout: str
    stderr_lines_count: int

    @property
    def rerun_command(self) -> str:
        import shlex
        return ' '.join(shlex.quote(a) for a in self.argv)


@dataclass
class Z3Runner:
    """Spawns z3, streams stderr, builds timeline, infers signature.

    The runner stays minimal: spawning, parsing, event collection, abort.
    Signature inference is delegated to `ctac.solver.signature.infer_signature`
    so the classifier can evolve independently of the runner.
    """
    smt2: Path
    timeout_s: int = 60
    seed: int = 0
    z3_bin: Path | str | None = None
    extra_args: Sequence[str] = ()
    poll_interval_s: float = 0.2

    def run(self, *,
              abort_policy: AbortPolicy | None = None,
              on_event: Callable[[ProgressEvent], None] | None = None,
              ) -> Z3RunResult:
        from ctac.solver.signature import infer_signature
        z3 = resolve_z3_bin(self.z3_bin)
        argv = [str(z3), f'-T:{self.timeout_s}', '-v:2', '-st',
                 '-smt2', str(self.smt2),
                 f'smt.random_seed={self.seed}',
                 f'sat.random_seed={self.seed}']
        argv += list(self.extra_args)

        timeline: list[ProgressEvent] = []
        stdout_buf: list[str] = []
        stderr_lines = 0
        early_aborted = False
        abort_reason = ''

        t_start = time.time()
        proc = subprocess.Popen(
            argv, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            text=True, bufsize=1, start_new_session=True)

        try:
            while True:
                wall = time.time() - t_start
                ready, _, _ = select.select(
                    [proc.stdout, proc.stderr], [], [], self.poll_interval_s)
                for fd in ready:
                    line = fd.readline()
                    if not line:
                        continue
                    if fd is proc.stdout:
                        stdout_buf.append(line)
                    else:
                        stderr_lines += 1
                        parsed = parse_line(line)
                        if parsed is None or parsed['kind'] == 'header':
                            continue
                        kind = parsed['kind']
                        payload = {k: v for k, v in parsed.items() if k != 'kind'}
                        ev = ProgressEvent(wall_s=wall, kind=kind, payload=payload)
                        timeline.append(ev)
                        if on_event:
                            on_event(ev)
                if proc.poll() is not None:
                    # Drain remaining
                    for line in proc.stdout:
                        stdout_buf.append(line)
                    for line in proc.stderr:
                        stderr_lines += 1
                        parsed = parse_line(line)
                        if parsed is None or parsed['kind'] == 'header':
                            continue
                        kind = parsed['kind']
                        payload = {k: v for k, v in parsed.items() if k != 'kind'}
                        ev = ProgressEvent(wall_s=time.time() - t_start,
                                           kind=kind, payload=payload)
                        timeline.append(ev)
                    break
                if abort_policy is not None:
                    should, reason = _should_abort(timeline, abort_policy, wall)
                    if should:
                        early_aborted = True
                        abort_reason = reason
                        try:
                            os.killpg(os.getpgid(proc.pid), _signal.SIGKILL)
                        except (ProcessLookupError, PermissionError):
                            pass
                        proc.wait(timeout=5)
                        break
                # Safety: if z3's own -T didn't fire, our hard cap
                if wall > self.timeout_s + 10:
                    try:
                        os.killpg(os.getpgid(proc.pid), _signal.SIGKILL)
                    except (ProcessLookupError, PermissionError):
                        pass
                    proc.wait(timeout=5)
                    break
        except BaseException:
            try:
                os.killpg(os.getpgid(proc.pid), _signal.SIGKILL)
            except (ProcessLookupError, PermissionError):
                pass
            raise

        wall_s = time.time() - t_start
        stdout = ''.join(stdout_buf)

        if early_aborted:
            verdict = 'aborted'
        else:
            first_line = stdout.strip().split('\n', 1)[0] if stdout else ''
            if first_line == 'sat':
                verdict = 'sat'
            elif first_line == 'unsat':
                verdict = 'unsat'
            elif 'timeout' in stdout or proc.returncode in (-9, 137):
                verdict = 'timeout'
            elif 'unknown' in first_line:
                verdict = 'unknown'
            else:
                verdict = 'error' if proc.returncode != 0 else 'unknown'

        final_stats = parse_final_stats(stdout)
        nlsat_calls = group_nlsat_calls(timeline)
        signature = infer_signature(timeline, final_stats, wall_s, verdict)

        return Z3RunResult(
            smt2_path=Path(self.smt2), argv=argv,
            verdict=verdict, wall_s=wall_s,
            final_stats=final_stats, timeline=timeline,
            nlsat_calls=nlsat_calls, signature=signature,
            early_aborted=early_aborted, abort_reason=abort_reason,
            stdout=stdout, stderr_lines_count=stderr_lines,
        )
