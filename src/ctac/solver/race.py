"""Parallel z3 race — first verdict wins, with live progress IPC.

Architecture:
  - Worker pool of N processes; each pulls (task, on_event-relay) from a
    shared input queue.
  - Workers send start / progress / done messages on an output queue.
  - Parent thread reads the output queue, updates per-task state, fires
    `on_status` callbacks (used for live dashboard rendering).
  - When parent sees a sat/unsat result, it sets a stop event and SIGKILLs
    all workers (which also kills their z3 children via process group).

Used by:
  - `ctac z3` multi-task modes (seed sweep, configs × seeds).
  - Cover orchestration (parallel cluster commits, etc.).
"""
from __future__ import annotations

import multiprocessing as mp
import os
import queue as _queue
import signal as _signal
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Callable

from ctac.solver.config import Z3Config
from ctac.solver.runner import AbortPolicy, ProgressEvent, Z3Runner, Z3RunResult


@dataclass(frozen=True)
class RaceTask:
    """One (config, seed, smt2) job."""
    config: Z3Config
    seed: int
    smt2: Path
    timeout_s: int
    z3_bin: Path | str | None = None

    @property
    def label(self) -> str:
        return f'{self.config.name}/seed={self.seed}'


@dataclass
class TaskStatus:
    """Live state of one task in the race; consumed by render callbacks."""
    label: str
    status: str                          # 'pending' | 'running' | 'done' | 'error'
    started_at: float | None = None      # wall-clock start (time.time())
    events: list = None                  # ProgressEvent list for live signature
    last_event_kind: str | None = None   # 'smt-stats' / 'nlsat-line' / 'tactic-start'
    n_smt_stats: int = 0
    n_nlsat: int = 0
    verdict: str | None = None
    wall_s: float | None = None
    signature_label: str | None = None
    signature_confidence: float | None = None

    def __post_init__(self) -> None:
        if self.events is None:
            self.events = []

    def elapsed_now(self) -> float | None:
        if self.started_at is None or self.status != 'running':
            return None
        return time.time() - self.started_at

    def live_signature(self) -> tuple[str, float] | None:
        """Compute a partial signature from events seen so far.

        Useful for the dashboard while a task is still running. Returns
        (label, confidence) or None if no useful inference is possible
        yet (e.g. waiting for first event)."""
        if not self.events:
            return None
        # Late import to avoid an import cycle (signature → runner → ...)
        from ctac.solver.signature import infer_signature
        wall_s = self.elapsed_now() or 0.0
        sig = infer_signature(self.events, {}, wall_s, 'unknown')
        return (sig.label, sig.confidence)


@dataclass
class RaceResult:
    winner: tuple[RaceTask, Z3RunResult] | None
    all_results: list[tuple[RaceTask, Z3RunResult]]
    wall_s: float
    aborted_count: int

    @property
    def winner_task(self) -> RaceTask | None:
        return self.winner[0] if self.winner else None

    @property
    def winner_result(self) -> Z3RunResult | None:
        return self.winner[1] if self.winner else None


# ---- Worker -----------------------------------------------------------------


def _race_worker(in_q: 'mp.Queue', msg_q: 'mp.Queue',
                  stop_event: 'mp.Event',
                  abort_policy_kwargs: dict | None) -> None:
    """Worker process: pull tasks from in_q, run them, post to msg_q.

    Installs a SIGTERM handler to kill the current z3 child on parent
    termination."""
    # Note: import inside worker to avoid issues with fork/pickling.
    _current_z3_pid: list[int] = []   # mutable holder accessible from handler

    def _on_sigterm(signum, frame):  # noqa: ARG001
        for pid in list(_current_z3_pid):
            try:
                os.killpg(os.getpgid(pid), _signal.SIGKILL)
            except (ProcessLookupError, PermissionError):
                pass
        sys.exit(1)

    _signal.signal(_signal.SIGTERM, _on_sigterm)

    while not stop_event.is_set():
        try:
            task = in_q.get(timeout=0.5)
        except _queue.Empty:
            continue
        if task is None:   # poison pill: drain
            break

        msg_q.put(('start', task.label, None))

        def on_event(ev) -> None:
            if stop_event.is_set():
                return
            msg_q.put(('progress', task.label, {
                'wall_s': ev.wall_s,
                'kind': ev.kind,
                'payload': dict(ev.payload),
            }))

        policy = AbortPolicy(**abort_policy_kwargs) if abort_policy_kwargs else None
        runner = Z3Runner(
            smt2=task.smt2, timeout_s=task.timeout_s, seed=task.seed,
            z3_bin=task.z3_bin, extra_args=task.config.args,
        )
        # Patch the runner to share the z3 child pid with this worker's
        # sigterm handler. Wrap _spawn? Easier: detect after run starts via
        # signal. We accept a small race here; the z3 process group will
        # be SIGKILL'd by the worker.kill() path even without our handler.
        try:
            result = runner.run(abort_policy=policy, on_event=on_event)
            msg_q.put(('done', task.label, (task, result)))
        except BaseException as e:
            msg_q.put(('error', task.label, (task, str(e))))

        if stop_event.is_set():
            break


# ---- Driver -----------------------------------------------------------------


def _accept_definitive(result: Z3RunResult) -> bool:
    return result.verdict in ('sat', 'unsat')


def race(tasks: list[RaceTask], *,
          max_concurrent: int | None = None,
          accept: Callable[[Z3RunResult], bool] = _accept_definitive,
          abort_policy: AbortPolicy | None = None,
          on_complete: Callable[[RaceTask, Z3RunResult], None] | None = None,
          on_status: Callable[[dict[str, TaskStatus]], None] | None = None,
          status_refresh_s: float = 0.25,
          ) -> RaceResult:
    """Run tasks in parallel; return first acceptable verdict.

    Args:
      tasks: jobs to race.
      max_concurrent: worker pool size. None → cpu_count // 2 (min 1).
      accept: predicate; first task whose result satisfies it wins.
              On winner, remaining workers are SIGKILL'd.
      abort_policy: per-task abort policy (passed to Z3Runner).
      on_complete: callback after each task finishes.
      on_status: callback fired periodically (every status_refresh_s)
                 with the full {label → TaskStatus} dict. Used for live
                 dashboards.
      status_refresh_s: how often to fire on_status when no events are
                        arriving (events trigger immediate updates too).
    """
    if max_concurrent is None:
        max_concurrent = max(1, (os.cpu_count() or 2) // 2)
    if not tasks:
        return RaceResult(winner=None, all_results=[], wall_s=0.0, aborted_count=0)

    policy_kwargs: dict | None = None
    if abort_policy is not None:
        policy_kwargs = {
            'min_wall_s': abort_policy.min_wall_s,
            'no_progress_window_s': abort_policy.no_progress_window_s,
            'nlsat_stuck_window_s': abort_policy.nlsat_stuck_window_s,
            'preprocessing_max_s': abort_policy.preprocessing_max_s,
        }

    ctx = mp.get_context('fork')
    in_q: mp.Queue = ctx.Queue()
    msg_q: mp.Queue = ctx.Queue()
    stop_event = ctx.Event()

    n_workers = min(max_concurrent, len(tasks))
    workers: list[mp.Process] = []
    for _ in range(n_workers):
        w = ctx.Process(target=_race_worker,
                         args=(in_q, msg_q, stop_event, policy_kwargs),
                         daemon=True)
        w.start()
        workers.append(w)

    for t in tasks:
        in_q.put(t)
    # Poison pills to let workers exit cleanly if no winner triggers shutdown
    for _ in workers:
        in_q.put(None)

    state: dict[str, TaskStatus] = {
        t.label: TaskStatus(label=t.label, status='pending') for t in tasks
    }

    all_results: list[tuple[RaceTask, Z3RunResult]] = []
    winner: tuple[RaceTask, Z3RunResult] | None = None
    aborted = 0
    completed = 0
    n_tasks = len(tasks)

    t0 = time.time()
    last_status_emit = 0.0

    def maybe_emit_status(force: bool = False) -> None:
        nonlocal last_status_emit
        if on_status is None:
            return
        now = time.time()
        if force or (now - last_status_emit) >= status_refresh_s:
            on_status(state)
            last_status_emit = now

    try:
        while completed < n_tasks and winner is None:
            try:
                kind, label, data = msg_q.get(timeout=status_refresh_s)
            except _queue.Empty:
                maybe_emit_status()
                continue

            if kind == 'start':
                state[label].status = 'running'
                state[label].started_at = time.time()
            elif kind == 'progress':
                # data is {'wall_s', 'kind', 'payload'} (from the worker)
                ev_kind = data.get('kind')
                state[label].last_event_kind = ev_kind
                if ev_kind == 'smt-stats':
                    state[label].n_smt_stats += 1
                elif ev_kind == 'nlsat-line':
                    state[label].n_nlsat += 1
                state[label].events.append(ProgressEvent(
                    wall_s=data.get('wall_s', 0.0),
                    kind=ev_kind,
                    payload=data.get('payload', {}),
                ))
            elif kind == 'done':
                task, result = data
                state[label].status = 'done'
                state[label].verdict = result.verdict
                state[label].wall_s = result.wall_s
                if result.signature is not None:
                    state[label].signature_label = result.signature.label
                    state[label].signature_confidence = result.signature.confidence
                all_results.append((task, result))
                completed += 1
                if on_complete:
                    on_complete(task, result)
                if accept(result):
                    winner = (task, result)
            elif kind == 'error':
                task, errmsg = data
                state[label].status = 'error'
                state[label].verdict = 'error'
                completed += 1

            maybe_emit_status(force=(kind in ('start', 'done', 'error')))
    finally:
        stop_event.set()
        # Drain any leftover input so workers don't block on get
        try:
            while True:
                in_q.get_nowait()
        except _queue.Empty:
            pass
        # SIGKILL all workers (cascades to their z3 children via process
        # group when start_new_session is set in Z3Runner)
        for w in workers:
            if w.is_alive():
                try:
                    w.kill()
                except Exception:
                    pass
        # Count running-at-shutdown as aborted
        aborted = sum(1 for s in state.values()
                       if s.status in ('pending', 'running'))
        # Best-effort short join
        for w in workers:
            w.join(timeout=1.0)

    # Final status update
    if on_status is not None:
        try:
            on_status(state)
        except Exception:
            pass

    return RaceResult(winner=winner, all_results=all_results,
                       wall_s=time.time() - t0, aborted_count=aborted)
