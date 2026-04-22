from __future__ import annotations

import os
import shlex
import signal
import subprocess
import threading
import time
from dataclasses import dataclass
from typing import Callable


@dataclass(frozen=True)
class Z3RunResult:
    argv: tuple[str, ...]
    exit_code: int
    stdout: str
    stderr: str
    timed_out: bool = False


def parse_z3_args(raw: str) -> list[str]:
    return shlex.split(raw) if raw.strip() else []


def build_z3_argv(
    *,
    z3_path: str,
    timeout_seconds: int | None,
    seed: int,
    tactic: str,
    extra_args: list[str],
    want_model: bool = False,
) -> list[str]:
    argv = [z3_path]
    if timeout_seconds is not None:
        argv.append(f"-T:{timeout_seconds}")
    argv.append(f"smt.random_seed={seed}")
    argv.append(f"tactic.default_tactic={tactic}")
    if want_model:
        # Ask z3 to print the model on `sat` without polluting the
        # script with a trailing `(get-model)`.
        argv.append("-model")
    argv.extend(extra_args)
    argv.append("-in")
    return argv


def _terminate_process_group(proc: subprocess.Popen[str]) -> None:
    if proc.poll() is not None:
        return
    try:
        if os.name == "posix":
            os.killpg(proc.pid, signal.SIGTERM)
        else:
            proc.terminate()
    except OSError:
        return
    try:
        proc.wait(timeout=1.0)
        return
    except subprocess.TimeoutExpired:
        pass
    try:
        if os.name == "posix":
            os.killpg(proc.pid, signal.SIGKILL)
        else:
            proc.kill()
    except OSError:
        return
    try:
        proc.wait(timeout=1.0)
    except subprocess.TimeoutExpired:
        pass


def run_z3_solver(
    *,
    smt_text: str,
    z3_path: str,
    timeout_seconds: int | None,
    seed: int,
    tactic: str,
    extra_args: list[str],
    progress_cb: Callable[[float], None] | None = None,
    want_model: bool = False,
) -> Z3RunResult:
    argv = build_z3_argv(
        z3_path=z3_path,
        timeout_seconds=timeout_seconds,
        seed=seed,
        tactic=tactic,
        extra_args=extra_args,
        want_model=want_model,
    )
    popen_kwargs: dict[str, object] = {}
    if os.name == "posix":
        popen_kwargs["preexec_fn"] = os.setsid
    proc = subprocess.Popen(
        argv,
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        **popen_kwargs,
    )
    timed_out = False
    if progress_cb is None:
        wait_timeout = None if timeout_seconds is None else float(timeout_seconds + 2)
        try:
            stdout, stderr = proc.communicate(input=smt_text, timeout=wait_timeout)
        except subprocess.TimeoutExpired:
            timed_out = True
            _terminate_process_group(proc)
            stdout = (proc.stdout.read() if proc.stdout is not None else "") or ""
            stderr = (proc.stderr.read() if proc.stderr is not None else "") or ""
        except KeyboardInterrupt:
            _terminate_process_group(proc)
            raise
    else:
        stdout_chunks: list[str] = []
        stderr_chunks: list[str] = []

        def _reader(stream: object, out: list[str]) -> None:
            if stream is None:
                return
            while True:
                chunk = stream.readline()
                if chunk == "":
                    break
                out.append(chunk)

        t_out = threading.Thread(target=_reader, args=(proc.stdout, stdout_chunks), daemon=True)
        t_err = threading.Thread(target=_reader, args=(proc.stderr, stderr_chunks), daemon=True)
        t_out.start()
        t_err.start()

        try:
            if proc.stdin is not None:
                proc.stdin.write(smt_text)
                proc.stdin.close()
            started = time.monotonic()
            deadline = None if timeout_seconds is None else started + float(timeout_seconds + 2)
            while True:
                elapsed = time.monotonic() - started
                progress_cb(elapsed)
                if deadline is not None and time.monotonic() >= deadline:
                    timed_out = True
                    _terminate_process_group(proc)
                    break
                try:
                    proc.wait(timeout=0.2)
                    break
                except subprocess.TimeoutExpired:
                    continue
        except KeyboardInterrupt:
            _terminate_process_group(proc)
            raise

        t_out.join(timeout=1.0)
        t_err.join(timeout=1.0)
        stdout = "".join(stdout_chunks)
        stderr = "".join(stderr_chunks)

    return Z3RunResult(
        argv=tuple(argv),
        exit_code=proc.returncode,
        stdout=stdout,
        stderr=stderr,
        timed_out=timed_out,
    )
