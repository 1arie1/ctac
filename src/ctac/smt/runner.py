from __future__ import annotations

import os
import shlex
import signal
import subprocess
from dataclasses import dataclass


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
) -> list[str]:
    argv = [z3_path]
    if timeout_seconds is not None:
        argv.append(f"-T:{timeout_seconds}")
    argv.append(f"smt.random_seed={seed}")
    argv.append(f"tactic.default_tactic={tactic}")
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
) -> Z3RunResult:
    argv = build_z3_argv(
        z3_path=z3_path,
        timeout_seconds=timeout_seconds,
        seed=seed,
        tactic=tactic,
        extra_args=extra_args,
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
    return Z3RunResult(
        argv=tuple(argv),
        exit_code=proc.returncode,
        stdout=stdout,
        stderr=stderr,
        timed_out=timed_out,
    )
