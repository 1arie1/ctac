from __future__ import annotations

import io
import subprocess

import pytest

import ctac.smt.runner as runner_mod
from ctac.smt.runner import build_z3_argv, parse_z3_args


def test_build_z3_argv_includes_timeout_seed_tactic() -> None:
    argv = build_z3_argv(
        z3_path="z3",
        timeout_seconds=12,
        seed=0,
        tactic="default",
        extra_args=["-smt2"],
    )
    assert argv[0] == "z3"
    assert "-T:12" in argv
    assert "smt.random_seed=0" in argv
    assert "tactic.default_tactic=default" in argv
    assert "-smt2" in argv
    assert argv[-1] == "-in"


def test_parse_z3_args_shell_splitting() -> None:
    args = parse_z3_args('-v:1 -st "foo bar"')
    assert args == ["-v:1", "-st", "foo bar"]


def test_run_z3_solver_timeout_marks_timed_out(monkeypatch) -> None:
    class _FakeProc:
        def __init__(self):
            self.pid = 42
            self.returncode = 124
            self.stdout = io.StringIO("partial-out")
            self.stderr = io.StringIO("partial-err")

        def communicate(self, *, input, timeout):
            raise subprocess.TimeoutExpired(cmd="z3", timeout=timeout)

        def poll(self):
            return None

        def wait(self, timeout):
            return 124

    monkeypatch.setattr(runner_mod.subprocess, "Popen", lambda *args, **kwargs: _FakeProc())
    monkeypatch.setattr(runner_mod, "_terminate_process_group", lambda proc: None)
    res = runner_mod.run_z3_solver(
        smt_text="(check-sat)\n",
        z3_path="z3",
        timeout_seconds=1,
        seed=0,
        tactic="default",
        extra_args=[],
    )
    assert res.timed_out is True
    assert "partial-out" in res.stdout


def test_run_z3_solver_keyboard_interrupt_cleans_up(monkeypatch) -> None:
    class _FakeProc:
        def __init__(self):
            self.pid = 43
            self.returncode = None
            self.stdout = io.StringIO("")
            self.stderr = io.StringIO("")

        def communicate(self, *, input, timeout):
            raise KeyboardInterrupt()

        def poll(self):
            return None

        def wait(self, timeout):
            return 0

    cleaned = {"ok": False}
    monkeypatch.setattr(runner_mod.subprocess, "Popen", lambda *args, **kwargs: _FakeProc())
    monkeypatch.setattr(runner_mod, "_terminate_process_group", lambda proc: cleaned.__setitem__("ok", True))
    with pytest.raises(KeyboardInterrupt):
        runner_mod.run_z3_solver(
            smt_text="(check-sat)\n",
            z3_path="z3",
            timeout_seconds=None,
            seed=0,
            tactic="default",
            extra_args=[],
        )
    assert cleaned["ok"] is True

