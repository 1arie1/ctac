from __future__ import annotations

from pathlib import Path

from typer.testing import CliRunner

import ctac.tool.commands_smt as commands_smt
from ctac.smt.runner import Z3RunResult
from ctac.tool.main import app

TAC_OK = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tb:bool
}
Program {
\tBlock entry Succ [ok, bad] {
\t\tAssignExpCmd b true
\t\tJumpiCmd ok bad b
\t}
\tBlock ok Succ [] {
\t\tAssertCmd b "must hold"
\t}
\tBlock bad Succ [] {
\t\tAssumeExpCmd false
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""

TAC_NO_ASSERT = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tb:bool
}
Program {
\tBlock entry Succ [] {
\t\tAssignExpCmd b true
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""

TAC_MULTIPLE_ASSERT = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tb:bool
}
Program {
\tBlock entry Succ [ok] {
\t\tAssignExpCmd b true
\t\tJumpCmd ok
\t}
\tBlock ok Succ [exit] {
\t\tAssertCmd b "first"
\t\tJumpCmd exit
\t}
\tBlock exit Succ [] {
\t\tAssertCmd b "second"
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""

TAC_ASSERT_NOT_LAST = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tb:bool
}
Program {
\tBlock entry Succ [exit] {
\t\tAssertCmd b "bad shape"
\t\tJumpCmd exit
\t}
\tBlock exit Succ [] {
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""

TAC_CYCLIC = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tb:bool
}
Program {
\tBlock entry Succ [loop] {
\t\tAssignExpCmd b true
\t\tJumpCmd loop
\t}
\tBlock loop Succ [entry] {
\t\tAssertCmd b "loop assert"
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""

# Chain of two conditional jumps whose failing branches fan into a shared
# sink — the shape `ctac ua` produces. `check1` and `check2` each have two
# successors, and `sink` has two predecessors, so (check1, sink) and
# (check2, sink) are critical edges. sea_vc's exclusivity is unsound on
# this shape.
TAC_CRITICAL_EDGE = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tb1:bool
\tb2:bool
}
Program {
\tBlock entry Succ [check1] {
\t\tAssignExpCmd b1 true
\t\tAssignExpCmd b2 false
\t\tJumpCmd check1
\t}
\tBlock check1 Succ [check2, sink] {
\t\tJumpiCmd check2 sink b1
\t}
\tBlock check2 Succ [ok, sink] {
\t\tJumpiCmd ok sink b2
\t}
\tBlock ok Succ [] {
\t\tAssumeExpCmd b2
\t}
\tBlock sink Succ [] {
\t\tAssertCmd false "merged failure"
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""


def _write_tac(tmp_path: Path, content: str, name: str) -> Path:
    path = tmp_path / name
    path.write_text(content, encoding="utf-8")
    return path


def test_smt_cli_emits_smtlib_and_check_sat(tmp_path: Path) -> None:
    p = _write_tac(tmp_path, TAC_OK, "ok.tac")
    runner = CliRunner()
    res = runner.invoke(app, ["smt", str(p), "--plain"])
    assert res.exit_code == 0
    assert "# encoding: sea_vc" in res.stdout
    # Default is QF_UFNIA; with --tight-logic, the NIA-only case narrows to QF_NIA.
    assert "(set-logic QF_UFNIA)" in res.stdout
    assert "(check-sat)" in res.stdout
    assert "(assert (=> BLK_EXIT (and (not b) BLK_ok)))" in res.stdout


def test_smt_cli_tight_logic_narrows_to_qf_nia(tmp_path: Path) -> None:
    p = _write_tac(tmp_path, TAC_OK, "tight.tac")
    runner = CliRunner()
    res = runner.invoke(app, ["smt", str(p), "--plain", "--tight-logic"])
    assert res.exit_code == 0
    assert "(set-logic QF_NIA)" in res.stdout


def test_smt_cli_rejects_missing_assert(tmp_path: Path) -> None:
    p = _write_tac(tmp_path, TAC_NO_ASSERT, "no-assert.tac")
    runner = CliRunner()
    res = runner.invoke(app, ["smt", str(p), "--plain"])
    assert res.exit_code == 1
    assert "expected exactly one AssertCmd in program, found 0" in res.stdout


def test_smt_cli_rejects_multiple_asserts(tmp_path: Path) -> None:
    p = _write_tac(tmp_path, TAC_MULTIPLE_ASSERT, "multi-assert.tac")
    runner = CliRunner()
    res = runner.invoke(app, ["smt", str(p), "--plain"])
    assert res.exit_code == 1
    assert "expected exactly one AssertCmd in program, found 2" in res.stdout


def test_smt_cli_rejects_assert_not_last(tmp_path: Path) -> None:
    p = _write_tac(tmp_path, TAC_ASSERT_NOT_LAST, "assert-not-last.tac")
    runner = CliRunner()
    res = runner.invoke(app, ["smt", str(p), "--plain"])
    assert res.exit_code == 1
    assert "AssertCmd must be the last command in block entry" in res.stdout


def test_smt_cli_rejects_cyclic_cfg(tmp_path: Path) -> None:
    p = _write_tac(tmp_path, TAC_CYCLIC, "cyclic.tac")
    runner = CliRunner()
    res = runner.invoke(app, ["smt", str(p), "--plain"])
    assert res.exit_code == 1
    assert "loop-free (acyclic) TAC program" in res.stdout


def test_smt_cli_auto_splits_critical_edges(tmp_path: Path) -> None:
    # Critical-edge input should not be rejected: ctac smt runs
    # split_critical_edges as a pre-pass, so the VC is built on a
    # cleaned-up CFG. Verify the VC emits and names a shim block.
    p = _write_tac(tmp_path, TAC_CRITICAL_EDGE, "critical.tac")
    runner = CliRunner()
    res = runner.invoke(app, ["smt", str(p), "--plain"])
    assert res.exit_code == 0
    assert "(check-sat)" in res.stdout
    # Shim ids follow `{u}_to_{v}`; at least one of the critical edges
    # (check1 -> sink, check2 -> sink) should surface as a BLK_ decl.
    assert "BLK_check1_to_sink" in res.stdout or "BLK_check2_to_sink" in res.stdout


def test_smt_cli_output_file(tmp_path: Path) -> None:
    p = _write_tac(tmp_path, TAC_OK, "ok-out.tac")
    out = tmp_path / "out.smt2"
    runner = CliRunner()
    res = runner.invoke(app, ["smt", str(p), "--plain", "-o", str(out)])
    assert res.exit_code == 0
    assert out.exists()
    txt = out.read_text(encoding="utf-8")
    assert "(check-sat)" in txt


def test_smt_cli_sea_vc_encoding_smoke(tmp_path: Path) -> None:
    p = _write_tac(tmp_path, TAC_OK, "ok-sea.tac")
    runner = CliRunner()
    res = runner.invoke(app, ["smt", str(p), "--plain", "--encoding", "sea_vc"])
    assert res.exit_code == 0
    # Default logic is QF_UFNIA regardless of whether UF was actually needed.
    assert "(set-logic QF_UFNIA)" in res.stdout
    assert "BLK_EXIT" in res.stdout


def test_smt_cli_run_sat_writes_model(tmp_path: Path, monkeypatch) -> None:
    p = _write_tac(tmp_path, TAC_OK, "ok-run.tac")
    model_out = tmp_path / "model.txt"

    def _fake_run_z3_solver(**kwargs):
        assert kwargs["timeout_seconds"] == 5
        assert kwargs["seed"] == 7
        assert kwargs["tactic"] == "qfnia"
        assert kwargs["extra_args"] == ["-st"]
        return Z3RunResult(
            argv=("z3",),
            exit_code=0,
            stdout="sat\n(model\n  (define-fun b () Bool true)\n)\n",
            stderr="",
        )

    monkeypatch.setattr(commands_smt, "run_z3_solver", _fake_run_z3_solver)
    runner = CliRunner()
    res = runner.invoke(
        app,
        [
            "smt",
            str(p),
            "--plain",
            "--run",
            "--timeout",
            "5",
            "--seed",
            "7",
            "--tactic",
            "qfnia",
            "--z3-args",
            "-st",
            "--model",
            str(model_out),
        ],
    )
    assert res.exit_code == 0
    assert "sat" in res.stdout
    assert model_out.exists()
    assert "TAC model begin" in model_out.read_text(encoding="utf-8")


def test_smt_cli_run_unsat_does_not_write_model(tmp_path: Path, monkeypatch) -> None:
    p = _write_tac(tmp_path, TAC_OK, "ok-unsat.tac")
    model_out = tmp_path / "model-unsat.txt"

    def _fake_run_z3_solver(**kwargs):
        return Z3RunResult(argv=("z3",), exit_code=0, stdout="unsat\n", stderr="")

    monkeypatch.setattr(commands_smt, "run_z3_solver", _fake_run_z3_solver)
    runner = CliRunner()
    res = runner.invoke(app, ["smt", str(p), "--plain", "--run", "--model", str(model_out)])
    assert res.exit_code == 0
    assert "unsat" in res.stdout
    assert not model_out.exists()


def test_smt_cli_run_timeout_exits_2(tmp_path: Path, monkeypatch) -> None:
    p = _write_tac(tmp_path, TAC_OK, "ok-timeout.tac")

    def _fake_run_z3_solver(**kwargs):
        return Z3RunResult(argv=("z3",), exit_code=0, stdout="", stderr="", timed_out=True)

    monkeypatch.setattr(commands_smt, "run_z3_solver", _fake_run_z3_solver)
    runner = CliRunner()
    res = runner.invoke(app, ["smt", str(p), "--plain", "--run"])
    assert res.exit_code == 2
    assert "timeout" in res.stdout


def test_smt_cli_run_prints_solver_command_without_plain(tmp_path: Path, monkeypatch) -> None:
    p = _write_tac(tmp_path, TAC_OK, "ok-run-rich.tac")

    def _fake_run_z3_solver(**kwargs):
        return Z3RunResult(argv=("z3", "smt.random_seed=0", "-in"), exit_code=0, stdout="unsat\n", stderr="")

    monkeypatch.setattr(commands_smt, "run_z3_solver", _fake_run_z3_solver)
    runner = CliRunner()
    res = runner.invoke(app, ["smt", str(p), "--run"])
    assert res.exit_code == 0
    assert "solver: z3 smt.random_seed=0 -in" in res.stdout
    assert "solver exit_code: 0" in res.stdout


def test_smt_cli_run_nonzero_unknown_fails(tmp_path: Path, monkeypatch) -> None:
    p = _write_tac(tmp_path, TAC_OK, "ok-fail.tac")

    def _fake_run_z3_solver(**kwargs):
        return Z3RunResult(argv=("z3",), exit_code=9, stdout="", stderr="boom")

    monkeypatch.setattr(commands_smt, "run_z3_solver", _fake_run_z3_solver)
    runner = CliRunner()
    res = runner.invoke(app, ["smt", str(p), "--plain", "--run"])
    assert res.exit_code == 1
    assert "# solver stderr: boom" in res.stdout


def test_smt_cli_rejects_unsat_core_with_model(tmp_path: Path) -> None:
    p = _write_tac(tmp_path, TAC_OK, "ok-both.tac")
    model_out = tmp_path / "m.txt"
    runner = CliRunner()
    res = runner.invoke(
        app,
        ["smt", str(p), "--plain", "--unsat-core", "--model", str(model_out)],
    )
    assert res.exit_code == 1
    assert "cannot combine" in res.stdout


def test_smt_cli_run_unsat_core_uses_script_without_get_model(tmp_path: Path, monkeypatch) -> None:
    p = _write_tac(tmp_path, TAC_OK, "ok-uc.tac")

    def _fake_run_z3_solver(**kwargs):
        smt = kwargs["smt_text"]
        assert "(get-unsat-core)" in smt
        assert "(get-model)" not in smt
        return Z3RunResult(argv=("z3",), exit_code=0, stdout="unsat\n(TAC_42)\n", stderr="")

    monkeypatch.setattr(commands_smt, "run_z3_solver", _fake_run_z3_solver)
    runner = CliRunner()
    res = runner.invoke(app, ["smt", str(p), "--plain", "--run", "--unsat-core"])
    assert res.exit_code == 0
    assert "unsat" in res.stdout
    assert "(TAC_42)" in res.stdout


def test_smt_cli_run_debug_prints_interaction_and_replay_cmd(tmp_path: Path, monkeypatch) -> None:
    p = _write_tac(tmp_path, TAC_OK, "ok-debug.tac")

    def _fake_run_z3_solver(**kwargs):
        return Z3RunResult(
            argv=("z3", "smt.random_seed=0", "tactic.default_tactic=default", "-in"),
            exit_code=0,
            stdout="sat\n(model\n  (define-fun b () Bool true)\n)\n",
            stderr="",
        )

    monkeypatch.setattr(commands_smt, "run_z3_solver", _fake_run_z3_solver)
    runner = CliRunner()
    res = runner.invoke(app, ["smt", str(p), "--plain", "--run", "--debug"])
    assert res.exit_code == 0
    assert "# debug replay smt:" in res.stdout
    assert "# debug replay cmd: z3 smt.random_seed=0 tactic.default_tactic=default" in res.stdout
    assert "# debug z3 stdin begin" in res.stdout
    assert "# debug z3 stdout begin" in res.stdout
    assert "# debug z3 stderr begin" in res.stdout
