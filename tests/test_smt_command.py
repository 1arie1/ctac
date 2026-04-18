from __future__ import annotations

from pathlib import Path

from typer.testing import CliRunner

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
    assert "(set-logic QF_NIA)" in res.stdout
    assert "(check-sat)" in res.stdout
    assert "(assert (=> BLK_EXIT (and (not b) BLK_ok)))" in res.stdout


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
    assert "(set-logic QF_NIA)" in res.stdout
    assert "BLK_EXIT" in res.stdout
