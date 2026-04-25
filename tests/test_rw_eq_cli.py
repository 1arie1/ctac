"""CLI tests for `ctac rw-eq`."""

from __future__ import annotations

from pathlib import Path

from typer.testing import CliRunner

from ctac.tool.main import app


_ORIG_TAC = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tR:bv256
}
Program {
\tBlock e Succ [] {
\t\tAssignExpCmd R Add(0x1 0x2)
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""


_RW_TAC = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tR:bv256
}
Program {
\tBlock e Succ [] {
\t\tAssignExpCmd R 0x3
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""


_R4A_ORIG = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tA:int
\tB:int
\tX:int
}
Program {
\tBlock e Succ [] {
\t\tAssignHavocCmd A
\t\tAssignHavocCmd B
\t\tAssumeExpCmd Gt(B 0x0)
\t\tAssignExpCmd X Div(A B)
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""


_R4A_RW = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tA:int
\tB:int
\tX:int
}
Program {
\tBlock e Succ [] {
\t\tAssignHavocCmd A
\t\tAssignHavocCmd B
\t\tAssumeExpCmd Gt(B 0x0)
\t\tAssignHavocCmd X
\t\tAssumeExpCmd Le(Mul(B X) A)
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""


def _write(tmp_path: Path, body: str, name: str) -> Path:
    p = tmp_path / name
    p.write_text(body, encoding="utf-8")
    return p


def test_cli_emits_merged_program(tmp_path: Path) -> None:
    o = _write(tmp_path, _ORIG_TAC, "orig.tac")
    r = _write(tmp_path, _RW_TAC, "rw.tac")
    out = tmp_path / "eq.tac"
    runner = CliRunner()
    res = runner.invoke(app, ["rw-eq", str(o), str(r), "-o", str(out), "--plain"])
    assert res.exit_code == 0, res.output
    assert out.is_file()
    text = out.read_text()
    # An equivalence assert was added.
    assert "AssertCmd CHK0" in text
    # The CHK0 declaration is in the symbol table.
    assert "CHK0:bool" in text


def test_cli_report_shows_rule_hits(tmp_path: Path) -> None:
    o = _write(tmp_path, _ORIG_TAC, "orig.tac")
    r = _write(tmp_path, _RW_TAC, "rw.tac")
    out = tmp_path / "eq.tac"
    runner = CliRunner()
    res = runner.invoke(
        app,
        ["rw-eq", str(o), str(r), "-o", str(out), "--plain", "--report"],
    )
    assert res.exit_code == 0, res.output
    assert "rule_2_assignment_diff: 1" in res.stdout
    assert "asserts_emitted: 1" in res.stdout
    assert "rehavoc_admissions: 0" in res.stdout


def test_cli_strict_aborts_on_rehavoc(tmp_path: Path) -> None:
    o = _write(tmp_path, _R4A_ORIG, "orig.tac")
    r = _write(tmp_path, _R4A_RW, "rw.tac")
    out = tmp_path / "eq.tac"
    runner = CliRunner()
    res = runner.invoke(
        app,
        ["rw-eq", str(o), str(r), "-o", str(out), "--plain", "--strict"],
    )
    # Distinct exit code for rule-6 strict.
    assert res.exit_code == 2
    assert "rule-6 rehavoc" in res.stdout
    assert not out.exists()


def test_cli_rehavoc_emits_warning(tmp_path: Path) -> None:
    # Click's CliRunner captures stdout + stderr together into `output`.
    # We just need to confirm the warning text appears somewhere in the
    # invocation's combined output.
    o = _write(tmp_path, _R4A_ORIG, "orig.tac")
    r = _write(tmp_path, _R4A_RW, "rw.tac")
    out = tmp_path / "eq.tac"
    runner = CliRunner()
    res = runner.invoke(
        app, ["rw-eq", str(o), str(r), "-o", str(out), "--plain"]
    )
    assert res.exit_code == 0, res.output
    assert "WARNING: 1 rehavoc admission(s) used" in res.output
    assert "rule 6" in res.output


def test_cli_check_feasibility_emits_assert_false(tmp_path: Path) -> None:
    o = _write(tmp_path, _R4A_ORIG, "orig.tac")
    r = _write(tmp_path, _R4A_RW, "rw.tac")
    out = tmp_path / "eq.tac"
    runner = CliRunner()
    res = runner.invoke(
        app,
        [
            "rw-eq",
            str(o),
            str(r),
            "-o",
            str(out),
            "--plain",
            "--check-feasibility",
            "--report",
        ],
    )
    assert res.exit_code == 0, res.output
    assert "feasibility_asserts: 1" in res.stdout
    text = out.read_text()
    assert "rw-eq-feasibility:" in text


def test_cli_block_mismatch_returns_exit_1(tmp_path: Path) -> None:
    o = _write(
        tmp_path,
        _ORIG_TAC.replace("Block e Succ", "Block entry Succ"),
        "orig.tac",
    )
    r = _write(
        tmp_path,
        _RW_TAC.replace("Block e Succ", "Block different Succ"),
        "rw.tac",
    )
    out = tmp_path / "eq.tac"
    runner = CliRunner()
    res = runner.invoke(
        app, ["rw-eq", str(o), str(r), "-o", str(out), "--plain"]
    )
    assert res.exit_code == 1, res.output
    assert "block-order mismatch" in res.stdout
    assert not out.exists()


def test_cli_htac_output_pretty_printed(tmp_path: Path) -> None:
    """``-o FILE.htac`` writes pretty-printed TAC; ``-o FILE.tac`` writes
    raw round-trippable TAC. Same convention as ``ctac rw``."""
    o = _write(tmp_path, _ORIG_TAC, "orig.tac")
    r = _write(tmp_path, _RW_TAC, "rw.tac")
    out_tac = tmp_path / "eq.tac"
    out_htac = tmp_path / "eq.htac"
    runner = CliRunner()
    r1 = runner.invoke(app, ["rw-eq", str(o), str(r), "-o", str(out_tac), "--plain"])
    r2 = runner.invoke(app, ["rw-eq", str(o), str(r), "-o", str(out_htac), "--plain"])
    assert r1.exit_code == 0 and r2.exit_code == 0
    tac_text = out_tac.read_text()
    htac_text = out_htac.read_text()
    assert "AssignExpCmd" in tac_text
    assert "AssignExpCmd" not in htac_text
    assert " = " in htac_text
