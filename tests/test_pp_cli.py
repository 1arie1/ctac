"""CLI tests for `ctac pp`, focusing on the `-o`/`--output` file-output option."""

from __future__ import annotations

from pathlib import Path

from typer.testing import CliRunner

from ctac.tool.main import app

TAC_SMALL = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\ta:bv256
\tb:bool
}
Program {
\tBlock entry Succ [next] {
\t\tAssignExpCmd a 0x1
\t\tAssignExpCmd b true
\t\tJumpCmd next
\t}
\tBlock next Succ [] {
\t\tAssertCmd b "must hold"
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""


def _write_tac(tmp_path: Path, content: str, name: str) -> Path:
    p = tmp_path / name
    p.write_text(content, encoding="utf-8")
    return p


def test_pp_output_file_option_writes_content(tmp_path: Path) -> None:
    """`ctac pp -o FILE` writes the pretty-printed output to FILE and a confirmation line to stdout."""
    tac = _write_tac(tmp_path, TAC_SMALL, "small.tac")
    out = tmp_path / "pp.out"
    runner = CliRunner()
    res = runner.invoke(app, ["pp", str(tac), "-o", str(out), "--plain"])
    assert res.exit_code == 0, res.output
    assert out.is_file()
    text = out.read_text(encoding="utf-8")
    # Block headers and commands are in the file (plain, no ANSI).
    assert "entry:" in text
    assert "next:" in text
    assert "assert b" in text
    # `# printer:` metadata line.
    assert "# printer: human" in text
    # Stdout got only the confirmation message, not the pp content.
    assert "# wrote" in res.output
    assert "entry:" not in res.output


def test_pp_without_output_prints_to_stdout(tmp_path: Path) -> None:
    """Without `-o`, pp prints to stdout as before (no file written)."""
    tac = _write_tac(tmp_path, TAC_SMALL, "small2.tac")
    runner = CliRunner()
    res = runner.invoke(app, ["pp", str(tac), "--plain"])
    assert res.exit_code == 0, res.output
    assert "entry:" in res.output
    assert "# printer: human" in res.output


def test_pp_output_file_omits_ansi_codes(tmp_path: Path) -> None:
    """File output is plain text — no ANSI escape sequences."""
    tac = _write_tac(tmp_path, TAC_SMALL, "small3.tac")
    out = tmp_path / "pp3.out"
    runner = CliRunner()
    res = runner.invoke(app, ["pp", str(tac), "-o", str(out)])  # no --plain
    assert res.exit_code == 0, res.output
    text = out.read_text(encoding="utf-8")
    assert "\x1b[" not in text  # no ANSI escape sequences in the file
