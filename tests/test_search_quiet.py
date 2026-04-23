"""Tests for `ctac search -q` / `--quiet` pipeable output."""

from __future__ import annotations

from typer.testing import CliRunner

from ctac.tool.main import app


_TAC = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tR0:bv256
\tR1:bv256
}
Program {
\tBlock e Succ [] {
\t\tAssignHavocCmd R0
\t\tAssignExpCmd R1 BWAnd(R0 0xff )
\t\tAssertCmd R1 "ok"
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""


def _run(tmp_path, *args):
    p = tmp_path / "q.tac"
    p.write_text(_TAC)
    return CliRunner().invoke(app, ["search", str(p), *args])


def test_quiet_suppresses_hash_preamble(tmp_path):
    result = _run(tmp_path, "BWAnd", "--plain", "--count", "-q")
    assert result.exit_code == 0, result.output
    # No `#` header lines at all.
    for line in result.output.splitlines():
        assert not line.startswith("#"), f"stray header line: {line!r}"
    # The numeric result lines survive.
    assert "matches: 1" in result.output
    assert "blocks_with_matches: 1" in result.output


def test_quiet_output_is_awk_parseable(tmp_path):
    """Idiomatic: pipe through `awk '/^matches:/ {print $2}'`."""
    result = _run(tmp_path, "BWAnd", "--plain", "--count", "-q")
    assert result.exit_code == 0
    # First non-empty line starts with "matches: " and parses as a count.
    lines = [ln for ln in result.output.splitlines() if ln.strip()]
    assert lines[0].startswith("matches: ")
    count = int(lines[0].split()[1])
    assert count == 1


def test_quiet_with_count_by_match_strips_header_and_total(tmp_path):
    result = _run(tmp_path, "0x[0-9a-f]+", "--plain", "--count-by-match", "-q")
    assert result.exit_code == 0, result.output
    # Header/footer gone; tally rows remain.
    for line in result.output.splitlines():
        assert not line.startswith("#"), f"stray header line: {line!r}"
    # The 0xff mask should be tallied.
    assert "0xff" in result.output


def test_quiet_without_count_keeps_match_lines(tmp_path):
    # In normal mode, matches: / blocks_with_matches: still appear; preamble gone.
    result = _run(tmp_path, "BWAnd", "--plain", "-q")
    assert result.exit_code == 0
    hash_lines = [ln for ln in result.output.splitlines() if ln.startswith("#")]
    assert hash_lines == [], f"stray #-lines: {hash_lines}"
    # The match row + footer numbers survive.
    assert "BWAnd" in result.output
    assert "matches: 1" in result.output


def test_quiet_long_form(tmp_path):
    """`--quiet` works the same as `-q`."""
    result = _run(tmp_path, "BWAnd", "--plain", "--count", "--quiet")
    assert result.exit_code == 0
    assert "matches: 1" in result.output
    for line in result.output.splitlines():
        assert not line.startswith("#")
