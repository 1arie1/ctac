"""Tests for `ctac cfg --style blocks`."""

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
}
Program {
\tBlock a Succ [b] {
\t\tAssignHavocCmd R0
\t\tJumpCmd b
\t}
\tBlock b Succ [c] {
\t\tJumpCmd c
\t}
\tBlock c Succ [] {
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""


def _run(tmp_path, *args):
    p = tmp_path / "cfg.tac"
    p.write_text(_TAC)
    return CliRunner().invoke(app, ["cfg", str(p), "--style", "blocks", *args])


def test_blocks_style_emits_one_id_per_line(tmp_path):
    result = _run(tmp_path, "--plain")
    assert result.exit_code == 0, result.output
    lines = result.output.splitlines()
    # Exactly three block ids, nothing else.
    assert lines == ["a", "b", "c"]


def test_blocks_style_suppresses_preamble_under_filter(tmp_path):
    # `--from b` activates the filter; blocks style must still not print
    # the `# filter:` preamble line.
    result = _run(tmp_path, "--plain", "--from", "b")
    assert result.exit_code == 0, result.output
    for line in result.output.splitlines():
        assert not line.startswith("#"), f"stray header line: {line!r}"
    # Filter keeps only blocks reachable from `b` → {b, c}.
    assert set(result.output.split()) == {"b", "c"}


def test_blocks_style_shell_loop_usage(tmp_path):
    """Integration-style: the output is directly usable as a bash word list."""
    result = _run(tmp_path, "--plain")
    # Every token in the output is a valid block id with no stray
    # characters (no `#`, no braces, no `:`, no `->`).
    tokens = result.output.split()
    assert tokens == ["a", "b", "c"]
    for t in tokens:
        assert not any(ch in t for ch in "#:->{}")


def test_blocks_style_with_max_blocks_truncates_silently(tmp_path):
    # `--max-blocks 2` should emit just 2 ids with NO truncation notice.
    result = _run(tmp_path, "--plain", "--max-blocks", "2")
    assert result.exit_code == 0, result.output
    lines = [ln for ln in result.output.splitlines() if ln.strip()]
    assert lines == ["a", "b"]


def test_blocks_style_empty_program_is_silent(tmp_path):
    # No basic blocks → blocks style stays silent (empty output), so
    # shell loops `for b in $(...); do ... done` naturally iterate zero
    # times without the user having to filter noise.
    empty = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
}
Program {
}
Axioms {
}
Metas {
  "0": []
}
"""
    p = tmp_path / "empty.tac"
    p.write_text(empty)
    result = CliRunner().invoke(
        app, ["cfg", str(p), "--style", "blocks", "--plain"]
    )
    assert result.exit_code == 0, result.output
    assert result.output.strip() == ""


def test_unknown_style_error_lists_blocks_in_valid_set(tmp_path):
    """Regression: the error message now lists `blocks` in the valid set."""
    p = tmp_path / "cfg.tac"
    p.write_text(_TAC)
    # Direct invocation with a bogus style; the validator should
    # mention "blocks" in the acceptable-values message.
    result = CliRunner().invoke(
        app, ["cfg", str(p), "--style", "nope", "--plain"]
    )
    assert result.exit_code != 0
    assert "blocks" in result.output
