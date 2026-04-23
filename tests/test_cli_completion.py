"""Tests for shell-completion wiring.

We can't exercise Typer's install-completion path from inside pytest
(it requires an interactive shell parent to detect zsh/bash/fish via
shellingham). What we *can* pin:

- The Typer app exposes ``--install-completion`` / ``--show-completion``.
- The per-option completion callbacks return the expected candidates.
"""

from __future__ import annotations

from typer.testing import CliRunner

from ctac.tool.cli_runtime import (
    complete_choices,
    complete_rule_names,
    complete_search_tokens,
    complete_smt_encodings,
)
from ctac.tool.main import app


def test_main_help_advertises_completion_flags():
    runner = CliRunner()
    result = runner.invoke(app, ["--help"])
    assert result.exit_code == 0, result.output
    assert "--install-completion" in result.output
    assert "--show-completion" in result.output


def test_complete_choices_filters_by_prefix():
    fn = complete_choices(["goto", "edges", "dot"])
    assert fn("") == ["goto", "edges", "dot"]
    assert fn("e") == ["edges"]
    assert fn("g") == ["goto"]
    assert fn("x") == []


def test_complete_smt_encodings_lists_known_encoders():
    fn = complete_smt_encodings()
    out = fn("")
    # `sea_vc` is the only encoder right now; the list should be non-empty
    # and contain it. If future encoders are added, update this pin.
    assert "sea_vc" in out
    assert len(out) >= 1


def test_complete_rule_names_returns_registered_cases():
    fn = complete_rule_names()
    assert fn("R4") == ["R4", "R4a"]
    assert fn("R6") == ["R6"]
    assert fn("X") == []


def test_complete_search_tokens_covers_ops_and_cmds():
    fn = complete_search_tokens()
    # Expression ops: bitwise family complete from a common prefix.
    assert fn("BW") == ["BWAnd", "BWOr", "BWXOr"]
    # Shift family — all three.
    assert fn("Shift") == [
        "ShiftLeft",
        "ShiftRightLogical",
        "ShiftRightArithmetical",
    ]
    # Command kinds.
    assert fn("Assign") == ["AssignExpCmd", "AssignHavocCmd"]
    assert "AssertCmd" in fn("Assert")
    # Builtin function symbols.
    assert fn("safe") == ["safe_math_narrow_bv256:bif"]
    # Humanized keywords (for searches under --printer human).
    assert "havoc" in fn("h")
    assert "assume" in fn("a")
    # No false positives.
    assert fn("zzzzz") == []
    # Empty prefix returns the full set (bounded for sanity).
    assert 30 < len(fn("")) < 100


def test_search_pattern_arg_declares_completion():
    """Regression guard: the `pattern` positional carries the token completer."""
    import typer
    click_app = typer.main.get_command(app)
    sub = click_app.commands["search"]  # type: ignore[attr-defined]
    pattern_param = next(p for p in sub.params if p.name == "pattern")
    assert pattern_param.shell_complete is not None
