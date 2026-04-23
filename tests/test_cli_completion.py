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
    assert "sea_vc" in out
    # At least one alternative encoder is registered.
    assert len(out) >= 2


def test_complete_rule_names_returns_registered_cases():
    fn = complete_rule_names()
    assert fn("R4") == ["R4", "R4a"]
    assert fn("R6") == ["R6"]
    assert fn("X") == []
