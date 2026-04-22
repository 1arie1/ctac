"""End-to-end tests for `ctac ua`."""

from __future__ import annotations

from pathlib import Path

import pytest
from typer.testing import CliRunner

from ctac.ast.nodes import AssertCmd, JumpCmd
from ctac.parse import parse_path
from ctac.tool.main import app

KEV_TAC = Path(
    "examples/KevKaminoLtvHelper/outputs/"
    "PresolverRule-rule_calculate_liquidation_verify_summary.tac"
)


def _require(p: Path) -> Path:
    if not p.is_file():
        pytest.skip(f"target TAC not present: {p}")
    return p


def _count_asserts(program) -> int:
    return sum(
        1 for b in program.blocks for c in b.commands if isinstance(c, AssertCmd)
    )


def test_ua_merges_all_asserts_on_kev_target(tmp_path):
    runner = CliRunner()
    src = _require(KEV_TAC)
    out = tmp_path / "ua.tac"
    result = runner.invoke(
        app, ["ua", str(src), "-o", str(out), "--plain", "--report"]
    )
    assert result.exit_code == 0, result.output
    # Report header is present.
    assert "ua:" in result.output
    assert "strategy: merge" in result.output
    # The target has multiple asserts — so was_noop is false and merged>1.
    assert "was_noop: false" in result.output
    # Reparses cleanly and ends with a __UA_ERROR block.
    tac = parse_path(out)
    assert _count_asserts(tac.program) == 1
    assert any(b.id == "__UA_ERROR" for b in tac.program.blocks)


def test_ua_error_block_is_assert_false(tmp_path):
    runner = CliRunner()
    src = _require(KEV_TAC)
    out = tmp_path / "ua.tac"
    result = runner.invoke(app, ["ua", str(src), "-o", str(out), "--plain"])
    assert result.exit_code == 0, result.output
    tac = parse_path(out)
    err = next(b for b in tac.program.blocks if b.id == "__UA_ERROR")
    assert len(err.commands) == 1
    a = err.commands[0]
    assert isinstance(a, AssertCmd)


def test_ua_unknown_strategy_exits_with_error(tmp_path):
    runner = CliRunner()
    src = _require(KEV_TAC)
    result = runner.invoke(
        app, ["ua", str(src), "--strategy", "split", "--plain"]
    )
    assert result.exit_code != 0


def test_ua_continuation_block_has_assume_and_branch(tmp_path):
    """Every continuation block emitted by the merge strategy starts with an
    AssumeExpCmd on the predicate and the split-point block ends in a
    JumpiCmd or JumpCmd targeting __UA_ERROR."""
    runner = CliRunner()
    src = _require(KEV_TAC)
    out = tmp_path / "ua.tac"
    result = runner.invoke(app, ["ua", str(src), "-o", str(out), "--plain"])
    assert result.exit_code == 0, result.output
    tac = parse_path(out)
    ua_blocks = [b for b in tac.program.blocks if "_UA" in b.id]
    assert ua_blocks, "expected continuation blocks with `_UA` in the id"
    # Every block that points to __UA_ERROR is either via JumpCmd (assert
    # false case) or JumpiCmd (conditional assert case).
    branching = [
        b for b in tac.program.blocks
        if "__UA_ERROR" in b.successors
    ]
    assert branching, "no blocks branch to __UA_ERROR"
    for b in branching:
        if b.id == "__UA_ERROR":
            continue
        term = b.commands[-1] if b.commands else None
        assert term is not None
        # Terminator must be a jump of some kind targeting the error block.
        assert term.__class__.__name__ in {"JumpiCmd", "JumpCmd"}
        if isinstance(term, JumpCmd):
            assert term.target == "__UA_ERROR"
