"""End-to-end tests for `ctac rw` on the klend target TAC."""

from __future__ import annotations

from pathlib import Path

import pytest
from typer.testing import CliRunner

from ctac.parse import parse_path
from ctac.tool.main import app

TARGET_TAC = Path(
    "claude/emv-3-certora-20-Apr--10-31/outputs/"
    "PresolverRule-rule_withdraw_amounts_summary_sound-#assert_6.tac"
)


def _require_target(path: Path) -> Path:
    if not path.is_file():
        pytest.skip(f"target TAC not present: {path}")
    return path


def test_rw_stdout_on_target(tmp_path):
    runner = CliRunner()
    src = _require_target(TARGET_TAC)
    result = runner.invoke(app, ["rw", str(src), "--plain"])
    assert result.exit_code == 0, result.output
    # PP output begins with block header lines.
    assert "0_0_0_0_0_0:" in result.output


def test_rw_report_counts_on_target():
    runner = CliRunner()
    src = _require_target(TARGET_TAC)
    result = runner.invoke(app, ["rw", str(src), "--plain", "--report"])
    assert result.exit_code == 0, result.output
    assert "rule_hits:" in result.output
    # N1 and R1 should both fire — the target has the shifted-BWAnd pattern with bounds.
    assert "N1:" in result.output
    assert "R1:" in result.output


def test_rw_tac_output_roundtrips(tmp_path):
    runner = CliRunner()
    src = _require_target(TARGET_TAC)
    out = tmp_path / "rw.tac"
    result = runner.invoke(app, ["rw", str(src), "-o", str(out), "--plain"])
    assert result.exit_code == 0, result.output
    assert out.is_file()
    tac = parse_path(out)
    assert tac.program.blocks, "parsed empty program from rewrite output"


def test_rw_htac_output_written(tmp_path):
    runner = CliRunner()
    src = _require_target(TARGET_TAC)
    out = tmp_path / "rw.htac"
    result = runner.invoke(app, ["rw", str(src), "-o", str(out), "--plain"])
    assert result.exit_code == 0, result.output
    text = out.read_text()
    assert "0_0_0_0_0_0:" in text
    # pp format uses `=` for assignments.
    assert " = " in text
