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
    # N1 fires — the target has the shifted-BWAnd pattern with bounds, and
    # bit-op canonicalisation is the gateway for everything below.
    assert "N1:" in result.output
    # R6 fires on the ceiling-div chain. Before the chain-recognition phase
    # split, distribution rules pre-empted R6's match; pinning R6 here
    # catches a regression of that interaction.
    assert "R6:" in result.output


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


def test_rw_no_purify_div_disables_r4a():
    """`--no-purify-div` turns off R4a while keeping the rest of the pipeline."""
    runner = CliRunner()
    src = _require_target(TARGET_TAC)
    enabled = runner.invoke(app, ["rw", str(src), "--plain", "--report"])
    disabled = runner.invoke(app, ["rw", str(src), "--plain", "--report", "--no-purify-div"])
    assert enabled.exit_code == 0 and disabled.exit_code == 0
    # R4a appears only in the default run.
    assert "R4a:" in enabled.output or "t_div_" in enabled.output
    assert "R4a:" not in disabled.output
    # Other rules still fire in both runs.
    assert "N1:" in disabled.output
    assert "R6:" in disabled.output


def test_rw_no_purify_ite_disables_tb_naming():
    """`--no-purify-ite` prevents the post-DCE TB<N> naming of Ite conditions."""
    runner = CliRunner()
    src = _require_target(TARGET_TAC)
    enabled = runner.invoke(app, ["rw", str(src), "--plain", "--report"])
    disabled = runner.invoke(app, ["rw", str(src), "--plain", "--report", "--no-purify-ite"])
    assert enabled.exit_code == 0 and disabled.exit_code == 0
    # Default: ITE_PURIFY hits appear.
    assert "ITE_PURIFY:" in enabled.output
    # Disabled: no ITE_PURIFY hits reported.
    assert "ITE_PURIFY:" not in disabled.output


def test_rw_purify_ite_introduces_tb_symbols_in_output(tmp_path):
    """Default `--purify-ite` run emits `TB<N>:bool` declarations in the written TAC."""
    runner = CliRunner()
    src = _require_target(TARGET_TAC)
    out = tmp_path / "rw_ite.tac"
    result = runner.invoke(app, ["rw", str(src), "-o", str(out), "--plain"])
    assert result.exit_code == 0, result.output
    text = out.read_text()
    assert "TB0:bool" in text
    # Re-parses cleanly (round-trip).
    reparsed = parse_path(out)
    assert reparsed.program.blocks


def test_rw_purify_assert_and_assume_flags_accepted():
    """Both flags parse cleanly and don't break the pipeline on the target TAC."""
    runner = CliRunner()
    src = _require_target(TARGET_TAC)
    for args in (
        ["rw", str(src), "--plain", "--report", "--no-purify-assert"],
        ["rw", str(src), "--plain", "--report", "--purify-assume"],
        ["rw", str(src), "--plain", "--report", "--no-purify-assert", "--purify-assume"],
    ):
        result = runner.invoke(app, args)
        assert result.exit_code == 0, (args, result.output)


def test_rw_no_purify_assert_disables_ta_naming():
    runner = CliRunner()
    src = _require_target(TARGET_TAC)
    result = runner.invoke(
        app, ["rw", str(src), "--plain", "--report", "--no-purify-assert"]
    )
    assert result.exit_code == 0, result.output
    assert "PURIFY_ASSERT:" not in result.output


def test_rw_purify_assume_off_by_default():
    runner = CliRunner()
    src = _require_target(TARGET_TAC)
    result = runner.invoke(app, ["rw", str(src), "--plain", "--report"])
    assert result.exit_code == 0, result.output
    assert "PURIFY_ASSUME:" not in result.output


# ---------------------------------------------------------------------------
# --ceildiv-op flag — toggles R6's emit shape between IntCeilDiv (default)
# and the legacy havoc + polynomial-bounds form.

_R6_FIXTURE = Path("tests/rw_eq_fixtures/R6/ceildiv_chain.tac")


def test_rw_ceildiv_op_default_emits_intceildiv(tmp_path):
    """Default ``--ceildiv-op`` flag: R6 emits IntCeilDiv wrapped in
    safe_math_narrow_bv256 instead of havoc + bounds."""
    runner = CliRunner()
    if not _R6_FIXTURE.is_file():
        pytest.skip(f"R6 fixture not present: {_R6_FIXTURE}")
    out = tmp_path / "ceildiv.tac"
    result = runner.invoke(app, ["rw", str(_R6_FIXTURE), "-o", str(out), "--plain"])
    assert result.exit_code == 0, result.output
    text = out.read_text()
    assert "IntCeilDiv" in text
    assert "safe_math_narrow_bv256" in text


def test_rw_no_ceildiv_op_uses_legacy_havoc(tmp_path):
    """``--no-ceildiv-op`` falls back to the legacy emission: a havoc
    on R_ceil + polynomial-bound assumes (R_den * R_ceil >= R_num,
    etc.). No IntCeilDiv anywhere."""
    runner = CliRunner()
    if not _R6_FIXTURE.is_file():
        pytest.skip(f"R6 fixture not present: {_R6_FIXTURE}")
    out = tmp_path / "ceildiv_legacy.tac"
    result = runner.invoke(
        app, ["rw", str(_R6_FIXTURE), "-o", str(out), "--plain", "--no-ceildiv-op"]
    )
    assert result.exit_code == 0, result.output
    text = out.read_text()
    assert "IntCeilDiv" not in text
    # Legacy emission has a havoc on R_ceil + IntMul(R_den, R_ceil) bound.
    assert "AssignHavocCmd R_ceil" in text
    assert "IntMul(R_den" in text
