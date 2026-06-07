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


def test_rw_purify_div_enables_r4a():
    """R4a is off by default; `--purify-div` turns it on."""
    runner = CliRunner()
    src = _require_target(TARGET_TAC)
    default = runner.invoke(app, ["rw", str(src), "--plain", "--report"])
    enabled = runner.invoke(app, ["rw", str(src), "--plain", "--report", "--purify-div"])
    assert default.exit_code == 0 and enabled.exit_code == 0
    # R4a appears only in the opt-in run.
    assert "R4a:" not in default.output
    assert "R4a:" in enabled.output or "t_div_" in enabled.output
    # Other rules still fire in both runs.
    assert "N1:" in default.output
    assert "R6:" in default.output


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


def test_rw_purify_ite_output_round_trips(tmp_path):
    """Default `--purify-ite` run produces output that re-parses cleanly."""
    runner = CliRunner()
    src = _require_target(TARGET_TAC)
    out = tmp_path / "rw_ite.tac"
    result = runner.invoke(app, ["rw", str(src), "-o", str(out), "--plain"])
    assert result.exit_code == 0, result.output
    reparsed = parse_path(out)
    assert reparsed.program.blocks


# Inline TAC fixture: a single Ite with a non-trivial Eq cond, designed so
# ITE_PURIFY fires once and the resulting TB def has no duplicate to be
# folded away by the late CSE pass. Used as the self-contained regression
# for the program-passthrough bug where ITE_PURIFY's hits were reported
# but its emitted TB defs were discarded by the late-CSE loop.
_PURIFY_REGRESSION_TAC = """TACSymbolTable {
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
\tBlock 0_0_0_0_0_0 Succ [] {
\t\tAssignHavocCmd R0
\t\tAssignExpCmd R1 Ite(Eq(R0 0x5) 0x1 0x2)
\t\tAssertCmd Lt(R1 0xff) "stay-alive"
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""


def test_rw_ite_purify_hits_actually_land_in_output(tmp_path):
    """Regression: ITE_PURIFY's TB<N> defs must survive into the emitted
    .tac. Previously the CLI's post-DCE loop seeded its first CSE pass
    from the pre-purify ``program`` variable, so the purify phase's
    output was silently discarded by ``_merge_phases`` — ``--report``
    still showed ITE_PURIFY hits but no TB defs reached the writer.

    Self-contained input: a single ``Ite(Eq(R0, 0x5), 0x1, 0x2)`` whose
    cond ITE_PURIFY will name. With one occurrence there is nothing for
    late CSE to fold, so the TB def must appear verbatim in the output.
    """
    runner = CliRunner()
    src = tmp_path / "src.tac"
    src.write_text(_PURIFY_REGRESSION_TAC)
    out = tmp_path / "rw.tac"
    result = runner.invoke(
        app, ["rw", str(src), "-o", str(out), "--plain", "--report"]
    )
    assert result.exit_code == 0, result.output
    assert "ITE_PURIFY:" in result.output, "ITE_PURIFY did not fire on the fixture"
    text = out.read_text()
    # The TB-named bool def must be present in the symbol table and as
    # an AssignExpCmd; the Ite must reference the named cond.
    assert "TB0:bool" in text or "TB1:bool" in text, (
        "ITE_PURIFY hit but no TB<N>:bool symbol declaration in output:\n"
        + text
    )
    assert "AssignExpCmd TB" in text, (
        "ITE_PURIFY hit but no AssignExpCmd TB<N> def in output:\n" + text
    )
    # Output must round-trip — paranoia, the writer must not lose the
    # new symbol along the way.
    reparsed = parse_path(out)
    assert reparsed.program.blocks


def test_rw_ite_purify_disabled_emits_no_tb_in_output(tmp_path):
    """Companion to ``test_rw_ite_purify_hits_actually_land_in_output``:
    with ``--no-purify-ite``, no TB defs must appear. Pins the
    flag's negative direction so a default-flip can't silently
    re-enable purification."""
    runner = CliRunner()
    src = tmp_path / "src.tac"
    src.write_text(_PURIFY_REGRESSION_TAC)
    out = tmp_path / "rw.tac"
    result = runner.invoke(
        app, ["rw", str(src), "-o", str(out), "--plain", "--no-purify-ite"]
    )
    assert result.exit_code == 0, result.output
    text = out.read_text()
    assert "TB0" not in text and "TB1" not in text, (
        "ITE_PURIFY disabled but TB<N> appeared in output:\n" + text
    )


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


_FOLD_CHAIN_TAC = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tX:bv256\n\tQ:bv256\n\tB:bool\n\tP:bool
}
Program {
\tBlock e Succ [] {
\t\tAssignHavocCmd X
\t\tAssumeExpCmd Le(X 0xffffffffffffffffffffffffffffffff)
\t\tAssignHavocCmd P
\t\tAssignExpCmd Q Div(X 0x10000000000000000)
\t\tAssignExpCmd B LOr(Eq(IntSub(0x10000000000000000 Q) 0x0) P)
\t\tAssumeExpCmd B
\t\tAssertCmd false
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""


def test_rw_post_r4_fold_chain_completes_in_one_run(tmp_path):
    """The infeasible-disjunct chain (EqSubZero -> R4 window ->
    CmpRangeFold vs the dominating assume -> LOr prune) completes in
    a single ``ctac rw`` invocation: ``(2^64 -int Q) == 0`` with
    ``Q = X / 2^64`` and ``assume X <= 2^128-1`` requires
    ``X >= 2^128`` — false — so the disjunct drops and ``B = P``.
    Before the post-R4 fold loop, the window emitted by the final
    phase was terminal output and the prune needed a second run."""
    runner = CliRunner()
    src = tmp_path / "chain.tac"
    src.write_text(_FOLD_CHAIN_TAC)
    out = tmp_path / "chain.rw.htac"
    result = runner.invoke(app, ["rw", str(src), "-o", str(out), "--plain"])
    assert result.exit_code == 0, result.output
    text = out.read_text()
    assert "B = P" in text
    # The Div def and the window arithmetic are gone with the disjunct.
    assert "Q" not in text


def test_rw_post_r4_fold_output_is_fold_fixpoint(tmp_path):
    """A second ``ctac rw`` run on the fold-loop's output finds no
    FOLD work (the not-a-fixpoint gap was R4's terminal emit feeding
    CmpRangeFold/bool folds only on re-run). Substitution-rule
    residue (CP aliasing the collapsed ``B = P`` through the assume)
    is outside the fold-only contract and acceptable."""
    runner = CliRunner()
    src = tmp_path / "chain.tac"
    src.write_text(_FOLD_CHAIN_TAC)
    first = tmp_path / "first.tac"
    result = runner.invoke(app, ["rw", str(src), "-o", str(first), "--plain"])
    assert result.exit_code == 0, result.output
    rerun = runner.invoke(
        app, ["rw", str(first), "--plain", "--report"]
    )
    assert rerun.exit_code == 0, rerun.output
    fold_rules = (
        "R4:", "CmpRangeFold:", "BOOL_FOLD:", "BoolAbsorb:",
        "EqSubZero:", "EqFold:", "EqReflexive:", "LAndEqConstPrune:",
    )
    for name in fold_rules:
        assert name not in rerun.output, rerun.output
