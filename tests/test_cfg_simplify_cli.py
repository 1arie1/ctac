"""CLI + end-to-end tests for `ctac cfg-simplify`."""

from __future__ import annotations

from pathlib import Path

import pytest
from typer.testing import CliRunner

from ctac.parse import parse_path
from ctac.rw_eq import emit_equivalence_program
from ctac.rw_eq.model import BlockRef
from ctac.tool.main import app
from ctac.transform.cfg_simplify import simplify_cfg


_REPO_ROOT = Path(__file__).resolve().parent.parent
_CSB_LEMMA_RW = _REPO_ROOT / "examples" / "kvault" / "csb_lemma" / "csb_lemma.rw.tac"


_FALL_THROUGH_TAC = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tC:bool
}
Program {
\tBlock A Succ [X, Z] {
\t\tAssignExpCmd C true
\t\tJumpiCmd X Z C
\t}
\tBlock X Succ [Y] {
\t\tAnnotationCmd JSON{"k":1}
\t}
\tBlock Y Succ [] {
\t}
\tBlock Z Succ [] {
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""


def test_cli_writes_simplified_output(tmp_path: Path) -> None:
    """`ctac cfg-simplify in.tac -o out.tac` writes a parsable output
    with fewer blocks; report stats look reasonable."""
    in_path = tmp_path / "in.tac"
    out_path = tmp_path / "out.tac"
    in_path.write_text(_FALL_THROUGH_TAC)

    runner = CliRunner()
    result = runner.invoke(
        app,
        ["cfg-simplify", str(in_path), "-o", str(out_path), "--plain", "--report"],
    )
    assert result.exit_code == 0, result.output
    assert "dropped 1" in result.output
    assert "rewires 1" in result.output
    assert "X -> Y" in result.output

    # Output file parses and has fewer blocks.
    out_tac = parse_path(out_path)
    out_ids = [b.id for b in out_tac.program.blocks]
    assert "X" not in out_ids
    assert out_ids == ["A", "Y", "Z"]


def test_cli_stdout_without_output_flag(tmp_path: Path) -> None:
    """Without `-o`, the simplified TAC streams to stdout."""
    in_path = tmp_path / "in.tac"
    in_path.write_text(_FALL_THROUGH_TAC)

    runner = CliRunner()
    result = runner.invoke(app, ["cfg-simplify", str(in_path), "--plain"])
    assert result.exit_code == 0, result.output
    # Stdout contains the rendered TAC envelope (TACSymbolTable + Program)
    assert "TACSymbolTable" in result.output
    assert "Program" in result.output
    # Dropped block X should NOT appear as a Block declaration
    assert "Block X" not in result.output


def test_cli_report_shows_no_drops_for_clean_file(tmp_path: Path) -> None:
    """A program with no fall-through candidates produces a no-op."""
    clean = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tR:bv256
}
Program {
\tBlock A Succ [] {
\t\tAssignExpCmd R 0x1
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""
    in_path = tmp_path / "in.tac"
    in_path.write_text(clean)

    runner = CliRunner()
    result = runner.invoke(
        app, ["cfg-simplify", str(in_path), "--plain", "--report"]
    )
    assert result.exit_code == 0, result.output
    assert "dropped 0" in result.output


# --- End-to-end on csb_lemma.rw.tac ----------------------------------------


@pytest.mark.skipif(
    not _CSB_LEMMA_RW.exists(),
    reason="csb_lemma.rw.tac fixture not present",
)
def test_csb_lemma_drop_count_and_rw_eq() -> None:
    """Apply the simplifier to the checked-in csb_lemma.rw.tac, then
    run rw-eq's stuttering walker between original and simplified.
    Verify the decomposition matches (dropped → stutter,
    rewired-preds → divergence)."""
    orig_tac = parse_path(_CSB_LEMMA_RW)
    simplified_program, report = simplify_cfg(orig_tac.program)

    # Empirical baseline; tighten if the fixture stabilizes
    assert 4 <= report.n_dropped <= 10, (
        f"unexpected drop count: {report.n_dropped} "
        f"(blocks: {report.dropped_blocks})"
    )
    # Skipped multi-pred set should be small (loop-merge points)
    assert len(report.skipped_multipred) <= 4

    # rw-eq stuttering walker accepts the pair without structural errors.
    result = emit_equivalence_program(orig_tac.program, simplified_program)

    # Each dropped block maps to a stutter in the rw-eq decomp.
    expected_stutter = {BlockRef(id=bid) for bid in report.dropped_blocks}
    assert set(result.stutter_blocks) == expected_stutter

    # Every block that was rewired (had a JumpCmd/JumpiCmd target
    # changed) should appear as a divergence point.
    rewired_preds = {BlockRef(id=pred) for (pred, _, _) in report.rewires}
    assert rewired_preds <= set(result.divergence_points)

    # Sync points exist (the dropped blocks' successors get IN_DEST CHKs).
    assert result.sync_points, "expected at least one sync point"

    # Some IN_DEST CHK asserts were emitted (count > 0 in stutter mode).
    assert result.asserts_emitted >= 1
