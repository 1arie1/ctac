"""Test the `ctac rw --simplify-cfg` flag wiring.

The simplify_cfg pass itself has unit tests in test_cfg_simplify.py; this
file exercises the wire-in to the ``ctac rw`` pipeline: the flag toggles
the final CFG-simplification phase, the report surface shows the drop
counts, and the output contains fewer blocks than the no-flag baseline.
"""

from __future__ import annotations

from pathlib import Path

from typer.testing import CliRunner

from ctac.parse import parse_path
from ctac.tool.main import app


_REPO_ROOT = Path(__file__).resolve().parent.parent
_CSB_LEMMA_SRC = (
    _REPO_ROOT / "examples" / "kvault" / "csb_lemma" / "csb_lemma.tac"
)


_SIMPLE_INPUT = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tR:bv256
\tC:bool
}
Program {
\tBlock A Succ [X, Z] {
\t\tAssignExpCmd R 0x1
\t\tAssignExpCmd C true
\t\tJumpiCmd X Z C
\t}
\tBlock X Succ [Y] {
\t\tAnnotationCmd JSON{"k":1}
\t}
\tBlock Y Succ [] {
\t\tAssignExpCmd R 0x2
\t}
\tBlock Z Succ [] {
\t\tAssignExpCmd R 0x3
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""


def test_rw_simplify_cfg_drops_fall_through(tmp_path: Path) -> None:
    """`ctac rw <file> --simplify-cfg` drops the annotation-only X
    block; without the flag X survives the pipeline."""
    src = tmp_path / "in.tac"
    src.write_text(_SIMPLE_INPUT)

    runner = CliRunner()

    # Baseline: no --simplify-cfg
    out_default = tmp_path / "out-default.tac"
    res_default = runner.invoke(
        app, ["rw", str(src), "-o", str(out_default), "--plain"]
    )
    assert res_default.exit_code == 0, res_default.output
    default_ids = [b.id for b in parse_path(out_default).program.blocks]
    assert "X" in default_ids, "without --simplify-cfg, X should still be present"

    # With --simplify-cfg
    out_simp = tmp_path / "out-simp.tac"
    res_simp = runner.invoke(
        app,
        ["rw", str(src), "-o", str(out_simp), "--plain", "--simplify-cfg"],
    )
    assert res_simp.exit_code == 0, res_simp.output
    simp_ids = [b.id for b in parse_path(out_simp).program.blocks]
    assert "X" not in simp_ids, "--simplify-cfg should drop annotation-only X"
    assert len(simp_ids) < len(default_ids)


def test_rw_simplify_cfg_report(tmp_path: Path) -> None:
    """`--simplify-cfg --report` surfaces the drop / rewire counts."""
    src = tmp_path / "in.tac"
    src.write_text(_SIMPLE_INPUT)
    out = tmp_path / "out.tac"

    runner = CliRunner()
    result = runner.invoke(
        app,
        [
            "rw",
            str(src),
            "-o",
            str(out),
            "--plain",
            "--simplify-cfg",
            "--report",
        ],
    )
    assert result.exit_code == 0, result.output
    assert "cfg_simplify: dropped=1" in result.output
    assert "rewires=1" in result.output


def test_rw_no_simplify_cfg_skips_report_line(tmp_path: Path) -> None:
    """Without --simplify-cfg, the report doesn't mention cfg_simplify."""
    src = tmp_path / "in.tac"
    src.write_text(_SIMPLE_INPUT)
    out = tmp_path / "out.tac"

    runner = CliRunner()
    result = runner.invoke(
        app,
        ["rw", str(src), "-o", str(out), "--plain", "--report"],
    )
    assert result.exit_code == 0, result.output
    assert "cfg_simplify:" not in result.output
