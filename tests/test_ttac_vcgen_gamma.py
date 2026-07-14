"""The gamma merge mode: sea_gate-style thin gates in ttac vcgen.

`--merge gamma` re-emits scalar phi definitions as total gammas whose
case guards are branch-condition expressions (thin gated-SSA) with the
classical block-guard chain as the else-tail, and the gamma annotator
serializes the certificates (cases, gate table, valuation table) that
`Ttac.checkVCGAnn` validates. The Lean goldens
(`lean/TtacExamples/GammaVc.lean`) verify the checker; these tests pin
the Python planner, emission, and module shapes.
"""

import os
import shutil
import subprocess

import pytest
from typer.testing import CliRunner

import ttac_fixtures as fx
from ctac.ttac import parse_program
from ctac.ttac.cli import app
from ctac.ttac.lean.vccheck import generate_gann_vc_check
from ctac.ttac.vcgen import generate_vc
from ctac.ttac.vcgen.gamma import plan_gammas

runner = CliRunner()


def test_gamma_diamond_emits_thin_gate():
    res = generate_vc(parse_program(fx.SCALAR_DIAMOND), merge="gamma")
    assert res.gamma_sites == 1
    # the case guard is the branch register; the tail is the classical chain
    assert "(assert (= y (ite c y1 (ite BLK_pos y1 y2))))" in res.smt_text
    assert "(assert (= y (ite BLK_pos y1 y2)))" not in res.smt_text


def test_gamma_default_mode_unchanged():
    prog = parse_program(fx.SCALAR_DIAMOND)
    default = generate_vc(prog)
    phi = generate_vc(prog, merge="phi")
    assert default.smt_text == phi.smt_text
    assert default.gamma_sites == 0
    assert "(assert (= y (ite BLK_pos y1 y2)))" in default.smt_text


def test_gamma_two_region_covers_all_joins():
    res = generate_vc(parse_program(fx.TWO_REGION), merge="gamma")
    assert res.gamma_sites == 3
    # local joins: two-hop guards (region gate AND local branch)
    assert "(assert (= v_a (ite (and c1 c2) v_x (ite BLK_x v_x v_a0))))" in res.smt_text
    assert "(assert (= v_b (ite (and (not c1) c3) v_y (ite BLK_y v_y v_b0))))" in res.smt_text
    # final join: the outer branch alone (the doc's ite(c1, v_a, v_b))
    assert "(assert (= v (ite c1 v_a (ite BLK_a_join v_a v_b))))" in res.smt_text


def test_gamma_crossing_join_falls_back_to_classical():
    prog = parse_program(fx.CROSSING_JOIN)
    res = generate_vc(prog, merge="gamma")
    assert res.gamma_sites == 0
    assert res.smt_text == generate_vc(prog).smt_text


def test_gamma_plan_two_region_gates():
    from ctac.ttac.analysis import infer_types

    prog = parse_program(fx.TWO_REGION)
    plan = plan_gammas(prog, infer_types(prog))
    assert len(plan.sites) == 3
    assert [g.block for g in plan.gates] == ["a", "b"]
    assert all(r.parent is None and r.ctrl == "entry" for g in plan.gates for r in g.rows)
    # the region gates are pinned true/false down their regions
    assert ("c1", True) in plan.val["a_join"]
    assert ("c1", False) in plan.val["b_join"]


def test_gann_module_shapes():
    prog = parse_program(fx.TWO_REGION)
    smt = generate_vc(prog, merge="gamma").smt_text
    res = generate_gann_vc_check(prog, smt, module_name="TwoRegionG")
    assert res.unmatched == ()
    text = res.vc_text
    assert "def vc : Ttac.Vc.GAnnVC where" in text
    assert "tgammas := [(0, { cases := [{ row := { parent := some 0, " in text
    assert (
        "gates := [{ block := 1, rows := [{ parent := none, ctrl := 0, "
        "side := true }] }" in text
    )
    assert "val := [" in text
    assert "Ttac.checkVCGAnn Deep.prog Vc.vc = true" in res.check_text
    assert "Ttac.checkVCGAnn_safe vc_ok" in res.check_text


def test_gamma_vcgen_cli(tmp_path):
    ttac = tmp_path / "prog.ttac"
    ttac.write_text(fx.SCALAR_DIAMOND)
    out = tmp_path / "vc.smt2"
    result = runner.invoke(
        app, ["vcgen", str(ttac), "--merge", "gamma", "-o", str(out), "--plain"]
    )
    assert result.exit_code == 0, result.output
    assert "gamma merge applied at 1 phi site(s)" in result.output
    assert "(ite c y1" in out.read_text()


def test_gamma_ann_vc_check_cli_generates(tmp_path):
    ttac = tmp_path / "prog.ttac"
    ttac.write_text(fx.SCALAR_DIAMOND)
    smt2 = tmp_path / "vc.smt2"
    smt2.write_text(
        generate_vc(parse_program(fx.SCALAR_DIAMOND), merge="gamma").smt_text
    )
    out = tmp_path / "out"
    result = runner.invoke(
        app,
        ["ann-vc-check", str(ttac), str(smt2), "-o", str(out),
         "--merge", "gamma", "--no-build", "--plain"],
    )
    assert result.exit_code == 0, result.output
    vc_files = list(out.glob("*/Vc.lean"))
    assert vc_files, "no Vc.lean written"
    assert "Ttac.Vc.GAnnVC" in vc_files[0].read_text()
    check_files = list(out.glob("*/Check.lean"))
    assert "checkVCGAnn_safe" in check_files[0].read_text()


@pytest.mark.skipif(shutil.which("lake") is None, reason="lake not on PATH")
@pytest.mark.skipif(
    not os.environ.get("CTAC_LEAN_TESTS"), reason="set CTAC_LEAN_TESTS=1"
)
@pytest.mark.parametrize("fixture", [fx.SCALAR_DIAMOND, fx.TWO_REGION])
def test_lake_build_validates_gamma_vc(tmp_path, fixture):
    ttac = tmp_path / "prog.ttac"
    ttac.write_text(fixture)
    smt2 = tmp_path / "vc.smt2"
    smt2.write_text(generate_vc(parse_program(fixture), merge="gamma").smt_text)
    out = tmp_path / "out"
    result = runner.invoke(
        app,
        ["ann-vc-check", str(ttac), str(smt2), "-o", str(out),
         "--merge", "gamma", "--no-build", "--plain"],
    )
    assert result.exit_code == 0, result.output
    subprocess.run(["lake", "exe", "cache", "get"], cwd=out, check=True, timeout=1800)
    build = subprocess.run(
        ["lake", "build"], cwd=out, capture_output=True, text=True, timeout=1800
    )
    assert build.returncode == 0, build.stderr
