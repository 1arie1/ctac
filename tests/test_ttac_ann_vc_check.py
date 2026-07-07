"""Annotated vc-check: the denotational `Ttac.Vc.AnnVC` / `checkVCWAnn` path.

The annotator transpiles the same smt2 as the flat path, then files each
assert into the block bucket (CFG / commands) or objective whose encoder
generator contains it. These tests pin the bucketing and the emitted
module shapes; the Lean `checkVCWAnn` + `DiamondAnnVc` golden verify the
checker itself.
"""

import os
import shutil
import subprocess

import pytest
from typer.testing import CliRunner

import ttac_fixtures as fx
from ctac.ttac import parse_program
from ctac.ttac.cli import app
from ctac.ttac.errors import VcCheckError
from ctac.ttac.lean.vccheck import generate_ann_vc_check
from ctac.ttac.vcgen import generate_vc

runner = CliRunner()


def _ann(fixture=fx.SCALAR_DIAMOND, module_name="Diamond"):
    program = parse_program(fixture)
    smt_text = generate_vc(program).smt_text
    return generate_ann_vc_check(program, smt_text, module_name=module_name)


def test_diamond_ann_buckets_completely():
    res = _ann()
    # Every transpiled assert found a block/objective bucket whose generator
    # contains it — nothing left unattributed.
    assert res.unmatched == ()
    assert res.n_asserts == 13


def test_diamond_ann_module_shape():
    res = _ann()
    text = res.vc_text
    assert "def vc : Ttac.Vc.AnnVC where" in text
    assert "perBlock := [" in text
    assert "cfg :=" in text
    assert "cmds := [" in text
    assert "objective :=" in text
    # the entry-block fact (guard folds to true) lands in block 0's commands
    assert ".eqB (.var .bool 0) (.le (.litI 0) (.var .int 0))" in text
    # a join-block CFG constraint lands in a block's cfg bucket
    assert ".imp (.blk 3) (.or (.blk 1) (.blk 2))" in text
    assert text.rstrip().endswith("end Diamond.Vc")


def test_diamond_ann_check_module_is_forward():
    res = _ann()
    assert "Ttac.checkVCWAnn Deep.prog Vc.vc = true" in res.check_text
    assert "Ttac.Vc.AnnVC.Unsat Vc.vc → Deep.prog.Safe" in res.check_text
    assert "Ttac.checkVCWAnn_safe vc_ok" in res.check_text
    assert "native_decide" in res.check_text


def test_bytemap_ann_has_map_defs():
    res = _ann(fx.BYTEMAP_PHI, module_name="Bytemap")
    assert res.unmatched == ()
    assert "maps := [(" in res.vc_text


def test_ann_rejects_alien_assert():
    # An assert the encoder never emits has no block bucket -> the annotator
    # reports it rather than mis-filing it.
    program = parse_program(fx.SCALAR_DIAMOND)
    smt2 = (
        "(declare-const ok Bool)\n(declare-const BLK_join Bool)\n"
        "(assert (=> BLK_join (= ok (< 0 0))))\n(check-sat)\n"
    )
    with pytest.raises(VcCheckError) as exc:
        generate_ann_vc_check(program, smt2, module_name="P")
    assert any("not in any block generator" in e for e in exc.value.errors)


def test_ann_vc_check_cli_generates(tmp_path):
    ttac = tmp_path / "prog.ttac"
    ttac.write_text(fx.SCALAR_DIAMOND)
    smt2 = tmp_path / "vc.smt2"
    smt2.write_text(generate_vc(parse_program(fx.SCALAR_DIAMOND)).smt_text)
    out = tmp_path / "out"
    result = runner.invoke(
        app,
        ["ann-vc-check", str(ttac), str(smt2), "-o", str(out),
         "--no-build", "--plain"],
    )
    assert result.exit_code == 0, result.output
    assert "generated (not validated)" in result.output
    vc_files = list(out.glob("*/Vc.lean"))
    assert vc_files, "no Vc.lean written"
    assert "Ttac.Vc.AnnVC" in vc_files[0].read_text()
    check_files = list(out.glob("*/Check.lean"))
    assert "checkVCWAnn_safe" in check_files[0].read_text()


@pytest.mark.skipif(shutil.which("lake") is None, reason="lake not on PATH")
@pytest.mark.skipif(
    not os.environ.get("CTAC_LEAN_TESTS"), reason="set CTAC_LEAN_TESTS=1"
)
def test_lake_build_validates_ann_vc(tmp_path):
    ttac = tmp_path / "prog.ttac"
    ttac.write_text(fx.SCALAR_DIAMOND)
    smt2 = tmp_path / "vc.smt2"
    smt2.write_text(generate_vc(parse_program(fx.SCALAR_DIAMOND)).smt_text)
    out = tmp_path / "out"
    result = runner.invoke(
        app,
        ["ann-vc-check", str(ttac), str(smt2), "-o", str(out),
         "--no-build", "--plain"],
    )
    assert result.exit_code == 0, result.output
    subprocess.run(["lake", "exe", "cache", "get"], cwd=out, check=True, timeout=1800)
    build = subprocess.run(
        ["lake", "build"], cwd=out, capture_output=True, text=True, timeout=1800
    )
    assert build.returncode == 0, build.stderr
