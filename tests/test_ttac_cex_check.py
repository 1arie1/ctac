"""cex-check: certify a solver `sat` by denotational replay in Lean.

The model transpiles into a seed state; `denot` is computable, so the
generated project proves `(denot prog seed).blks EXIT = true` by
`native_decide` and concludes `¬ Safe_denot prog` via
`not_safe_denot_of_seed`. The Lean `DiamondCex` golden pins the
checker side; these tests pin the seed transpilation and module shapes.
"""

import os
import shutil
import subprocess

import pytest
from typer.testing import CliRunner

import ttac_fixtures as fx
from ctac.ttac import parse_program
from ctac.ttac.cli import app
from ctac.ttac.lean.vccheck import generate_cex_check

runner = CliRunner()

UNSAFE_DIAMOND = fx.SCALAR_DIAMOND.replace("y1 := x + 1", "y1 := x - 1")

# The seed x = 0 takes the pos branch (0 <= 0) into y = y1 = -1.
DIAMOND_MODEL = """\
sat
(
  (define-fun x () Int 0)
  (define-fun c () Bool true)
  (define-fun y1 () Int (- 1))
  (define-fun y2 () Int 0)
  (define-fun y () Int (- 1))
  (define-fun ok () Bool false)
)
"""


def _cex(src=UNSAFE_DIAMOND, model=DIAMOND_MODEL, module_name="Diamond"):
    return generate_cex_check(
        parse_program(src), model, module_name=module_name
    )


def test_cex_seed_module_shape():
    res = _cex()
    text = res.cex_text
    assert "def seed : Ttac.State where" in text
    assert "| .int => fun x => match x with" in text
    # int reg 0 = x seeded from the model
    assert "| 0 => 0" in text
    # negative model values parenthesized (int regs 1/3 = y1/y)
    assert "| 1 => (-1)" in text
    assert "| .bool => fun x => match x with" in text
    assert "| 0 => true" in text
    assert "blks := fun _ => false" in text
    assert res.missing == ()


def test_cex_check_module_shape():
    res = _cex()
    text = res.check_text
    assert (
        "(Ttac.denot Deep.prog Cex.seed).blks Deep.prog.blocks.length = true"
        in text
    )
    assert "native_decide" in text
    assert "Ttac.not_safe_denot_of_seed Cex.seed cex_ok" in text
    assert "¬ Ttac.Safe_denot Deep.prog" in text


def test_cex_partial_model_defaults_and_reports():
    partial = "sat\n(\n  (define-fun x () Int 0)\n)\n"
    res = _cex(model=partial)
    assert "y1" in res.missing
    assert "ok" in res.missing
    # unseeded sorts still render (defaults only)
    assert "| .bool => fun _ => false" in res.cex_text


def test_cex_map_seed_renders_entries():
    model = (
        "sat\n(\n"
        "  (define-fun i () Int 3)\n"
        "  (define-fun v () Int 7)\n"
        "  (define-fun x () Int 7)\n"
        "  (define-fun ok () Bool false)\n"
        "  (define-fun M ((a!0 Int)) Int (ite (= a!0 3) 7 0))\n"
        ")\n"
    )
    src = (
        "entry:\n  M := havoc\n  i := havoc\n  v := havoc\n"
        "  M2 := M[i := v]\n  x := M2[i]\n  ok := x == v\n"
        "  assert ok\n  halt\n"
    )
    res = _cex(src=src, model=model, module_name="Bytemap")
    assert "| .map => fun x => match x with" in res.cex_text
    assert "if i = 3 then 7 else 0" in res.cex_text


def test_cex_check_cli_generates(tmp_path):
    ttac = tmp_path / "prog.ttac"
    ttac.write_text(UNSAFE_DIAMOND)
    model = tmp_path / "model.txt"
    model.write_text(DIAMOND_MODEL)
    out = tmp_path / "out"
    result = runner.invoke(
        app,
        ["cex-check", str(ttac), str(model), "-o", str(out),
         "--no-build", "--plain"],
    )
    assert result.exit_code == 0, result.output
    assert "generated (not certified)" in result.output
    cex_files = list(out.glob("*/Cex.lean"))
    assert cex_files, "no Cex.lean written"
    assert "def seed : Ttac.State where" in cex_files[0].read_text()
    check_files = list(out.glob("*/Check.lean"))
    assert "not_safe_denot_of_seed" in check_files[0].read_text()


def _z3_path():
    try:
        from ctac.solver.z3 import resolve_z3_bin

        return str(resolve_z3_bin(None))
    except FileNotFoundError:
        return None


@pytest.mark.skipif(_z3_path() is None, reason="no z3 binary resolvable")
def test_cex_from_real_z3_model():
    from ctac.smt.runner import run_z3_solver
    from ctac.smt.z3_model import parse_z3_sat_output
    from ctac.ttac.vcgen import generate_vc

    program = parse_program(UNSAFE_DIAMOND)
    vc = generate_vc(program)
    r = run_z3_solver(
        smt_text=vc.smt_text, z3_path=_z3_path(), timeout_seconds=30,
        seed=0, tactic="default", extra_args=[], want_model=True,
    )
    out = parse_z3_sat_output(r.stdout)
    assert out.status == "sat"
    res = generate_cex_check(
        program, out.model_text, module_name="Diamond"
    )
    assert res.missing == ()
    assert "def seed : Ttac.State where" in res.cex_text


@pytest.mark.skipif(shutil.which("lake") is None, reason="lake not on PATH")
@pytest.mark.skipif(
    not os.environ.get("CTAC_LEAN_TESTS"), reason="set CTAC_LEAN_TESTS=1"
)
def test_lake_build_certifies_cex(tmp_path):
    ttac = tmp_path / "prog.ttac"
    ttac.write_text(UNSAFE_DIAMOND)
    model = tmp_path / "model.txt"
    model.write_text(DIAMOND_MODEL)
    out = tmp_path / "out"
    result = runner.invoke(
        app,
        ["cex-check", str(ttac), str(model), "-o", str(out),
         "--no-build", "--plain"],
    )
    assert result.exit_code == 0, result.output
    subprocess.run(["lake", "exe", "cache", "get"], cwd=out, check=True, timeout=1800)
    build = subprocess.run(
        ["lake", "build"], cwd=out, capture_output=True, text=True, timeout=1800
    )
    assert build.returncode == 0, build.stdout + build.stderr


@pytest.mark.skipif(shutil.which("lake") is None, reason="lake not on PATH")
@pytest.mark.skipif(
    not os.environ.get("CTAC_LEAN_TESTS"), reason="set CTAC_LEAN_TESTS=1"
)
def test_lake_build_rejects_non_driving_seed(tmp_path):
    # x = 5 keeps the broken arm harmless (y = 4): EXIT stays unreached,
    # native_decide fails, the certificate does not build.
    ttac = tmp_path / "prog.ttac"
    ttac.write_text(UNSAFE_DIAMOND)
    model = tmp_path / "model.txt"
    model.write_text(DIAMOND_MODEL.replace("(define-fun x () Int 0)",
                                           "(define-fun x () Int 5)"))
    out = tmp_path / "out"
    result = runner.invoke(
        app,
        ["cex-check", str(ttac), str(model), "-o", str(out),
         "--no-build", "--plain"],
    )
    assert result.exit_code == 0, result.output
    subprocess.run(["lake", "exe", "cache", "get"], cwd=out, check=True, timeout=1800)
    build = subprocess.run(
        ["lake", "build"], cwd=out, capture_output=True, text=True, timeout=1800
    )
    assert build.returncode != 0, "a non-driving seed must not certify"
