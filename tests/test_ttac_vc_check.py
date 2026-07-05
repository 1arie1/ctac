import os
import shutil
import subprocess

import pytest
from typer.testing import CliRunner

import ttac_fixtures as fx
from ctac.solver.smt2 import parse as parse_smt2
from ctac.ttac import parse_program
from ctac.ttac.analysis import infer_types
from ctac.ttac.cli import app
from ctac.ttac.errors import VcCheckError
from ctac.ttac.lean import generate_vc_check
from ctac.ttac.lean.naming import build_numbering
from ctac.ttac.lean.vc import (
    build_vc_symbols,
    render_top,
    transpile_vc,
)
from ctac.ttac.lean.vc_expected import (
    expected_map_defs,
    expected_vc,
    precheck_diff,
)
from ctac.ttac.vcgen import generate_vc

runner = CliRunner()


def _write(tmp_path, src, name="prog.ttac"):
    f = tmp_path / name
    f.write_text(src)
    return str(f)


def _symbols(src):
    program = parse_program(src)
    types = infer_types(program)
    numbering = build_numbering(program, types)
    return program, numbering, types


DECLS = """\
(declare-const x Int)
(declare-const c Bool)
(declare-const BLK_pos Bool)
(declare-const y1 Int)
(declare-const BLK_neg Bool)
(declare-const y2 Int)
(declare-const BLK_join Bool)
(declare-const y Int)
(declare-const ok Bool)
(declare-const BLK_EXIT Bool)
"""


def _transpile(body, decls=DECLS):
    program, numbering, types = _symbols(fx.SCALAR_DIAMOND)
    smt = parse_smt2(f"{decls}(assert {body})\n(check-sat)\n")
    syms, errs = build_vc_symbols(program, numbering, types, smt)
    assert errs == []
    asserts, _map_defs, errs = transpile_vc(smt, syms)
    if errs:
        return None, errs
    return render_top(asserts[0].term), []


# --- transpiler units ---


def test_transpile_ops():
    cases = {
        "(= y (+ x 1))": ".eqI (.var .int 3) (.add (.var .int 0) (.litI 1))",
        "(= y (- x y1))": ".eqI (.var .int 3) (.sub (.var .int 0) (.var .int 1))",
        "(= y (* x x))": ".eqI (.var .int 3) (.mul (.var .int 0) (.var .int 0))",
        "(= y (div x y1))":
            ".eqI (.var .int 3) (.div (.var .int 0) (.var .int 1))",
        "(<= x y)": ".le (.var .int 0) (.var .int 3)",
        "(< x y)": ".lt (.var .int 0) (.var .int 3)",
        "(= c ok)": ".eqB (.var .bool 0) (.var .bool 1)",
        "(not c)": ".not (.var .bool 0)",
        "(=> BLK_pos c)": ".imp (.blk 1) (.var .bool 0)",
        "(= y (ite c x y1))":
            ".eqI (.var .int 3) (.ite (.var .bool 0) (.var .int 0) (.var .int 1))",
        "(ite c ok true)": ".ite (.var .bool 0) (.var .bool 1) (.litB true)",
    }
    for body, want in cases.items():
        got, errs = _transpile(body)
        assert errs == [], (body, errs)
        assert got == want, body


def test_transpile_negative_literal():
    got, _ = _transpile("(= x (- 5))")
    assert got == ".eqI (.var .int 0) (.litI (-5))"
    got, _ = _transpile("(= x (- 0 x))")
    assert got == ".eqI (.var .int 0) (.sub (.litI 0) (.var .int 0))"
    _, errs = _transpile("(= x (- y))")
    assert any("unary minus" in e for e in errs)


def test_transpile_nary_fold_right():
    got, _ = _transpile("(and c ok (not c))")
    assert got == ".and (.var .bool 0) (.and (.var .bool 1) (.not (.var .bool 0)))"
    got, _ = _transpile("(or c ok BLK_EXIT)")
    assert got == ".or (.var .bool 0) (.or (.var .bool 1) (.blk 4))"


def test_transpile_eq_sort_mismatch():
    _, errs = _transpile("(= x c)")
    assert any("different sorts" in e for e in errs)


def test_transpile_unsupported_operator():
    _, errs = _transpile("(select x c)")
    assert any("unsupported operator 'select'" in e for e in errs)


def test_transpile_block_var_mapping():
    got, _ = _transpile("BLK_EXIT")
    assert got == ".blk 4"
    got, _ = _transpile("BLK_entry")
    assert got == ".blk 0"


# --- symbol table / statement triage ---


def test_unknown_const_rejected():
    program, numbering, types = _symbols(fx.SCALAR_DIAMOND)
    smt = parse_smt2("(declare-const zzz Int)\n(assert true)\n")
    _, errs = build_vc_symbols(program, numbering, types, smt)
    assert any("unknown constant 'zzz'" in e for e in errs)


def test_sort_mismatch_rejected():
    program, numbering, types = _symbols(fx.SCALAR_DIAMOND)
    smt = parse_smt2("(declare-const c Int)\n(assert true)\n")
    _, errs = build_vc_symbols(program, numbering, types, smt)
    assert any("bool register but declared Int" in e for e in errs)


def test_declare_fun_unknown_map_rejected():
    # declare-fun is a bytemap declaration now; on a scalar program any
    # such name is unknown, and non-(Int)Int shapes are rejected.
    program = parse_program(fx.SCALAR_DIAMOND)
    smt2 = "(declare-fun M (Int) Int)\n(assert true)\n(check-sat)\n"
    with pytest.raises(VcCheckError) as exc:
        generate_vc_check(program, smt2, module_name="P")
    assert any("unknown function 'M'" in e for e in exc.value.errors)
    smt2 = "(declare-fun f (Int Int) Bool)\n(assert true)\n(check-sat)\n"
    with pytest.raises(VcCheckError) as exc:
        generate_vc_check(program, smt2, module_name="P")
    assert any(
        "only (Int) Int bytemap declarations" in e for e in exc.value.errors
    )


# --- program-side validation ---


def _gen_errors(src, smt2="(assert true)\n"):
    with pytest.raises(VcCheckError) as exc:
        generate_vc_check(parse_program(src), smt2, module_name="P")
    return exc.value.errors


def test_two_asserts_rejected_with_ua_hint():
    errs = _gen_errors(fx.TWO_ASSERTS)
    assert any("run `ttac ua" in e for e in errs)


def test_assert_not_last_rejected():
    src = """\
entry:
  a := havoc
  ok := 0 <= a
  assert ok
  b := a + 1
  halt
"""
    errs = _gen_errors(src)
    assert any("not the last command" in e for e in errs)


def test_no_assert_rejected():
    src = "entry:\n  a := havoc\n  b := a + 1\n  halt\n"
    errs = _gen_errors(src)
    assert any("no assert" in e for e in errs)


def test_backward_edge_rejected():
    errs = _gen_errors(
        """\
entry:
  c := havoc
  if c goto b2 else b1

b2:
  ok2 := c == c
  goto b3

b1:
  goto b2

b3:
  assert ok2
  halt
"""
    )
    assert any("backward edge b1 -> b2" in e for e in errs)


def test_unreachable_block_rejected():
    src = """\
entry:
  a := havoc
  ok := 0 <= a
  assert ok
  halt

orphan:
  halt
"""
    errs = _gen_errors(src)
    assert any("unreachable" in e for e in errs)


# --- golden e2e on the diamond ---


def _diamond_result(**kwargs):
    program = parse_program(fx.SCALAR_DIAMOND)
    smt_text = generate_vc(program).smt_text
    return generate_vc_check(
        program, smt_text, module_name="Diamond", **kwargs
    ), smt_text


def test_diamond_vc_lines_golden():
    res, _ = _diamond_result()
    assert res.n_asserts == 13
    text = res.vc_text
    assert ".eqB (.var .bool 0) (.le (.litI 0) (.var .int 0))," in text
    assert (".eqI (.var .int 3) (.ite (.blk 1) (.var .int 1) (.var .int 2))," in text)
    assert (".imp (.blk 4) (.and (.blk 3) (.not (.var .bool 1)))," in text)
    assert text.rstrip().endswith("end Diamond.Vc")
    assert text.count(".imp (.blk 3) (.or (.blk 1) (.blk 2)),") == 2
    assert "theorem vc_ok : Ttac.checkVC Deep.prog Vc.vc = true := by" in res.check_text
    assert "native_decide" in res.check_text


def test_diamond_precheck_clean():
    res, _ = _diamond_result()
    assert res.mismatches == ()


def test_precheck_clean_on_scalar_fixtures():
    for src in (fx.SCALAR_DIAMOND, fx.SCALAR_STRAIGHT):
        program = parse_program(src)
        smt_text = generate_vc(program).smt_text
        res = generate_vc_check(program, smt_text, module_name="P")
        assert res.mismatches == (), src


def test_precheck_catches_tampering():
    program = parse_program(fx.SCALAR_DIAMOND)
    smt_text = generate_vc(program).smt_text
    tampered = smt_text.replace("(<= 0 y)", "(< 0 y)")
    res = generate_vc_check(program, tampered, module_name="P")
    kinds = {m.kind for m in res.mismatches}
    assert "unexpected-assert" in kinds
    assert "missing-assert" in kinds


def test_precheck_catches_dropped_assert():
    program = parse_program(fx.SCALAR_DIAMOND)
    smt_text = generate_vc(program).smt_text
    tampered = smt_text.replace("(assert BLK_EXIT)\n", "")
    res = generate_vc_check(program, tampered, module_name="P")
    assert any(m.kind == "missing-assert" for m in res.mismatches)


def test_expected_mirror_matches_transpiled_multiset():
    program, numbering, types = _symbols(fx.SCALAR_DIAMOND)
    smt = parse_smt2(generate_vc(program).smt_text)
    syms, _ = build_vc_symbols(program, numbering, types, smt)
    asserts, map_defs, errs = transpile_vc(smt, syms)
    assert errs == []
    expected = expected_vc(program, numbering, types)
    expected_defs = expected_map_defs(program, numbering, types)
    assert precheck_diff(asserts, expected, map_defs, expected_defs) == ()


# --- bytemaps ---


def _bytemap_result(**kwargs):
    program = parse_program(fx.BYTEMAP_PHI)
    smt_text = generate_vc(program).smt_text
    return generate_vc_check(
        program, smt_text, module_name="BytemapPhi", **kwargs
    ), smt_text


def test_bytemap_phi_vc_lines_golden():
    res, _ = _bytemap_result()
    text = res.vc_text
    # selects transpile inside scalar constraints
    assert (".imp (.blk 3) (.eqI (.var .int 2) "
            "(.select (.var .map 3) (.var .int 0)))," in text)
    # stores and the map phi become mapDefs entries
    assert "(1, .store (.var .map 0) (.var .int 0) (.var .int 1))," in text
    assert "(2, .store (.var .map 0) (.var .int 0) (.var .int 1))," in text
    assert "(3, .ite (.blk 1) (.var .map 1) (.var .map 2))]" in text
    assert "def vc : Ttac.Vc.VC where" in text
    # the map-phi AMO clause is a plain constraint
    assert ".or (.not (.blk 1)) (.not (.blk 2))," in text


def test_bytemap_precheck_clean():
    res, _ = _bytemap_result()
    assert res.mismatches == ()


def test_scalar_program_empty_mapdefs():
    res, _ = _diamond_result()
    assert "mapDefs := []" in res.vc_text


def test_tampered_store_caught_by_precheck():
    program = parse_program(fx.BYTEMAP_PHI)
    smt_text = generate_vc(program).smt_text
    tampered = smt_text.replace(
        "(define-fun M1 ((idx Int)) Int (ite (= idx i) v (M idx)))",
        "(define-fun M1 ((idx Int)) Int (ite (= idx v) i (M idx)))",
    )
    assert tampered != smt_text
    res = generate_vc_check(program, tampered, module_name="BytemapPhi")
    kinds = {m.kind for m in res.mismatches}
    assert "unexpected-map-def" in kinds


def test_alias_define_fun_transpiles():
    src = """\
entry:
  M := havoc
  M2 := M
  x := M2[0]
  ok := x == x
  assert ok
  halt
"""
    program = parse_program(src)
    res = generate_vc_check(
        program, generate_vc(program).smt_text, module_name="Alias"
    )
    assert "(1, .var .map 0)" in res.vc_text
    assert res.mismatches == ()


def test_kernel_flag():
    res, _ = _diamond_result(kernel=True)
    assert "by\n  decide" in res.check_text
    assert "native_decide" not in res.check_text


def test_determinism():
    a, _ = _diamond_result()
    b, _ = _diamond_result()
    assert a.vc_text == b.vc_text
    assert a.deep_text == b.deep_text


# --- CLI ---


def _diamond_files(tmp_path):
    ttac = _write(tmp_path, fx.SCALAR_DIAMOND)
    smt_text = generate_vc(parse_program(fx.SCALAR_DIAMOND)).smt_text
    smt2 = tmp_path / "prog.smt2"
    smt2.write_text(smt_text)
    return ttac, str(smt2)


def test_cli_writes_project(tmp_path):
    ttac, smt2 = _diamond_files(tmp_path)
    out = tmp_path / "out"
    result = runner.invoke(
        app, ["vc-check", ttac, smt2, "-o", str(out), "--no-build", "--plain"]
    )
    assert result.exit_code == 0, result.output
    assert (out / "Prog" / "Deep.lean").is_file()
    assert (out / "Prog" / "Vc.lean").is_file()
    assert (out / "Prog" / "Check.lean").is_file()
    assert (out / "Ttac" / "VcCheck.lean").is_file()
    assert "generated (not validated)" in result.output


def test_cli_missing_smt2(tmp_path):
    ttac = _write(tmp_path, fx.SCALAR_DIAMOND)
    result = runner.invoke(
        app,
        ["vc-check", ttac, str(tmp_path / "nope.smt2"), "-o", str(tmp_path / "o"),
         "--no-build", "--plain"],
    )
    assert result.exit_code == 2


def test_cli_validation_error(tmp_path):
    ttac = _write(tmp_path, fx.TWO_ASSERTS)
    smt2 = tmp_path / "x.smt2"
    smt2.write_text("(assert true)\n")
    result = runner.invoke(
        app,
        ["vc-check", ttac, str(smt2), "-o", str(tmp_path / "o"),
         "--no-build", "--plain"],
    )
    assert result.exit_code == 1
    assert "ttac ua" in result.output


def test_cli_force(tmp_path):
    ttac, smt2 = _diamond_files(tmp_path)
    out = tmp_path / "out"
    out.mkdir()
    (out / "junk").write_text("x")
    args = ["vc-check", ttac, smt2, "-o", str(out), "--no-build", "--plain"]
    assert runner.invoke(app, args).exit_code == 2
    assert runner.invoke(app, [*args, "--force"]).exit_code == 0


# --- integration (opt-in) ---


@pytest.mark.skipif(shutil.which("lake") is None, reason="lake not on PATH")
@pytest.mark.skipif(not os.environ.get("CTAC_LEAN_TESTS"), reason="set CTAC_LEAN_TESTS=1")
def test_lake_build_validates_diamond(tmp_path):
    ttac, smt2 = _diamond_files(tmp_path)
    out = tmp_path / "out"
    result = runner.invoke(
        app, ["vc-check", ttac, smt2, "-o", str(out), "--no-build", "--plain"]
    )
    assert result.exit_code == 0
    subprocess.run(["lake", "exe", "cache", "get"], cwd=out, check=True, timeout=1800)
    build = subprocess.run(
        ["lake", "build"], cwd=out, capture_output=True, text=True, timeout=1800
    )
    assert build.returncode == 0, build.stdout + build.stderr


@pytest.mark.skipif(shutil.which("lake") is None, reason="lake not on PATH")
@pytest.mark.skipif(not os.environ.get("CTAC_LEAN_TESTS"), reason="set CTAC_LEAN_TESTS=1")
def test_lake_build_validates_bytemap_phi(tmp_path):
    ttac = _write(tmp_path, fx.BYTEMAP_PHI)
    smt_text = generate_vc(parse_program(fx.BYTEMAP_PHI)).smt_text
    smt2 = tmp_path / "prog.smt2"
    smt2.write_text(smt_text)
    out = tmp_path / "out"
    result = runner.invoke(
        app,
        ["vc-check", ttac, str(smt2), "-o", str(out), "--no-build", "--plain"],
    )
    assert result.exit_code == 0
    subprocess.run(["lake", "exe", "cache", "get"], cwd=out, check=True, timeout=1800)
    build = subprocess.run(
        ["lake", "build"], cwd=out, capture_output=True, text=True, timeout=1800
    )
    assert build.returncode == 0, build.stdout + build.stderr


@pytest.mark.skipif(shutil.which("lake") is None, reason="lake not on PATH")
@pytest.mark.skipif(not os.environ.get("CTAC_LEAN_TESTS"), reason="set CTAC_LEAN_TESTS=1")
def test_lake_build_rejects_tampered_map_def(tmp_path):
    ttac = _write(tmp_path, fx.BYTEMAP_PHI)
    smt_text = generate_vc(parse_program(fx.BYTEMAP_PHI)).smt_text
    smt2 = tmp_path / "bad.smt2"
    smt2.write_text(smt_text.replace(
        "(define-fun M1 ((idx Int)) Int (ite (= idx i) v (M idx)))",
        "(define-fun M1 ((idx Int)) Int (ite (= idx v) i (M idx)))",
    ))
    out = tmp_path / "out"
    result = runner.invoke(
        app,
        ["vc-check", ttac, str(smt2), "-o", str(out), "--no-build",
         "--no-precheck", "--plain"],
    )
    assert result.exit_code == 0
    subprocess.run(["lake", "exe", "cache", "get"], cwd=out, check=True, timeout=1800)
    build = subprocess.run(
        ["lake", "build"], cwd=out, capture_output=True, text=True, timeout=1800
    )
    assert build.returncode != 0


@pytest.mark.skipif(shutil.which("lake") is None, reason="lake not on PATH")
@pytest.mark.skipif(not os.environ.get("CTAC_LEAN_TESTS"), reason="set CTAC_LEAN_TESTS=1")
def test_lake_build_rejects_tampered_vc(tmp_path):
    ttac = _write(tmp_path, fx.SCALAR_DIAMOND)
    smt_text = generate_vc(parse_program(fx.SCALAR_DIAMOND)).smt_text
    smt2 = tmp_path / "bad.smt2"
    smt2.write_text(smt_text.replace("(<= 0 y)", "(< 0 y)"))
    out = tmp_path / "out"
    result = runner.invoke(
        app,
        ["vc-check", ttac, str(smt2), "-o", str(out), "--no-build",
         "--no-precheck", "--plain"],
    )
    assert result.exit_code == 0
    subprocess.run(["lake", "exe", "cache", "get"], cwd=out, check=True, timeout=1800)
    build = subprocess.run(
        ["lake", "build"], cwd=out, capture_output=True, text=True, timeout=1800
    )
    assert build.returncode != 0
