import os
import shutil
import subprocess

import pytest
from typer.testing import CliRunner

import ttac_fixtures as fx
from ctac.ttac import parse_program
from ctac.ttac.analysis import infer_types
from ctac.ttac.cli import app
from ctac.ttac.errors import LeanGenError
from ctac.ttac.lean import generate_lean, validate_for_lean
from ctac.ttac.lean.liveness import block_liveness
from ctac.ttac.lean.naming import (
    build_numbering,
    lean_ident,
    module_name_for,
)

runner = CliRunner()


def _write(tmp_path, src):
    f = tmp_path / "prog.ttac"
    f.write_text(src)
    return str(f)


def _gen(src, name="Prog"):
    return generate_lean(parse_program(src), module_name=name)


# --- numbering ---


def test_numbering_first_def_order_separate_counters():
    program = parse_program(fx.SCALAR_DIAMOND)
    num = build_numbering(program, infer_types(program))
    assert num.int_regs == {"x": 0, "y1": 1, "y2": 2, "y": 3}
    assert num.bool_regs == {"c": 0, "ok": 1}
    assert num.block_index == {"entry": 0, "pos": 1, "neg": 2, "join": 3}
    assert num.entry_index == 0


# --- sanitizer / module names ---


def test_lean_ident_mangles_keywords_and_collisions():
    taken: set[str] = set()
    assert lean_ident("end", taken) == "end_"
    assert lean_ident("end_", taken) == "end__2"
    assert lean_ident("x", taken) == "x"
    assert lean_ident("x", taken) == "x_2"


def test_module_name_derivation():
    assert module_name_for("safe_core.ttac") == "SafeCore"
    assert module_name_for("a/b/diamond.ttac") == "Diamond"
    assert module_name_for("-") == "Prog"
    assert module_name_for("3way.ttac") == "P3way"


def test_block_def_names_reserved_against_registers():
    src = """\
entry:
  ok_join := havoc
  c := 0 <= ok_join
  if c goto join else join

join:
  assert c
  halt
"""
    res = _gen(src)
    assert res.names.block_defs["join"] == "ok_join"
    assert res.names.regs["ok_join"] == "ok_join_2"


# --- liveness ---


def test_liveness_diamond():
    program = parse_program(fx.SCALAR_DIAMOND)
    live = block_liveness(program)
    assert live.params["join"] == ("y",)
    assert live.live_in["join"] == frozenset()
    assert live.live_in["pos"] == {"x"}
    assert live.live_in["entry"] == frozenset()
    assert live.phi_targets["join"] == ("y",)


# --- validation ---


def _errors(src):
    return validate_for_lean(parse_program(src)).errors


def test_validate_rejects_bytemap_program():
    # `ttac lean` (shallow embedding) still rejects bytemaps; only
    # `ttac vc-check` accepts them (validate_for_lean(maps=True)).
    errs = _errors(fx.CORE)
    assert any("bytemap expression" in e for e in errs)
    assert any("bytemap" in e for e in errs)


def test_validate_rejects_reference_command():
    errs = _errors(fx.BORROW_SURFACE)
    assert any("reference command" in e for e in errs)


def test_validate_rejects_loop():
    src = "entry:\n  x := havoc\n  goto entry\n"
    assert any("loop-free" in e for e in _errors(src))


def test_validate_rejects_dynamic_definitions():
    src = """\
entry:
  c := havoc
  if c goto L else R

L:
  x := 1
  goto join

R:
  x := 2
  goto join

join:
  ok := 0 <= x
  assert ok
  halt
"""
    assert any("pure SSA" in e for e in _errors(src))


def test_generate_auto_converts_dynamic_to_ssa():
    # Same dynamic-merge program `validate_for_lean` rejects: `generate_lean`
    # runs the SSA precondition first and succeeds.
    src = """\
entry:
  c := havoc
  if c goto L else R

L:
  x := 1
  goto join

R:
  x := 2
  goto join

join:
  ok := 0 <= x
  assert ok
  halt
"""
    res = _gen(src)
    assert res.shallow_text is not None
    assert "phi" not in res.shallow_text  # phi is lowered, not left as a marker
    assert "x_L" in res.shallow_text and "x_R" in res.shallow_text


def test_validate_rejects_use_before_def():
    src = "entry:\n  y := x + 1\n  halt\n"
    assert any("used before it is defined" in e for e in _errors(src))


def test_validate_rejects_dangling_goto():
    src = "entry:\n  x := havoc\n  goto nowhere\n"
    assert any("undefined label 'nowhere'" in e for e in _errors(src))


def test_validate_rejects_phi_in_entry():
    src = """\
entry:
  x := phi [entry: y]
  halt
"""
    assert any("phi in the entry block" in e for e in _errors(src))


def test_validate_collects_multiple_errors():
    src = """\
entry:
  M := havoc
  x := M[0]
  goto nowhere
"""
    errs = _errors(src)
    assert len(errs) >= 2
    assert any("bytemap" in e for e in errs)
    assert any("undefined label" in e for e in errs)


def test_generate_raises_with_all_errors():
    with pytest.raises(LeanGenError) as exc:
        _gen(fx.CORE)
    assert len(exc.value.errors) >= 1


# --- emitters ---


def test_deep_text_pins():
    res = _gen(fx.SCALAR_DIAMOND, name="Diamond")
    assert "def prog : Program where" in res.deep_text
    assert ".phi .int 3 [(1, 1), (2, 2)]" in res.deep_text
    assert ".assign .bool 0 (.le (.litI 0) (.var .int 0))" in res.deep_text
    assert "term := .ifGoto 0 1 2" in res.deep_text
    assert "int registers:  0 = x, 1 = y1, 2 = y2, 3 = y" in res.deep_text
    assert "namespace Diamond.Deep" in res.deep_text
    assert "exit := none" in res.deep_text


def test_shallow_text_pins():
    res = _gen(fx.SCALAR_DIAMOND, name="Diamond")
    text = res.shallow_text
    assert "def ok_join (y : Int) : Prop :=" in text
    assert "ok_join y1" in text
    assert "ok_join y2" in text
    assert "∀ (x : Int)," in text
    assert "(c = true → ok_pos x) ∧ (c = false → ok_neg x)" in text
    assert "ok = true ∧ True" in text
    # join precedes its predecessors (reverse topological order).
    assert text.index("def ok_join") < text.index("def ok_pos")
    assert text.index("def ok_neg") < text.index("def ok_entry")


def test_shallow_assume_and_division():
    src = """\
entry:
  a := havoc
  b := a / 2
  assume not (a <= 0)
  ok := b <= a
  assert ok
  halt
"""
    res = _gen(src)
    assert "Int.ediv a 2" in res.shallow_text
    assert "(!(decide (a ≤ 0))) = true →" in res.shallow_text
    assert ".div (.var .int 0) (.litI 2)" in res.deep_text


def test_assert_parenthesizes_implication_continuation():
    src = """\
entry:
  a := havoc
  ok := 0 <= a
  assert ok
  assume a <= 10
  halt
"""
    res = _gen(src)
    # `∧` binds tighter than `→`: the assume after the assert must be
    # inside parens or the parse changes meaning.
    assert "ok = true ∧\n  ((decide (a ≤ 10)) = true →\n  True)" in res.shallow_text


def test_proofs_and_root_text():
    res = _gen(fx.SCALAR_DIAMOND, name="Diamond")
    assert "theorem shallow_safe : Shallow.ok_entry := by" in res.proofs_text
    assert "theorem deep_safe : Deep.prog.Safe := by" in res.proofs_text
    assert res.root_text.splitlines() == [
        "import Diamond.Deep",
        "import Diamond.Shallow",
        "import Diamond.Proofs",
    ]


def test_generation_is_deterministic():
    a = _gen(fx.SCALAR_DIAMOND)
    b = _gen(fx.SCALAR_DIAMOND)
    assert a.deep_text == b.deep_text
    assert a.shallow_text == b.shallow_text


# --- CLI ---


def test_cli_writes_project(tmp_path):
    out = tmp_path / "out"
    result = runner.invoke(
        app, ["lean", _write(tmp_path, fx.SCALAR_DIAMOND), "-o", str(out), "--plain"]
    )
    assert result.exit_code == 0
    assert (out / "lakefile.toml").is_file()
    assert (out / "lean-toolchain").is_file()
    assert (out / "Ttac" / "Semantics.lean").is_file()
    assert (out / "Prog" / "Deep.lean").is_file()
    assert (out / "Prog" / "Shallow.lean").is_file()
    assert (out / "Prog" / "Proofs.lean").is_file()


def test_cli_name_override(tmp_path):
    out = tmp_path / "out"
    result = runner.invoke(
        app,
        ["lean", _write(tmp_path, fx.SCALAR_DIAMOND), "-o", str(out),
         "--name", "Diamond", "--plain"],
    )
    assert result.exit_code == 0
    assert (out / "Diamond" / "Deep.lean").is_file()
    assert 'defaultTargets = ["Diamond"]' in (out / "lakefile.toml").read_text()


def test_cli_existing_dir_needs_force(tmp_path):
    out = tmp_path / "out"
    out.mkdir()
    (out / "junk.txt").write_text("keep me")
    src = _write(tmp_path, fx.SCALAR_DIAMOND)
    result = runner.invoke(app, ["lean", src, "-o", str(out), "--plain"])
    assert result.exit_code == 2
    result = runner.invoke(app, ["lean", src, "-o", str(out), "--force", "--plain"])
    assert result.exit_code == 0
    assert (out / "junk.txt").read_text() == "keep me"


def test_cli_force_keeps_user_proofs(tmp_path):
    out = tmp_path / "out"
    src = _write(tmp_path, fx.SCALAR_DIAMOND)
    assert runner.invoke(app, ["lean", src, "-o", str(out), "--plain"]).exit_code == 0
    proofs = out / "Prog" / "Proofs.lean"
    proofs.write_text("-- my proofs\n")
    assert (
        runner.invoke(app, ["lean", src, "-o", str(out), "--force", "--plain"]).exit_code
        == 0
    )
    assert proofs.read_text() == "-- my proofs\n"


def test_cli_validation_failure(tmp_path):
    result = runner.invoke(
        app, ["lean", _write(tmp_path, fx.CORE), "-o", str(tmp_path / "out"), "--plain"]
    )
    assert result.exit_code == 1
    assert "bytemap" in result.output


def test_cli_stdin(tmp_path):
    out = tmp_path / "out"
    result = runner.invoke(
        app, ["lean", "-", "-o", str(out), "--plain"], input=fx.SCALAR_STRAIGHT
    )
    assert result.exit_code == 0
    assert (out / "Prog" / "Shallow.lean").is_file()


def test_cli_no_assert_note(tmp_path):
    src = "entry:\n  x := havoc\n  y := x + 1\n  halt\n"
    result = runner.invoke(
        app, ["lean", _write(tmp_path, src), "-o", str(tmp_path / "out"), "--plain"]
    )
    assert result.exit_code == 0
    assert "vacuous" in result.output


def test_cli_shallow_only_is_dependency_free(tmp_path):
    out = tmp_path / "out"
    result = runner.invoke(
        app,
        ["lean", _write(tmp_path, fx.SCALAR_DIAMOND), "-o", str(out),
         "--no-deep", "--plain"],
    )
    assert result.exit_code == 0
    assert (out / "Prog" / "Shallow.lean").is_file()
    assert not (out / "Prog" / "Deep.lean").exists()
    assert not (out / "Ttac").exists()
    lakefile = (out / "lakefile.toml").read_text()
    assert "mathlib" not in lakefile
    assert "Ttac" not in lakefile
    proofs = (out / "Prog" / "Proofs.lean").read_text()
    assert "shallow_safe" in proofs
    assert "deep_safe" not in proofs


def test_cli_deep_only(tmp_path):
    out = tmp_path / "out"
    result = runner.invoke(
        app,
        ["lean", _write(tmp_path, fx.SCALAR_DIAMOND), "-o", str(out),
         "--no-shallow", "--plain"],
    )
    assert result.exit_code == 0
    assert (out / "Prog" / "Deep.lean").is_file()
    assert not (out / "Prog" / "Shallow.lean").exists()
    assert (out / "Ttac" / "Semantics.lean").is_file()
    proofs = (out / "Prog" / "Proofs.lean").read_text()
    assert "deep_safe" in proofs
    assert "shallow_safe" not in proofs
    root = (out / "Prog.lean").read_text()
    assert "import Prog.Shallow" not in root


def test_cli_rejects_no_embeddings(tmp_path):
    result = runner.invoke(
        app,
        ["lean", _write(tmp_path, fx.SCALAR_DIAMOND), "-o", str(tmp_path / "out"),
         "--no-deep", "--no-shallow", "--plain"],
    )
    assert result.exit_code == 2
    assert "nothing to emit" in result.output


# --- integration (opt-in: cold caches make this slow) ---


@pytest.mark.skipif(shutil.which("lake") is None, reason="lake not on PATH")
@pytest.mark.skipif(not os.environ.get("CTAC_LEAN_TESTS"), reason="set CTAC_LEAN_TESTS=1")
def test_lake_build_generated_project(tmp_path):
    out = tmp_path / "out"
    result = runner.invoke(
        app, ["lean", _write(tmp_path, fx.SCALAR_DIAMOND), "-o", str(out), "--plain"]
    )
    assert result.exit_code == 0
    subprocess.run(["lake", "exe", "cache", "get"], cwd=out, check=True, timeout=1800)
    build = subprocess.run(
        ["lake", "build"], cwd=out, capture_output=True, text=True, timeout=1800
    )
    assert build.returncode == 0, build.stdout + build.stderr
