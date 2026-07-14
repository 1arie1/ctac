"""Solver-backed vcgen tests; skipped when no z3 is resolvable."""

import pytest

import ttac_fixtures as fx
from ctac.ttac import parse_program
from ctac.ttac.vcgen import generate_vc

run_z3_solver = pytest.importorskip("ctac.smt.runner").run_z3_solver
from ctac.smt.z3_model import parse_z3_sat_output  # noqa: E402
from ctac.solver.z3 import resolve_z3_bin  # noqa: E402

try:
    _Z3 = str(resolve_z3_bin(None))
except FileNotFoundError:
    _Z3 = None

requires_z3 = pytest.mark.skipif(_Z3 is None, reason="no z3 binary resolvable")

BYTEMAP_SAFE = (
    "entry:\n  M := havoc\n  i := havoc\n  v := havoc\n  M2 := M[i := v]\n"
    "  x := M2[i]\n  ok := x == v\n  assert ok\n  halt\n"
)


def _solve(src):
    res = generate_vc(parse_program(src))
    r = run_z3_solver(
        smt_text=res.smt_text, z3_path=_Z3, timeout_seconds=30, seed=0,
        tactic="default", extra_args=[], want_model=True,
    )
    assert not r.timed_out
    return parse_z3_sat_output(r.stdout).status


@requires_z3
def test_core_is_unsat():
    assert _solve(fx.CORE) == "unsat"


@requires_z3
def test_bytemap_store_then_read_is_unsat():
    assert _solve(BYTEMAP_SAFE) == "unsat"


@requires_z3
def test_two_asserts_havoc_bools_is_sat():
    # Asserting arbitrary havoc'd bools can fail -> merged VC is sat.
    assert _solve(fx.TWO_ASSERTS) == "sat"


# --- desugar -> vcgen: the strong check that borrow lowering matches the doc ---

from ctac.ttac.transform import desugar_refs  # noqa: E402


def _solve_desugared(src):
    return _solve_program(desugar_refs(parse_program(src)).program)


def _solve_program(program):
    from ctac.ttac.vcgen import generate_vc
    res = generate_vc(program)
    r = run_z3_solver(
        smt_text=res.smt_text, z3_path=_Z3, timeout_seconds=30, seed=0,
        tactic="default", extra_args=[], want_model=False,
    )
    assert not r.timed_out
    return parse_z3_sat_output(r.stdout).status


_UNSAFE_BORROW = (
    "entry:\n  M := havoc\n  i := havoc\n  r, M2 := borrow_mut M[i]\n"
    "  r2 := put_ref r, 7\n  release r2\n  x := M2[i]\n  ok := x == 8\n"
    "  assert ok\n  halt\n"
)


@requires_z3
@pytest.mark.parametrize(
    "name", ["BORROW_SURFACE", "MUT_BORROW_SURFACE", "REBORROW_SURFACE"]
)
def test_desugared_surface_examples_are_unsat(name):
    assert _solve_desugared(fx.ALL[name]) == "unsat"


@requires_z3
def test_desugared_unsafe_borrow_is_sat():
    assert _solve_desugared(_UNSAFE_BORROW) == "sat"


@requires_z3
def test_run_replays_vcgen_counterexample():
    # vcgen --model on the desugared unsafe borrow, then run with that model
    # must reproduce the assertion failure (run and vcgen share semantics).
    from ctac.eval.model import parse_model_text
    from ctac.ttac.run import RunConfig, run_program
    from ctac.ttac.vcgen import generate_vc

    desugared = desugar_refs(parse_program(_UNSAFE_BORROW)).program
    res = generate_vc(desugared)
    r = run_z3_solver(
        smt_text=res.smt_text, z3_path=_Z3, timeout_seconds=30, seed=0,
        tactic="default", extra_args=[], want_model=True,
    )
    out = parse_z3_sat_output(r.stdout)
    assert out.status == "sat"
    model = parse_model_text(out.model_text)
    rr = run_program(desugared, config=RunConfig(model=model))
    assert rr.assert_fail >= 1
