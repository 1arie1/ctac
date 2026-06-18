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
