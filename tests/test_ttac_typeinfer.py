import pytest

import ttac_fixtures as fx
from ctac.ttac import parse_program
from ctac.ttac.analysis.typeinfer import analyze_types, infer_types
from ctac.ttac.ast import Ty
from ctac.ttac.errors import TtacTypeError


def types(src):
    return infer_types(parse_program(src))


def test_core_fixture_fully_typed():
    t = types(fx.CORE)
    assert t == {
        "M": Ty.BYTEMAP,
        "i": Ty.INT,
        "limit": Ty.INT,
        "x": Ty.INT,
        "y": Ty.INT,
        "M2": Ty.BYTEMAP,
        "c": Ty.BOOL,
    }


def test_lowered_ref_program_typed():
    t = types(fx.MUT_BORROW_LOWERED)
    assert t["r"] == Ty.REF
    assert t["r2"] == Ty.REF
    assert t["M"] == Ty.BYTEMAP
    assert t["M2"] == Ty.BYTEMAP
    assert t["x"] == Ty.INT
    assert t["ok"] == Ty.BOOL


def test_borrow_surface_program_typed():
    t = types(fx.MUT_BORROW_SURFACE)
    assert t["r"] == Ty.REF
    assert t["M2"] == Ty.BYTEMAP
    assert t["ok"] == Ty.BOOL


def test_annotation_types_an_otherwise_free_havoc():
    assert types("entry:\n  x: int := havoc\n  halt\n") == {"x": Ty.INT}


def test_copy_and_arithmetic_propagation():
    src = "entry:\n  i := havoc\n  x := i + 1\n  y := x\n  c := y <= i\n  assert c\n  halt\n"
    t = types(src)
    assert t["x"] == Ty.INT and t["y"] == Ty.INT and t["c"] == Ty.BOOL


def test_phi_unifies_arm_types():
    src = (
        "entry:\n  c := havoc\n  if c goto l else r\n\n"
        "l:\n  a := havoc\n  goto j\n\n"
        "r:\n  b := havoc\n  goto j\n\n"
        "j:\n  z := phi [l: a, r: b]\n  zz := z + 1\n  halt\n"
    )
    t = types(src)
    assert t["a"] == Ty.INT and t["b"] == Ty.INT and t["z"] == Ty.INT


def test_conflict_is_reported():
    src = "entry:\n  M := havoc\n  i := havoc\n  x := M[i]\n  b := not x\n  halt\n"
    res = analyze_types(parse_program(src))
    assert "x" in res.conflicts
    with pytest.raises(TtacTypeError):
        infer_types(parse_program(src))


def test_unconstrained_variable_hard_fails():
    with pytest.raises(TtacTypeError) as exc:
        types("entry:\n  x := havoc\n  halt\n")
    assert "x" in exc.value.unknown


def test_analyze_types_does_not_raise_on_unknown():
    res = analyze_types(parse_program("entry:\n  x := havoc\n  halt\n"))
    assert res.types["x"] is None
    assert not res.is_total
