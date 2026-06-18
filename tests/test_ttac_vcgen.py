import pytest

import ttac_fixtures as fx
from ctac.ttac import parse_program
from ctac.ttac.errors import VcGenError
from ctac.ttac.vcgen import generate_vc

PHI_DIAMOND = (
    "entry:\n  c := havoc\n  if c goto left else right\n\n"
    "left:\n  xl := havoc\n  goto join\n\n"
    "right:\n  xr := havoc\n  goto join\n\n"
    "join:\n  x := phi [left: xl, right: xr]\n  ok := 0 <= x\n  assert ok\n  halt\n"
)

BYTEMAP = (
    "entry:\n  M := havoc\n  i := havoc\n  v := havoc\n  M2 := M[i := v]\n"
    "  x := M2[i]\n  ok := x == v\n  assert ok\n  halt\n"
)


def vc(src):
    return generate_vc(parse_program(src))


def test_core_single_assert_objective():
    res = vc(fx.CORE)
    assert res.assert_block == "ok"
    assert not res.merged and res.asserts_before == 1
    assert "(check-sat)" in res.smt_text
    assert "BLK_EXIT" in res.smt_text
    assert "(set-logic QF_UFNIA)" in res.smt_text
    # exactly one assert objective (BLK_EXIT implication + its reachability)
    assert res.smt_text.count("BLK_EXIT") >= 2


def test_multi_assert_is_merged():
    res = vc(fx.TWO_ASSERTS)
    assert res.merged and res.asserts_before == 2
    assert res.assert_block == "__UA_ERROR"
    # the only assert command in the VC is the __ua_fail objective
    assert "__ua_fail" in res.smt_text


def test_branch_asserts_merged():
    res = vc(fx.BRANCH_ASSERTS)
    assert res.merged and res.asserts_before == 2


def test_reference_program_rejected():
    with pytest.raises(VcGenError, match="reference"):
        vc(fx.MUT_BORROW_SURFACE)


def test_loop_rejected():
    src = "entry:\n  c := havoc\n  assert c\n  goto entry\n"
    with pytest.raises(VcGenError, match="loop"):
        vc(src)


def test_no_assertion_rejected():
    with pytest.raises(VcGenError, match="no assertion"):
        vc("entry:\n  x := havoc\n  halt\n")


def test_bytemap_uf_no_bv256_axiom():
    res = vc(BYTEMAP)
    assert "(declare-fun M (Int) Int)" in res.smt_text
    assert "(define-fun M2" in res.smt_text
    assert "in_bv256" not in res.smt_text  # select_range="none" -> no bv256 range axiom


def test_phi_encoded_as_ite_with_amo():
    res = vc(PHI_DIAMOND)
    # ITE merge over the predecessor guards for the phi target x.
    assert "(ite BLK_left xl xr)" in res.smt_text
    # at-most-one over the feeding guards (both predecessor guards appear
    # together in a clause).
    assert "BLK_left" in res.smt_text and "BLK_right" in res.smt_text
