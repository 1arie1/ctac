from ctac.ttac import parse_program
from ctac.ttac.analysis.defuse import extract_def_use


def du(src):
    return extract_def_use(parse_program(src))


def test_defs_and_uses_of_assignment():
    d = du("entry:\n  y := havoc\n  x := y + 1\n  halt\n")
    assert set(d.defs_by_symbol) == {"y", "x"}
    assert len(d.defs_by_symbol["x"]) == 1
    assert [u.symbol for u in d.uses_by_symbol["y"]] == ["y"]


def test_two_target_borrow_defines_both():
    d = du("entry:\n  M := havoc\n  i := havoc\n  r, M2 := borrow_mut M[i]\n  halt\n")
    assert {"r", "M2"} <= set(d.defs_by_symbol)
    assert {"M", "i"} <= set(d.uses_by_symbol)


def test_phi_arm_values_are_uses():
    src = (
        "entry:\n  c := havoc\n  if c goto l else r\n\n"
        "l:\n  a := havoc\n  goto j\n\n"
        "r:\n  b := havoc\n  goto j\n\n"
        "j:\n  z := phi [l: a, r: b]\n  halt\n"
    )
    d = du(src)
    assert "a" in d.uses_by_symbol and "b" in d.uses_by_symbol
    assert d.defs_by_symbol["z"][0].kind == "Phi"


def test_ifgoto_condition_is_a_use_at_terminator():
    d = du("entry:\n  c := havoc\n  if c goto a else b\n\na:\n  halt\n\nb:\n  halt\n")
    uses = d.uses_by_symbol["c"]
    assert len(uses) == 1
    assert uses[0].kind == "IfGoto"


def test_symbol_ids_are_compact_and_unique():
    d = du("entry:\n  M := havoc\n  i := havoc\n  x := M[i]\n  halt\n")
    ids = set(d.symbol_to_id.values())
    assert ids == set(range(len(d.symbol_to_id)))
    assert len(d.definitions) == 3  # M, i, x


def test_release_and_getref_ref_operands_are_uses():
    d = du("entry:\n  M := havoc\n  i := havoc\n  p := borrow M[i]\n"
           "  x := get_ref p\n  release p\n  halt\n")
    # p is used by get_ref and release.
    assert [u.kind for u in d.uses_by_symbol["p"]] == ["GetRef", "Release"]
