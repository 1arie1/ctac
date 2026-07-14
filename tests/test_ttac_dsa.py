import ttac_fixtures as fx
from ctac.ttac import parse_program
from ctac.ttac.analysis.dsa import check_dsa


def chk(src):
    return check_dsa(parse_program(src))


SSA_DIAMOND = (
    "entry:\n  c := havoc\n  if c goto left else right\n\n"
    "left:\n  xl := havoc\n  goto join\n\n"
    "right:\n  xr := havoc\n  goto join\n\n"
    "join:\n  x := phi [left: xl, right: xr]\n  halt\n"
)

DSA_DIAMOND = (
    "entry:\n  c := havoc\n  if c goto left else right\n\n"
    "left:\n  al := havoc\n  x := al\n  goto join\n\n"
    "right:\n  ar := havoc\n  x := ar\n  goto join\n\n"
    "join:\n  halt\n"
)

# A phi (for y) and a dynamic merge (for x) in the same program.
MIXED = (
    "entry:\n  c := havoc\n  if c goto left else right\n\n"
    "left:\n  al := havoc\n  x := al\n  goto join\n\n"
    "right:\n  ar := havoc\n  x := ar\n  goto join\n\n"
    "join:\n  y := phi [left: al, right: ar]\n  halt\n"
)


def test_core_fixture_is_valid_ssa():
    assert chk(fx.CORE).is_valid


def test_ssa_diamond_valid_phi():
    r = chk(SSA_DIAMOND)
    assert r.is_valid
    assert "x" in r.phi


def test_dsa_diamond_valid_dynamic():
    r = chk(DSA_DIAMOND)
    assert r.is_valid
    assert "x" in r.dynamic


def test_mixed_phi_and_dynamic_is_valid():
    r = chk(MIXED)
    assert r.is_valid, r.issues
    assert "x" in r.dynamic
    assert "y" in r.phi


def test_double_static_definition_is_over_definition():
    r = chk("entry:\n  x := havoc\n  x := havoc\n  halt\n")
    assert not r.is_valid
    assert any(i.kind == "over-definition" for i in r.issues)


def test_phi_arity_mismatch():
    src = (
        "entry:\n  c := havoc\n  if c goto left else right\n\n"
        "left:\n  q := havoc\n  goto join\n\n"
        "right:\n  goto join\n\n"
        "join:\n  x := phi [left: q]\n  halt\n"
    )
    r = chk(src)
    assert not r.is_valid
    assert any(i.kind == "phi" for i in r.issues)


def test_dynamic_not_contiguous_suffix():
    src = (
        "entry:\n  c := havoc\n  if c goto left else right\n\n"
        "left:\n  al := havoc\n  x := al\n  z := havoc\n  goto join\n\n"
        "right:\n  ar := havoc\n  x := ar\n  goto join\n\n"
        "join:\n  halt\n"
    )
    r = chk(src)
    assert not r.is_valid
    assert any(i.kind == "shape" for i in r.issues)


def test_ambiguous_use_of_non_dynamic_symbol():
    src = (
        "entry:\n  c := havoc\n  x := havoc\n  if c goto mid else join\n\n"
        "mid:\n  x := havoc\n  goto join\n\n"
        "join:\n  y := x + 1\n  halt\n"
    )
    r = chk(src)
    assert not r.is_valid
    assert any(i.kind == "ambiguous-use" for i in r.issues)
