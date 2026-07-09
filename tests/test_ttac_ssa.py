from ctac.ttac import parse_program
from ctac.ttac.analysis.dsa import check_dsa
from ctac.ttac.transform.ssa import to_ssa

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
    "join:\n  ok := x == x\n  assert ok\n  halt\n"
)

# x is dynamic and used again *inside* its own def block after the def.
DSA_USE_AFTER_DEF = (
    "entry:\n  c := havoc\n  if c goto left else right\n\n"
    "left:\n  x := havoc\n  y := x\n  goto join\n\n"
    "right:\n  x := havoc\n  goto join\n\n"
    "join:\n  ok := x == x\n  assert ok\n  halt\n"
)


def test_ssa_input_is_noop():
    prog = parse_program(SSA_DIAMOND)
    res = to_ssa(prog)
    assert res.was_noop
    assert res.program is prog


def test_dynamic_merge_becomes_phi():
    res = to_ssa(parse_program(DSA_DIAMOND))
    assert not res.was_noop
    assert res.converted == ("x",)
    dsa = check_dsa(res.program)
    assert dsa.is_valid, dsa.issues
    assert "x" in dsa.phi
    assert not dsa.dynamic
    join = next(b for b in res.program.blocks if b.label == "join")
    phi = join.commands[0]
    assert phi.target.name == "x"
    assert {a.label for a in phi.arms} == {"left", "right"}
    assert {a.value for a in phi.arms} == {"x_left", "x_right"}


def test_use_after_def_in_branch_is_renamed():
    res = to_ssa(parse_program(DSA_USE_AFTER_DEF))
    dsa = check_dsa(res.program)
    assert dsa.is_valid, dsa.issues
    left = next(b for b in res.program.blocks if b.label == "left")
    # `y := x` must now read the fresh per-block name, not the phi target.
    y_assign = next(c for c in left.commands if getattr(c, "target", None)
                    and c.target.name == "y")
    assert y_assign.rhs.name == "x_left"
