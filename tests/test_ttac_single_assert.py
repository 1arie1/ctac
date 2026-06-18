import ttac_fixtures as fx
from ctac.ttac import ast, parse_program, pretty
from ctac.ttac.analysis import check_dsa, infer_types
from ctac.ttac.ast import Ty
from ctac.ttac.transform.single_assert import to_single_assert


def asserts_in(program):
    return [
        (b.label, c.cond_name)
        for b in program.blocks
        for c in b.commands
        if isinstance(c, ast.Assert)
    ]


def assumes_in(program):
    return [
        c.cond
        for b in program.blocks
        for c in b.commands
        if isinstance(c, ast.Assume)
    ]


def test_keeps_chosen_assert_demotes_others():
    prog = parse_program(fx.BRANCH_ASSERTS)
    # The L-arm assert is at block "L", command index 1.
    out = to_single_assert(prog, "L", 1)
    assert asserts_in(out) == [("L", "okL")]
    # The R-arm obligation (okR) survives only as an assumption, and the
    # branch guard c is assumed (then-arm).
    assert ast.Assume(ast.Var("c")) in [
        c for b in out.blocks for c in b.commands if isinstance(c, ast.Assume)
    ]


def test_live_block_truncated_to_halt():
    prog = parse_program(fx.BRANCH_ASSERTS)
    out = to_single_assert(prog, "L", 1)
    live = [b for b in out.blocks if b.label == "L"][0]
    assert isinstance(live.terminator, ast.Halt)
    assert isinstance(live.commands[-1], ast.Assert)


def test_output_is_wellformed_and_typed():
    prog = parse_program(fx.BRANCH_ASSERTS)
    out = to_single_assert(prog, "L", 1)
    assert check_dsa(out).is_valid
    t = infer_types(out)
    assert t["c"] == Ty.BOOL and t["x"] == Ty.INT and t["okL"] == Ty.BOOL
    assert parse_program(pretty(out)) == out


def test_else_arm_uses_negated_guard():
    prog = parse_program(fx.BRANCH_ASSERTS)
    out = to_single_assert(prog, "R", 1)
    assert asserts_in(out) == [("R", "okR")]
    assert ast.UnExpr("not", ast.Var("c")) in assumes_in(out)
