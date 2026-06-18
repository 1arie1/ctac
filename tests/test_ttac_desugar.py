import ttac_fixtures as fx
from ctac.ttac import ast, parse_program, pretty
from ctac.ttac.analysis import check_dsa, infer_types
from ctac.ttac.transform import desugar_refs

_BORROW_CMDS = (
    ast.Borrow, ast.BorrowMut, ast.GetRef, ast.PutRef, ast.Release,
    ast.BorrowRef, ast.BorrowRefMut,
)


def one_cmd(body):
    """Desugar a single command (wrapped in a trivial block) -> cmd list."""
    prog = parse_program(f"entry:\n  {body}\n  halt\n")
    return list(desugar_refs(prog).program.blocks[0].commands)


def test_borrow_lowers_to_three_assigns():
    cmds = one_cmd("r := borrow M[i]")
    assert cmds == [
        ast.Assign(ast.Target("r__addr"), ast.Var("i")),
        ast.Assign(ast.Target("r__value"), ast.Load(ast.Var("M"), ast.Var("i"))),
        ast.Havoc(ast.Target("r__promise")),
    ]


def test_borrow_mut_adds_continuation_map():
    cmds = one_cmd("r, M2 := borrow_mut M[i]")
    assert cmds[-1] == ast.Assign(
        ast.Target("M2"), ast.Update(ast.Var("M"), ast.Var("i"), ast.Var("r__promise"))
    )
    assert ast.Havoc(ast.Target("r__promise")) in cmds


def test_get_ref_reads_value_register():
    assert one_cmd("x := get_ref r") == [ast.Assign(ast.Target("x"), ast.Var("r__value"))]


def test_put_ref_copies_addr_promise_sets_value():
    cmds = one_cmd("r2 := put_ref r, 7")
    assert cmds == [
        ast.Assign(ast.Target("r2__addr"), ast.Var("r__addr")),
        ast.Assign(ast.Target("r2__value"), ast.Num(7)),
        ast.Assign(ast.Target("r2__promise"), ast.Var("r__promise")),
    ]


def test_release_asserts_value_equals_promise():
    assert one_cmd("release r") == [
        ast.Assume(ast.BinExpr("==", ast.Var("r__value"), ast.Var("r__promise")))
    ]


def test_borrow_ref_mut_two_targets():
    cmds = one_cmd("q, r2 := borrow_ref_mut r")
    assert cmds == [
        ast.Assign(ast.Target("q__addr"), ast.Var("r__addr")),
        ast.Assign(ast.Target("q__value"), ast.Var("r__value")),
        ast.Havoc(ast.Target("q__promise")),
        ast.Assign(ast.Target("r2__addr"), ast.Var("r__addr")),
        ast.Assign(ast.Target("r2__value"), ast.Var("q__promise")),
        ast.Assign(ast.Target("r2__promise"), ast.Var("r__promise")),
    ]


def _no_borrow_commands(program):
    return not any(
        isinstance(c, _BORROW_CMDS) for b in program.blocks for c in b.commands
    )


def _no_records_or_fields(program):
    def expr_clean(e):
        if isinstance(e, (ast.Record, ast.Field)):
            return False
        if isinstance(e, ast.Load):
            return expr_clean(e.base) and expr_clean(e.index)
        if isinstance(e, ast.Update):
            return all(expr_clean(x) for x in (e.base, e.index, e.value))
        if isinstance(e, ast.BinExpr):
            return expr_clean(e.lhs) and expr_clean(e.rhs)
        if isinstance(e, ast.UnExpr):
            return expr_clean(e.operand)
        if isinstance(e, ast.IfExpr):
            return all(expr_clean(x) for x in (e.cond, e.then, e.els))
        return True
    for b in program.blocks:
        for c in b.commands:
            if isinstance(c, ast.Assign) and not expr_clean(c.rhs):
                return False
            if isinstance(c, ast.Assume) and not expr_clean(c.cond):
                return False
    return True


import pytest  # noqa: E402


@pytest.mark.parametrize(
    "name", ["BORROW_SURFACE", "MUT_BORROW_SURFACE", "REBORROW_SURFACE"]
)
def test_surface_examples_become_reference_free(name):
    res = desugar_refs(parse_program(fx.ALL[name]))
    out = res.program
    assert _no_borrow_commands(out)
    assert _no_records_or_fields(out)
    assert parse_program(pretty(out)) == out
    assert check_dsa(out).is_valid
    types = infer_types(out)  # raises if not total
    assert ast.Ty.REF not in types.values()
    assert res.refs_lowered > 0


def test_refs_lowered_count():
    # MUT_BORROW_SURFACE: borrow_mut, put_ref, release = 3 borrow commands.
    assert desugar_refs(parse_program(fx.MUT_BORROW_SURFACE)).refs_lowered == 3


def test_collision_guard():
    src = "entry:\n  r__value := havoc\n  r := borrow M[i]\n  halt\n"
    with pytest.raises(ValueError, match="collide"):
        desugar_refs(parse_program(src))
