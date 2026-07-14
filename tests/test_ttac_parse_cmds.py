import pytest

from ctac.ttac import ast, parse_program
from ctac.ttac.errors import TtacParseError


def first_cmd(body):
    prog = parse_program(f"entry:\n  {body}\n  halt\n")
    return prog.blocks[0].commands[0]


def test_expression_assignment():
    assert first_cmd("y := x + 1") == ast.Assign(
        ast.Target("y"), ast.BinExpr("+", ast.Var("x"), ast.Num(1))
    )


def test_havoc_command():
    assert first_cmd("M := havoc") == ast.Havoc(ast.Target("M"))


def test_phi_command():
    cmd = first_cmd("x := phi [left: x_left, right: x_right]")
    assert cmd == ast.Phi(
        ast.Target("x"),
        (ast.PhiArm("left", "x_left"), ast.PhiArm("right", "x_right")),
    )


def test_get_ref():
    assert first_cmd("x := get_ref p") == ast.GetRef(ast.Target("x"), "p")


def test_borrow():
    assert first_cmd("p := borrow M[i]") == ast.Borrow(
        ast.Target("p"), ast.Var("M"), ast.Var("i")
    )


def test_borrow_mut_two_targets():
    assert first_cmd("r, M2 := borrow_mut M[i]") == ast.BorrowMut(
        ast.Target("r"), ast.Target("M2"), ast.Var("M"), ast.Var("i")
    )


def test_borrow_ref():
    assert first_cmd("q := borrow_ref r") == ast.BorrowRef(ast.Target("q"), "r")


def test_borrow_ref_mut_two_targets():
    assert first_cmd("q, r2 := borrow_ref_mut r") == ast.BorrowRefMut(
        ast.Target("q"), ast.Target("r2"), "r"
    )


def test_put_ref():
    assert first_cmd("r2 := put_ref r, 7") == ast.PutRef(
        ast.Target("r2"), "r", ast.Num(7)
    )


def test_release():
    assert first_cmd("release r") == ast.Release("r")


def test_assume_arbitrary_expression():
    assert first_cmd("assume not c") == ast.Assume(ast.UnExpr("not", ast.Var("c")))


def test_assert_named_register():
    assert first_cmd("assert ok") == ast.Assert("ok")


def test_optional_type_annotation():
    assert first_cmd("x: int := havoc") == ast.Havoc(ast.Target("x", ast.Ty.INT))
    assert first_cmd("r: ref := borrow M[i]") == ast.Borrow(
        ast.Target("r", ast.Ty.REF), ast.Var("M"), ast.Var("i")
    )


def test_untyped_target_has_no_type():
    cmd = first_cmd("x := havoc")
    assert cmd.target.ty is None


def test_borrow_mut_requires_two_targets():
    with pytest.raises(TtacParseError, match="binds 2 target"):
        first_cmd("r := borrow_mut M[i]")


def test_expression_assignment_rejects_two_targets():
    with pytest.raises(TtacParseError, match="single target"):
        first_cmd("a, b := x + 1")


def test_unknown_type_annotation_rejected():
    with pytest.raises(TtacParseError, match="unknown type"):
        first_cmd("x: u64 := havoc")
