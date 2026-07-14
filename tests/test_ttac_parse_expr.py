from ctac.ttac import ast, parse_program


def parse_rhs(expr_src):
    prog = parse_program(f"entry:\n  x := {expr_src}\n  halt\n")
    return prog.blocks[0].commands[0].rhs


def test_arithmetic_binds_tighter_than_comparison():
    e = parse_rhs("x + 1 <= limit")
    assert e == ast.BinExpr(
        "<=", ast.BinExpr("+", ast.Var("x"), ast.Num(1)), ast.Var("limit")
    )


def test_mul_binds_tighter_than_add():
    assert parse_rhs("1 + 2 * 3") == ast.BinExpr(
        "+", ast.Num(1), ast.BinExpr("*", ast.Num(2), ast.Num(3))
    )


def test_left_associative_subtraction():
    assert parse_rhs("1 - 2 - 3") == ast.BinExpr(
        "-", ast.BinExpr("-", ast.Num(1), ast.Num(2)), ast.Num(3)
    )


def test_not_binds_looser_than_comparison():
    # not a == b  parses as  not (a == b)
    assert parse_rhs("not a == b") == ast.UnExpr(
        "not", ast.BinExpr("==", ast.Var("a"), ast.Var("b"))
    )


def test_not_binds_tighter_than_and():
    assert parse_rhs("not b and c") == ast.BinExpr(
        "and", ast.UnExpr("not", ast.Var("b")), ast.Var("c")
    )


def test_and_binds_tighter_than_or():
    assert parse_rhs("a or b and c") == ast.BinExpr(
        "or", ast.Var("a"), ast.BinExpr("and", ast.Var("b"), ast.Var("c"))
    )


def test_parentheses_override_precedence():
    assert parse_rhs("(1 + 2) * 3") == ast.BinExpr(
        "*", ast.BinExpr("+", ast.Num(1), ast.Num(2)), ast.Num(3)
    )


def test_load():
    assert parse_rhs("M[i]") == ast.Load(ast.Var("M"), ast.Var("i"))


def test_update():
    assert parse_rhs("M[i := y]") == ast.Update(ast.Var("M"), ast.Var("i"), ast.Var("y"))


def test_if_expr_rust_syntax():
    assert parse_rhs("if b { 1 } else { 0 }") == ast.IfExpr(
        ast.Var("b"), ast.Num(1), ast.Num(0)
    )


def test_field_projection():
    assert parse_rhs("r.value") == ast.Field(ast.Var("r"), "value")


def test_record_literal_with_havoc_field():
    assert parse_rhs("{ addr: i, value: M[i], promise: havoc }") == ast.Record(
        ast.Var("i"), ast.Load(ast.Var("M"), ast.Var("i")), ast.HavocExpr()
    )


def test_bool_literals():
    assert parse_rhs("true") == ast.BoolLit(True)
    assert parse_rhs("false") == ast.BoolLit(False)
