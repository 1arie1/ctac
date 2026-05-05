"""Round-trip tests for the AST -> TAC command text unparser."""

from __future__ import annotations

from ctac.ast.nodes import (
    ApplyExpr,
    AssertCmd,
    AssignExpCmd,
    AssignHavocCmd,
    AssumeExpCmd,
    ConstExpr,
    JumpCmd,
    JumpiCmd,
    LabelCmd,
    SymbolRef,
)
from ctac.ast.parse_cmd import parse_command_line
from ctac.ast.parse_expr import parse_expr
from ctac.rewrite.unparse import canonicalize_cmd, unparse_cmd, unparse_expr


def _roundtrip_expr(text: str) -> None:
    expr = parse_expr(text)
    text2 = unparse_expr(expr)
    expr2 = parse_expr(text2)
    assert expr == expr2, (text, text2, expr, expr2)


def test_unparse_const():
    assert unparse_expr(ConstExpr("0x4000")) == "0x4000"
    assert unparse_expr(ConstExpr("0x4000(int)")) == "0x4000(int)"
    assert unparse_expr(ConstExpr("42")) == "42"
    assert unparse_expr(ConstExpr("true")) == "true"


def test_unparse_symbol_and_apply():
    assert unparse_expr(SymbolRef("R34")) == "R34"
    assert unparse_expr(SymbolRef("R34:5")) == "R34:5"
    assert (
        unparse_expr(ApplyExpr("Div", (SymbolRef("A"), ConstExpr("0x4"))))
        == "Div(A 0x4)"
    )


def test_unparse_nested_apply():
    expr = ApplyExpr(
        "Mul",
        (
            ApplyExpr(
                "Mod",
                (
                    ApplyExpr("Div", (SymbolRef("X"), ConstExpr("0x4000"))),
                    ConstExpr("0x100000000"),
                ),
            ),
            ConstExpr("0x4000"),
        ),
    )
    assert unparse_expr(expr) == "Mul(Mod(Div(X 0x4000) 0x100000000) 0x4000)"


def test_expr_roundtrip_variants():
    _roundtrip_expr("Div(R26 0x64)")
    _roundtrip_expr("BWAnd(R34 0x3fffffffc000)")
    _roundtrip_expr("LAnd(Ge(I37 0x0(int)) Le(I37 0xffffffffffffffff(int)))")
    _roundtrip_expr("Apply(safe_math_narrow_bv256:bif I33:0)")
    _roundtrip_expr("Ite(LOr(B50 B51) 0x4000 R48)")


def test_unparse_assign_with_meta():
    cmd = AssignExpCmd(
        raw="_unused_",
        meta_index=11,
        lhs="R35",
        rhs=ApplyExpr("BWAnd", (SymbolRef("R34"), ConstExpr("0x3fffffffc000"))),
    )
    assert unparse_cmd(cmd) == "AssignExpCmd:11 R35 BWAnd(R34 0x3fffffffc000)"


def test_unparse_assume_without_meta():
    cmd = AssumeExpCmd(
        raw="_unused_",
        condition=ApplyExpr("Le", (SymbolRef("R0"), ConstExpr("0xffffffff"))),
    )
    assert unparse_cmd(cmd) == "AssumeExpCmd Le(R0 0xffffffff)"


def test_unparse_havoc_jump_label_assert():
    assert unparse_cmd(AssignHavocCmd(raw="_", lhs="R0")) == "AssignHavocCmd R0"
    assert unparse_cmd(JumpCmd(raw="_", target="B2")) == "JumpCmd B2"
    assert (
        unparse_cmd(JumpiCmd(raw="_", then_target="t", else_target="e", condition="c"))
        == "JumpiCmd t e c"
    )
    assert unparse_cmd(LabelCmd(raw="_", text="hi")) == 'LabelCmd "hi"'
    assert (
        unparse_cmd(
            AssertCmd(raw="_", predicate=ConstExpr("false"), message="assertion failed")
        )
        == 'AssertCmd false "assertion failed"'
    )


def test_canonicalize_cmd_updates_raw_after_rewrite():
    cmd = parse_command_line("AssignExpCmd:7 R29 Div(R26 0x64 )")
    new_rhs = ApplyExpr("Div", (SymbolRef("R26"), ConstExpr("0x64")))
    from dataclasses import replace

    new_cmd = replace(cmd, rhs=new_rhs)
    canon = canonicalize_cmd(new_cmd)
    assert canon.raw == "AssignExpCmd:7 R29 Div(R26 0x64)"


def test_parse_assume_cmd_bareword_to_assume_exp():
    """`AssumeCmd <sym> "msg"` canonicalizes to AssumeExpCmd(SymbolRef(sym))."""
    cmd = parse_command_line('AssumeCmd g "g must hold"')
    assert isinstance(cmd, AssumeExpCmd)
    assert cmd.condition == SymbolRef("g")
    assert cmd.meta_index is None
    # Raw text round-trips verbatim — render_program will emit the
    # bareword form unchanged.
    assert cmd.raw == 'AssumeCmd g "g must hold"'


def test_parse_assume_not_cmd_bareword_to_assume_exp_lnot():
    """`AssumeNotCmd <sym> "msg"` canonicalizes to AssumeExpCmd(LNot(sym))."""
    cmd = parse_command_line('AssumeNotCmd h "h must not hold"')
    assert isinstance(cmd, AssumeExpCmd)
    assert cmd.condition == ApplyExpr("LNot", (SymbolRef("h"),))


def test_parse_assume_cmd_without_message():
    """The trailing message is optional."""
    cmd = parse_command_line("AssumeCmd g")
    assert isinstance(cmd, AssumeExpCmd)
    assert cmd.condition == SymbolRef("g")


def test_parse_assume_cmd_preserves_meta_index():
    """`AssumeCmd:42 g "msg"` keeps its meta_index through canonicalization."""
    cmd = parse_command_line('AssumeCmd:42 g "msg"')
    assert isinstance(cmd, AssumeExpCmd)
    assert cmd.meta_index == 42
    assert cmd.condition == SymbolRef("g")


def test_parse_assume_not_cmd_with_meta_and_message():
    cmd = parse_command_line('AssumeNotCmd:7 b "boundary"')
    assert isinstance(cmd, AssumeExpCmd)
    assert cmd.meta_index == 7
    assert cmd.condition == ApplyExpr("LNot", (SymbolRef("b"),))


def test_command_roundtrip_through_parser():
    lines = [
        "AssignExpCmd:7 R29 Div(R26 0x64)",
        "AssignExpCmd R35 BWAnd(R34 0x3fffffffc000)",
        "AssumeExpCmd LAnd(Ge(I37 0x0(int)) Le(I37 0xffffffffffffffff(int)))",
        "AssignHavocCmd R0",
        "JumpCmd 1_0_0",
    ]
    for line in lines:
        cmd = parse_command_line(line)
        text = unparse_cmd(cmd)
        cmd2 = parse_command_line(text)
        # Round-trip preserves structural equality (ignoring raw).
        from dataclasses import replace

        assert replace(cmd, raw="") == replace(cmd2, raw="")
