"""Tests for ADD_ITE_DIST / SUB_ITE_DIST_LEFT / SUB_ITE_DIST_RIGHT rules."""

from __future__ import annotations

from ctac.ast.nodes import ApplyExpr, AssignExpCmd
from ctac.parse import parse_string
from ctac.rewrite import rewrite_program
from ctac.rewrite.rules import (
    ADD_ITE_DIST,
    SUB_ITE_DIST_LEFT,
    SUB_ITE_DIST_RIGHT,
)


def _wrap(body: str, *, syms: str = "A:bv256\n\tY:bv256\n\tR:bv256\n\tc:bool") -> str:
    return f"""TACSymbolTable {{
\tUserDefined {{
\t}}
\tBuiltinFunctions {{
\t}}
\tUninterpretedFunctions {{
\t}}
\t{syms}
}}
Program {{
{body}
}}
Axioms {{
}}
Metas {{
  "0": []
}}
"""


def _rhs(program, lhs: str):
    for block in program.blocks:
        for cmd in block.commands:
            if isinstance(cmd, AssignExpCmd) and cmd.lhs == lhs:
                return cmd.rhs
    raise AssertionError(f"no AssignExpCmd for {lhs!r}")


def test_add_ite_dist_lhs_ite():
    # Add(Ite(c, T, E), Y) -> Ite(c, Add(T, Y), Add(E, Y)).
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd A\n"
            "\t\tAssignHavocCmd Y\n"
            "\t\tAssignHavocCmd c\n"
            "\t\tAssignExpCmd R Add(Ite(c 0x1 0x0) Y)\n"
            "\t}"
        ),
        path="<s>",
    )
    res = rewrite_program(
        tac.program, (ADD_ITE_DIST,), symbol_sorts=tac.symbol_sorts
    )
    rhs = _rhs(res.program, "R")
    assert isinstance(rhs, ApplyExpr) and rhs.op == "Ite"
    _cond, then_branch, else_branch = rhs.args
    assert isinstance(then_branch, ApplyExpr) and then_branch.op == "Add"
    assert isinstance(else_branch, ApplyExpr) and else_branch.op == "Add"


def test_add_ite_dist_rhs_ite():
    # Add commutes: Add(Y, Ite(c, T, E)) also distributes.
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd Y\n"
            "\t\tAssignHavocCmd c\n"
            "\t\tAssignExpCmd R Add(Y Ite(c 0x1 0x0))\n"
            "\t}"
        ),
        path="<s>",
    )
    res = rewrite_program(
        tac.program, (ADD_ITE_DIST,), symbol_sorts=tac.symbol_sorts
    )
    rhs = _rhs(res.program, "R")
    assert isinstance(rhs, ApplyExpr) and rhs.op == "Ite"
    _cond, then_branch, else_branch = rhs.args
    assert isinstance(then_branch, ApplyExpr) and then_branch.op == "Add"
    assert isinstance(else_branch, ApplyExpr) and else_branch.op == "Add"


def test_add_ite_dist_noop_without_ite():
    # Plain Add(A, Y) with no Ite operand — rule leaves it alone.
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd A\n"
            "\t\tAssignHavocCmd Y\n"
            "\t\tAssignExpCmd R Add(A Y)\n"
            "\t}"
        ),
        path="<s>",
    )
    res = rewrite_program(
        tac.program, (ADD_ITE_DIST,), symbol_sorts=tac.symbol_sorts
    )
    rhs = _rhs(res.program, "R")
    assert isinstance(rhs, ApplyExpr) and rhs.op == "Add"


def test_sub_ite_dist_left():
    # Sub(Ite(c, T, E), Y) -> Ite(c, Sub(T, Y), Sub(E, Y)).
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd Y\n"
            "\t\tAssignHavocCmd c\n"
            "\t\tAssignExpCmd R Sub(Ite(c 0x5 0x3) Y)\n"
            "\t}"
        ),
        path="<s>",
    )
    res = rewrite_program(
        tac.program, (SUB_ITE_DIST_LEFT,), symbol_sorts=tac.symbol_sorts
    )
    rhs = _rhs(res.program, "R")
    assert isinstance(rhs, ApplyExpr) and rhs.op == "Ite"
    _cond, then_branch, else_branch = rhs.args
    assert isinstance(then_branch, ApplyExpr) and then_branch.op == "Sub"
    assert isinstance(else_branch, ApplyExpr) and else_branch.op == "Sub"


def test_sub_ite_dist_right():
    # Sub(X, Ite(c, T, E)) -> Ite(c, Sub(X, T), Sub(X, E)).
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd A\n"
            "\t\tAssignHavocCmd c\n"
            "\t\tAssignExpCmd R Sub(A Ite(c 0x1 0x0))\n"
            "\t}"
        ),
        path="<s>",
    )
    res = rewrite_program(
        tac.program, (SUB_ITE_DIST_RIGHT,), symbol_sorts=tac.symbol_sorts
    )
    rhs = _rhs(res.program, "R")
    assert isinstance(rhs, ApplyExpr) and rhs.op == "Ite"
    _cond, then_branch, else_branch = rhs.args
    assert isinstance(then_branch, ApplyExpr) and then_branch.op == "Sub"
    assert isinstance(else_branch, ApplyExpr) and else_branch.op == "Sub"


def test_sub_left_ite_does_not_fire_on_right_ite_alone():
    # The left-Ite rule only matches when the LHS is the Ite;
    # right-Ite must be picked up by the sibling rule.
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd A\n"
            "\t\tAssignHavocCmd c\n"
            "\t\tAssignExpCmd R Sub(A Ite(c 0x1 0x0))\n"
            "\t}"
        ),
        path="<s>",
    )
    res = rewrite_program(
        tac.program, (SUB_ITE_DIST_LEFT,), symbol_sorts=tac.symbol_sorts
    )
    rhs = _rhs(res.program, "R")
    assert isinstance(rhs, ApplyExpr) and rhs.op == "Sub"


def test_compose_add_and_sub_on_r727_skeleton():
    # The R727 skeleton from kvault:
    # Sub(Add(A, Ite(c1, 1, 0)), Ite(c2, 1, 0))
    # Distribution should push the outermost Sub/Add inward so the
    # expression becomes nested Ites with Add/Sub leaves over simple
    # operands. The test doesn't pin the whole nested shape — just
    # that the outermost op is an Ite and the outermost Sub/Add are
    # gone from the root.
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd A\n"
            "\t\tAssignHavocCmd c1\n"
            "\t\tAssignHavocCmd c2\n"
            "\t\tAssignExpCmd R Sub(Add(A Ite(c1 0x1 0x0)) Ite(c2 0x1 0x0))\n"
            "\t}",
            syms="A:bv256\n\tR:bv256\n\tc1:bool\n\tc2:bool",
        ),
        path="<s>",
    )
    res = rewrite_program(
        tac.program,
        (ADD_ITE_DIST, SUB_ITE_DIST_LEFT, SUB_ITE_DIST_RIGHT),
        symbol_sorts=tac.symbol_sorts,
    )
    rhs = _rhs(res.program, "R")
    assert isinstance(rhs, ApplyExpr)
    assert rhs.op == "Ite"
