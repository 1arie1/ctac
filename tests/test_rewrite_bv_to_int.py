"""Tests for MUL_BV_TO_INT / ADD_BV_TO_INT rewrites."""

from __future__ import annotations

from ctac.ast.nodes import ApplyExpr, AssignExpCmd, ConstExpr
from ctac.parse import parse_string
from ctac.rewrite import rewrite_program
from ctac.rewrite.rules import (
    ADD_BV_MAX_TO_ITE,
    ADD_BV_TO_INT,
    ITE_COND_FOLD,
    MUL_BV_TO_INT,
)


def _wrap(body: str, *, syms: str = "R850:bv256\n\tR801:bv256") -> str:
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


def test_mul_div_k_k_pattern_lifts_to_intmul():
    # R801 = (R850 / 2^14) * 2^14. R850 is bv256 so in [0, 2^256).
    # Div by 2^14 gives [0, 2^242 - 1]; * 2^14 gives [0, 2^256 - 2^14],
    # which fits. Expected rewrite: Mul -> IntMul (Div stays bare).
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd R850\n"
            "\t\tAssignExpCmd R801 Mul(Div(R850 0x4000) 0x4000)\n"
            "\t}"
        ),
        path="<s>",
    )
    res = rewrite_program(
        tac.program, (MUL_BV_TO_INT,), symbol_sorts=tac.symbol_sorts
    )
    rhs = _rhs(res.program, "R801")
    assert isinstance(rhs, ApplyExpr)
    assert rhs.op == "IntMul"
    # Inner Div untouched.
    inner = rhs.args[0]
    assert isinstance(inner, ApplyExpr) and inner.op == "Div"


def test_mul_doesnt_lift_when_range_is_unknown():
    # No sort info (int) and no assume — range inference yields None,
    # so the rule cannot prove the result fits.
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd A\n"
            "\t\tAssignHavocCmd B\n"
            "\t\tAssignExpCmd C Mul(A B)\n"
            "\t}",
            syms="A:int\n\tB:int\n\tC:int",
        ),
        path="<s>",
    )
    res = rewrite_program(
        tac.program, (MUL_BV_TO_INT,), symbol_sorts=tac.symbol_sorts
    )
    rhs = _rhs(res.program, "C")
    assert isinstance(rhs, ApplyExpr)
    assert rhs.op == "Mul"


def test_mul_doesnt_lift_when_product_could_overflow():
    # Two bv256 factors: upper product is (2^256 - 1)^2 ≈ 2^512, way
    # beyond bv256. The rule must NOT lift.
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd A\n"
            "\t\tAssignHavocCmd B\n"
            "\t\tAssignExpCmd C Mul(A B)\n"
            "\t}",
            syms="A:bv256\n\tB:bv256\n\tC:bv256",
        ),
        path="<s>",
    )
    res = rewrite_program(
        tac.program, (MUL_BV_TO_INT,), symbol_sorts=tac.symbol_sorts
    )
    rhs = _rhs(res.program, "C")
    assert isinstance(rhs, ApplyExpr)
    assert rhs.op == "Mul"


def test_add_small_ranges_lifts_to_intadd():
    # Assume-bounded small integers: 0 <= A <= 100, 0 <= B <= 100.
    # A + B fits trivially in bv256.
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd A\n"
            "\t\tAssignHavocCmd B\n"
            "\t\tAssumeExpCmd Le(A 0x64)\n"
            "\t\tAssumeExpCmd Ge(A 0x0)\n"
            "\t\tAssumeExpCmd Le(B 0x64)\n"
            "\t\tAssumeExpCmd Ge(B 0x0)\n"
            "\t\tAssignExpCmd C Add(A B)\n"
            "\t}",
            syms="A:bv256\n\tB:bv256\n\tC:bv256",
        ),
        path="<s>",
    )
    res = rewrite_program(
        tac.program, (ADD_BV_TO_INT,), symbol_sorts=tac.symbol_sorts
    )
    rhs = _rhs(res.program, "C")
    assert isinstance(rhs, ApplyExpr)
    assert rhs.op == "IntAdd"


def test_add_doesnt_lift_when_sum_could_overflow():
    # Two bv256 factors: 2*(2^256 - 1) > 2^256. Rule must NOT lift.
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd A\n"
            "\t\tAssignHavocCmd B\n"
            "\t\tAssignExpCmd C Add(A B)\n"
            "\t}",
            syms="A:bv256\n\tB:bv256\n\tC:bv256",
        ),
        path="<s>",
    )
    res = rewrite_program(
        tac.program, (ADD_BV_TO_INT,), symbol_sorts=tac.symbol_sorts
    )
    rhs = _rhs(res.program, "C")
    assert isinstance(rhs, ApplyExpr)
    assert rhs.op == "Add"


# --- ADD_BV_MAX_TO_ITE + ITE_COND_FOLD ------------------------------------
# `Add(BV256_MAX, X)` is rewritten UNCONDITIONALLY to the Ite
# `Ite(X >= 1, X - 1, BV256_MAX)`. Downstream ITE_COND_FOLD uses
# range inference to collapse the Ite when `X >= 1` or `X == 0` is
# decidable. Together they subsume the old gated "IntSub" rule.

_BV256_MAX_HEX = "0x" + "f" * 64  # 2^256 - 1


def test_add_bv_max_to_ite_always_produces_ite_const_on_left():
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd X\n"
            f"\t\tAssignExpCmd R Add({_BV256_MAX_HEX} X)\n"
            "\t}",
            syms="X:bv256\n\tR:bv256",
        ),
        path="<s>",
    )
    res = rewrite_program(
        tac.program, (ADD_BV_MAX_TO_ITE,), symbol_sorts=tac.symbol_sorts
    )
    rhs = _rhs(res.program, "R")
    assert isinstance(rhs, ApplyExpr)
    assert rhs.op == "Ite"
    cond, then_branch, else_branch = rhs.args
    assert isinstance(cond, ApplyExpr) and cond.op == "Ge"
    assert cond.args[1] == ConstExpr("0x1")
    assert isinstance(then_branch, ApplyExpr) and then_branch.op == "IntSub"
    assert isinstance(else_branch, ConstExpr)


def test_add_bv_max_to_ite_handles_const_on_right():
    # Add is commutative; the rule must handle either operand order.
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd X\n"
            f"\t\tAssignExpCmd R Add(X {_BV256_MAX_HEX})\n"
            "\t}",
            syms="X:bv256\n\tR:bv256",
        ),
        path="<s>",
    )
    res = rewrite_program(
        tac.program, (ADD_BV_MAX_TO_ITE,), symbol_sorts=tac.symbol_sorts
    )
    rhs = _rhs(res.program, "R")
    assert isinstance(rhs, ApplyExpr)
    assert rhs.op == "Ite"


def test_add_bv_max_to_ite_does_not_fire_for_other_constants():
    # Only BV256_MAX triggers the rule; a different const left alone.
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd X\n"
            "\t\tAssignExpCmd R Add(0x1234 X)\n"
            "\t}",
            syms="X:bv256\n\tR:bv256",
        ),
        path="<s>",
    )
    res = rewrite_program(
        tac.program, (ADD_BV_MAX_TO_ITE,), symbol_sorts=tac.symbol_sorts
    )
    rhs = _rhs(res.program, "R")
    assert isinstance(rhs, ApplyExpr)
    assert rhs.op == "Add"


def test_add_bv_max_to_ite_plus_cond_fold_collapses_when_x_ge_1():
    # Composition test: with a dominating `Ge(X, 1)` assume, the emitted
    # Ite's condition is always true, and ITE_COND_FOLD collapses the
    # whole expression to `IntSub(X, 1)`.
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd X\n"
            "\t\tAssumeExpCmd Ge(X 0x1)\n"
            f"\t\tAssignExpCmd R Add({_BV256_MAX_HEX} X)\n"
            "\t}",
            syms="X:bv256\n\tR:bv256",
        ),
        path="<s>",
    )
    res = rewrite_program(
        tac.program,
        (ADD_BV_MAX_TO_ITE, ITE_COND_FOLD),
        symbol_sorts=tac.symbol_sorts,
    )
    rhs = _rhs(res.program, "R")
    assert isinstance(rhs, ApplyExpr)
    assert rhs.op == "IntSub"
    assert rhs.args[1] == ConstExpr("0x1")


def test_ite_cond_fold_does_not_fire_when_range_is_ambiguous():
    # With no lower-bound assume on X, X could be 0 or >=1, so the
    # condition `X >= 1` is undecidable and the Ite must stay.
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd X\n"
            f"\t\tAssignExpCmd R Add({_BV256_MAX_HEX} X)\n"
            "\t}",
            syms="X:bv256\n\tR:bv256",
        ),
        path="<s>",
    )
    res = rewrite_program(
        tac.program,
        (ADD_BV_MAX_TO_ITE, ITE_COND_FOLD),
        symbol_sorts=tac.symbol_sorts,
    )
    rhs = _rhs(res.program, "R")
    assert isinstance(rhs, ApplyExpr)
    assert rhs.op == "Ite"
