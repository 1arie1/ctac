"""Tests for MUL_BV_TO_INT / ADD_BV_TO_INT rewrites."""

from __future__ import annotations

from ctac.ast.nodes import ApplyExpr, AssignExpCmd
from ctac.parse import parse_string
from ctac.rewrite import rewrite_program
from ctac.rewrite.rules import ADD_BV_TO_INT, MUL_BV_TO_INT


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
