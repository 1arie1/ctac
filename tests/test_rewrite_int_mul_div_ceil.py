"""Unit tests for ``INT_MUL_DIV_CEIL``."""

from __future__ import annotations

from ctac.parse import parse_string
from ctac.rewrite import rewrite_program
from ctac.rewrite.rules import INT_MUL_DIV_CEIL


def _wrap(body: str, *, syms: str) -> str:
    return f"""TACSymbolTable {{
\tUserDefined {{
\t}}
\tBuiltinFunctions {{
\t\tsafe_math_narrow_bv256:JSON{{"#class":"vc.data.TACBuiltInFunction.SafeMathNarrow","returnSort":{{"#class":"tac.Tag.Bit256"}}}}
\t}}
\tUninterpretedFunctions {{
\t}}
\t{syms}
}}
Program {{
\tBlock e Succ [] {{
{body}
\t}}
}}
Axioms {{
}}
Metas {{
  "0": []
}}
"""


def test_basic_pattern_fires() -> None:
    """``IntCeilDiv(narrow(IntMul(A, B)), W) -> IntMulDivCeil(A, B, W)``
    when both A, B are u64-bounded (so A*B <= 2^128 << 2^256) and
    W >= 1."""
    bv64max = "0xffffffffffffffff"
    body = (
        f"\t\tAssignHavocCmd A\n"
        f"\t\tAssumeExpCmd Le(A {bv64max})\n"
        f"\t\tAssignHavocCmd B\n"
        f"\t\tAssumeExpCmd Le(B {bv64max})\n"
        f"\t\tAssignHavocCmd W\n"
        f"\t\tAssumeExpCmd LAnd(Ge(W 0x1) Le(W {bv64max}))\n"
        f"\t\tAssignExpCmd P IntMul(A B)\n"
        f"\t\tAssignExpCmd R Apply(safe_math_narrow_bv256:bif P)\n"
        f"\t\tAssignExpCmd I IntCeilDiv(R W)\n"
        f"\t\tAssertCmd Le(I W)\n"
    )
    syms = "A:bv256\n\tB:bv256\n\tW:bv256\n\tP:int\n\tR:bv256\n\tI:int"
    tac = parse_string(_wrap(body, syms=syms), path="<s>")
    res = rewrite_program(
        tac.program, (INT_MUL_DIV_CEIL,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule.get("IntMulDivCeil", 0) == 1, res.hits_by_rule


def test_non_positive_divisor_abstains() -> None:
    bv64max = "0xffffffffffffffff"
    body = (
        f"\t\tAssignHavocCmd A\n"
        f"\t\tAssumeExpCmd Le(A {bv64max})\n"
        f"\t\tAssignHavocCmd B\n"
        f"\t\tAssumeExpCmd Le(B {bv64max})\n"
        f"\t\tAssignHavocCmd W\n"
        f"\t\tAssumeExpCmd Le(W {bv64max})\n"  # no lower bound
        f"\t\tAssignExpCmd P IntMul(A B)\n"
        f"\t\tAssignExpCmd R Apply(safe_math_narrow_bv256:bif P)\n"
        f"\t\tAssignExpCmd I IntCeilDiv(R W)\n"
        f"\t\tAssertCmd Le(I W)\n"
    )
    syms = "A:bv256\n\tB:bv256\n\tW:bv256\n\tP:int\n\tR:bv256\n\tI:int"
    tac = parse_string(_wrap(body, syms=syms), path="<s>")
    res = rewrite_program(
        tac.program, (INT_MUL_DIV_CEIL,), symbol_sorts=tac.symbol_sorts
    )
    assert "IntMulDivCeil" not in res.hits_by_rule
