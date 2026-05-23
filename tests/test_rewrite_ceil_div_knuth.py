"""Unit tests for ``CEIL_DIV_KNUTH``."""

from __future__ import annotations

from ctac.parse import parse_string
from ctac.rewrite import rewrite_program
from ctac.rewrite.rules import CEIL_DIV_KNUTH


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
    """Minimal ``(V + W) - 1) / W`` -> ``IntCeilDiv(V, W)`` lift, with
    V and W in u64 range so the narrow on V+W is a no-op."""
    bv64max = "0xffffffffffffffff"
    body = (
        f"\t\tAssignHavocCmd V\n"
        f"\t\tAssumeExpCmd Le(V {bv64max})\n"
        f"\t\tAssignHavocCmd W\n"
        f"\t\tAssumeExpCmd LAnd(Ge(W 0x1) Le(W {bv64max}))\n"
        f"\t\tAssignExpCmd H0 Apply(safe_math_narrow_bv256:bif IntAdd(V W))\n"
        f"\t\tAssignExpCmd H2 IntSub(H0 0x1(int))\n"
        f"\t\tAssignExpCmd I IntDiv(H2 W)\n"
        f"\t\tAssertCmd Le(I W)\n"
    )
    syms = "V:bv256\n\tW:bv256\n\tH0:bv256\n\tH2:int\n\tI:int"
    tac = parse_string(_wrap(body, syms=syms), path="<s>")
    res = rewrite_program(
        tac.program, (CEIL_DIV_KNUTH,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule.get("CeilDivKnuth", 0) == 1, res.hits_by_rule


def test_non_positive_divisor_abstains() -> None:
    """If W's range allows 0, the floor-ceil identity fails (division
    by zero is undefined), so the rule must not fire."""
    bv64max = "0xffffffffffffffff"
    body = (
        f"\t\tAssignHavocCmd V\n"
        f"\t\tAssumeExpCmd Le(V {bv64max})\n"
        f"\t\tAssignHavocCmd W\n"
        f"\t\tAssumeExpCmd Le(W {bv64max})\n"  # no lower bound on W
        f"\t\tAssignExpCmd H0 Apply(safe_math_narrow_bv256:bif IntAdd(V W))\n"
        f"\t\tAssignExpCmd H2 IntSub(H0 0x1(int))\n"
        f"\t\tAssignExpCmd I IntDiv(H2 W)\n"
        f"\t\tAssertCmd Le(I W)\n"
    )
    syms = "V:bv256\n\tW:bv256\n\tH0:bv256\n\tH2:int\n\tI:int"
    tac = parse_string(_wrap(body, syms=syms), path="<s>")
    res = rewrite_program(
        tac.program, (CEIL_DIV_KNUTH,), symbol_sorts=tac.symbol_sorts
    )
    assert "CeilDivKnuth" not in res.hits_by_rule
