"""Unit tests for ``CEIL_TO_MULTIPLE``."""

from __future__ import annotations

from ctac.parse import parse_string
from ctac.rewrite import rewrite_program
from ctac.rewrite.rules import CEIL_TO_MULTIPLE


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


def test_basic_pattern_fires():
    """Minimal synthetic version of the SBF ``ceil_to_multiple(V, 2^14)``
    chunked encoding. Rule should fire once and rewrite ``X`` to
    ``IntMul(K, IntCeilDiv(V, K))`` (wrapped in safe_math_narrow_bv256).
    """
    K = 0x4000  # 2^14
    bv64max = "0xffffffffffffffff"
    body = (
        f"\t\tAssignHavocCmd V\n"
        f"\t\tAssumeExpCmd Le(V {bv64max})\n"
        f"\t\tAssignExpCmd R_floor IntMul(Div(V 0x{K:x}(int)) 0x{K:x}(int))\n"
        f"\t\tAssignExpCmd M_plus "
        f"Apply(safe_math_narrow_bv256:bif IntAdd(0x{K:x}(int) R_floor))\n"
        f"\t\tAssignExpCmd Cm Mod(M_plus 0x10000000000000000)\n"
        f"\t\tAssignExpCmd R_rem Mod(V 0x{K:x}(int))\n"
        f"\t\tAssignExpCmd B Eq(R_rem 0x0)\n"
        f"\t\tAssumeExpCmd LOr(B Le(M_plus {bv64max}))\n"
        f"\t\tAssignExpCmd X Ite(B R_floor Cm)\n"
        f"\t\tAssertCmd Le(X {bv64max})\n"
    )
    syms = (
        "V:bv256\n"
        "\tR_floor:bv256\n"
        "\tM_plus:bv256\n"
        "\tCm:bv256\n"
        "\tR_rem:bv256\n"
        "\tB:bool\n"
        "\tX:bv256"
    )
    tac = parse_string(_wrap(body, syms=syms), path="<s>")
    res = rewrite_program(
        tac.program, (CEIL_TO_MULTIPLE,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule.get("CeilToMultiple", 0) == 1, res.hits_by_rule


def test_no_wrap_guard_abstains():
    """Without the ``LOr(B, Le(M_plus, 2^64-1))`` assume, the rule must
    abstain — Cm = M_plus mod 2^64 could differ from K*ceil(V/K)."""
    K = 0x4000
    bv64max = "0xffffffffffffffff"
    body = (
        f"\t\tAssignHavocCmd V\n"
        f"\t\tAssumeExpCmd Le(V {bv64max})\n"
        f"\t\tAssignExpCmd R_floor IntMul(Div(V 0x{K:x}(int)) 0x{K:x}(int))\n"
        f"\t\tAssignExpCmd M_plus "
        f"Apply(safe_math_narrow_bv256:bif IntAdd(0x{K:x}(int) R_floor))\n"
        f"\t\tAssignExpCmd Cm Mod(M_plus 0x10000000000000000)\n"
        f"\t\tAssignExpCmd R_rem Mod(V 0x{K:x}(int))\n"
        f"\t\tAssignExpCmd B Eq(R_rem 0x0)\n"
        # NO wrap-guard assume here.
        f"\t\tAssignExpCmd X Ite(B R_floor Cm)\n"
        f"\t\tAssertCmd Le(X {bv64max})\n"
    )
    syms = (
        "V:bv256\n"
        "\tR_floor:bv256\n"
        "\tM_plus:bv256\n"
        "\tCm:bv256\n"
        "\tR_rem:bv256\n"
        "\tB:bool\n"
        "\tX:bv256"
    )
    tac = parse_string(_wrap(body, syms=syms), path="<s>")
    res = rewrite_program(
        tac.program, (CEIL_TO_MULTIPLE,), symbol_sorts=tac.symbol_sorts
    )
    assert "CeilToMultiple" not in res.hits_by_rule
