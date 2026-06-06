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


def test_narrow_wrapped_host_fires() -> None:
    """unpurify_div's shape: the div sits under a safe_math_narrow
    wrapper at the RHS top (``R = narrow((tmp - 1) /int W)``). The
    rule matches through it and keeps the wrapper on emission."""
    from ctac.ast.nodes import ApplyExpr

    bv64max = "0xffffffffffffffff"
    body = (
        f"\t\tAssignHavocCmd V\n"
        f"\t\tAssumeExpCmd Le(V {bv64max})\n"
        f"\t\tAssignHavocCmd W\n"
        f"\t\tAssumeExpCmd LAnd(Ge(W 0x1) Le(W {bv64max}))\n"
        f"\t\tAssignExpCmd H0 Apply(safe_math_narrow_bv256:bif IntAdd(V W))\n"
        f"\t\tAssignExpCmd H2 IntSub(H0 0x1(int))\n"
        f"\t\tAssignExpCmd H3 Apply(safe_math_narrow_bv256:bif H2)\n"
        f"\t\tAssignExpCmd I Apply(safe_math_narrow_bv256:bif IntDiv(H3 W))\n"
        f"\t\tAssertCmd Le(I W)\n"
    )
    syms = "V:bv256\n\tW:bv256\n\tH0:bv256\n\tH2:int\n\tH3:bv256\n\tI:bv256"
    tac = parse_string(_wrap(body, syms=syms), path="<s>")
    res = rewrite_program(
        tac.program, (CEIL_DIV_KNUTH,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule.get("CeilDivKnuth", 0) == 1, res.hits_by_rule
    rhs = next(
        c.rhs
        for b in res.program.blocks
        for c in b.commands
        if getattr(c, "lhs", None) == "I"
    )
    # Wrapper preserved: narrow(IntCeilDiv(V, W)).
    assert isinstance(rhs, ApplyExpr) and rhs.op == "Apply"
    inner = rhs.args[1]
    assert isinstance(inner, ApplyExpr) and inner.op == "IntCeilDiv"


def test_narrow_annotation_settles_no_wrap() -> None:
    """The lopu 222_1 shape: W is only known positive (its branch
    bounds don't dominate), so interval inference can't bound V + W
    -- but the safe_math_narrow on the sum is the Prover's no-wrap
    annotation and settles the precondition by fiat."""
    body = (
        "\t\tAssignHavocCmd V\n"
        "\t\tAssumeExpCmd Le(V 0xffffffffffffffffffffff9b789bf000)\n"
        "\t\tAssignHavocCmd W\n"
        "\t\tAssumeExpCmd Gt(W 0x0)\n"
        "\t\tAssignExpCmd T0 IntAdd(V W)\n"
        "\t\tAssignExpCmd T1 Apply(safe_math_narrow_bv256:bif T0)\n"
        "\t\tAssignExpCmd T2 IntSub(T1 0x1)\n"
        "\t\tAssignExpCmd T3 Apply(safe_math_narrow_bv256:bif T2)\n"
        "\t\tAssignExpCmd I Apply(safe_math_narrow_bv256:bif IntDiv(T3 W))\n"
        "\t\tAssertCmd Le(I W)\n"
    )
    syms = (
        "V:bv256\n\tW:bv256\n\tT0:int\n\tT1:bv256\n\tT2:int\n"
        "\tT3:bv256\n\tI:bv256"
    )
    tac = parse_string(_wrap(body, syms=syms), path="<s>")
    res = rewrite_program(
        tac.program, (CEIL_DIV_KNUTH,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule.get("CeilDivKnuth", 0) == 1, res.hits_by_rule


def test_no_narrow_and_unbounded_sum_abstains() -> None:
    """No narrow on the sum and no provable bound: the rule must not
    fire -- the floor-ceil identity needs the true int sum."""
    body = (
        "\t\tAssignHavocCmd V\n"
        "\t\tAssignHavocCmd W\n"
        "\t\tAssumeExpCmd Gt(W 0x0)\n"
        "\t\tAssignExpCmd H0 IntAdd(V W)\n"
        "\t\tAssignExpCmd H2 IntSub(H0 0x1(int))\n"
        "\t\tAssignExpCmd I IntDiv(H2 W)\n"
        "\t\tAssertCmd Le(I W)\n"
    )
    syms = "V:int\n\tW:bv256\n\tH0:int\n\tH2:int\n\tI:int"
    tac = parse_string(_wrap(body, syms=syms), path="<s>")
    res = rewrite_program(
        tac.program, (CEIL_DIV_KNUTH,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule.get("CeilDivKnuth", 0) == 0, res.hits_by_rule
