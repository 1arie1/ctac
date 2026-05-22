"""Unit tests for ``MULDIV_TO_FULL_PRODUCT_DIV``."""

from __future__ import annotations

from ctac.ast.nodes import ApplyExpr, AssumeExpCmd, SymbolRef
from ctac.parse import parse_string
from ctac.rewrite import rewrite_program
from ctac.rewrite.rules import MULDIV_TO_FULL_PRODUCT_DIV


def _wrap(body: str, *, syms: str) -> str:
    return f"""TACSymbolTable {{
\tUserDefined {{
\t}}
\tBuiltinFunctions {{
\t\tsafe_math_narrow_bv256:JSON{{"#class":"vc.data.TACBuiltInFunction.SafeMathNarrow.Implicit","returnSort":{{"bits":256}}}}
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


def _last_assume(prog):
    last = None
    for b in prog.blocks:
        for cmd in b.commands:
            if isinstance(cmd, AssumeExpCmd):
                last = cmd
    return last


def test_muldiv_to_full_product_div_basic():
    """When V = narrow(IntMul(A, narrow(IntMul(M, B)))) exists in
    scope, ``IntMulDiv(A, B, K)`` rewrites to ``Div(V, M*K)``."""
    body = (
        "\t\tAssignHavocCmd A\n"
        "\t\tAssignHavocCmd B\n"
        "\t\tAssignExpCmd W Apply(safe_math_narrow_bv256:bif "
        "IntMul(0x4000(int) B))\n"
        "\t\tAssignExpCmd V Apply(safe_math_narrow_bv256:bif IntMul(A W))\n"
        # IntMulDiv(A, B, 2^50). The rule should rewrite to Div(V, 2^64).
        "\t\tAssumeExpCmd Le(IntMulDiv(A B 0x4000000000000) 0xffffffff)\n"
        "\t\tAssertCmd false\n"
    )
    syms = "A:bv256\n\tB:bv256\n\tW:bv256\n\tV:bv256"
    tac = parse_string(_wrap(body, syms=syms), path="<s>")
    res = rewrite_program(
        tac.program,
        (MULDIV_TO_FULL_PRODUCT_DIV,),
        symbol_sorts=tac.symbol_sorts,
    )
    assert res.hits_by_rule.get("MulDivToFullProductDiv", 0) >= 1
    last = _last_assume(res.program)
    assert last is not None
    cond = last.condition
    assert isinstance(cond, ApplyExpr) and cond.op == "Le"
    # The IntMulDiv arg should now be Div(V, 2^64) (= 0x10000000000000000).
    div_expr = cond.args[0]
    assert isinstance(div_expr, ApplyExpr) and div_expr.op == "Div"
    assert div_expr.args[0] == SymbolRef("V")


def test_no_v_in_scope_skips():
    """No matching V → rule abstains."""
    body = (
        "\t\tAssignHavocCmd A\n"
        "\t\tAssignHavocCmd B\n"
        "\t\tAssumeExpCmd Le(IntMulDiv(A B 0x4000000000000) 0xffffffff)\n"
        "\t\tAssertCmd false\n"
    )
    tac = parse_string(_wrap(body, syms="A:bv256\n\tB:bv256"), path="<s>")
    res = rewrite_program(
        tac.program,
        (MULDIV_TO_FULL_PRODUCT_DIV,),
        symbol_sorts=tac.symbol_sorts,
    )
    assert "MulDivToFullProductDiv" not in res.hits_by_rule


def test_swapped_operands_in_intmul():
    """V = narrow(IntMul(W, A)) — operand ordering swapped — still matches."""
    body = (
        "\t\tAssignHavocCmd A\n"
        "\t\tAssignHavocCmd B\n"
        "\t\tAssignExpCmd W Apply(safe_math_narrow_bv256:bif "
        "IntMul(B 0x4000(int)))\n"
        # V's IntMul has W, A (swapped).
        "\t\tAssignExpCmd V Apply(safe_math_narrow_bv256:bif IntMul(W A))\n"
        "\t\tAssumeExpCmd Le(IntMulDiv(A B 0x4000000000000) 0xffffffff)\n"
        "\t\tAssertCmd false\n"
    )
    syms = "A:bv256\n\tB:bv256\n\tW:bv256\n\tV:bv256"
    tac = parse_string(_wrap(body, syms=syms), path="<s>")
    res = rewrite_program(
        tac.program,
        (MULDIV_TO_FULL_PRODUCT_DIV,),
        symbol_sorts=tac.symbol_sorts,
    )
    assert res.hits_by_rule.get("MulDivToFullProductDiv", 0) >= 1


def test_narrow_around_int_typed_intermediate():
    """Real-world shape: ``V = narrow(I)`` where ``I = IntMul(A, W)``
    is an int-typed intermediate (not the IntMul directly under the
    narrow). Lookthrough on the inner resolves the chain."""
    body = (
        "\t\tAssignHavocCmd A\n"
        "\t\tAssignHavocCmd B\n"
        "\t\tAssignExpCmd W Apply(safe_math_narrow_bv256:bif "
        "IntMul(0x4000(int) B))\n"
        "\t\tAssignExpCmd I IntMul(A W)\n"
        "\t\tAssignExpCmd V Apply(safe_math_narrow_bv256:bif I)\n"
        "\t\tAssumeExpCmd Le(IntMulDiv(A B 0x4000000000000) 0xffffffff)\n"
        "\t\tAssertCmd false\n"
    )
    syms = "A:bv256\n\tB:bv256\n\tW:bv256\n\tI:int\n\tV:bv256"
    tac = parse_string(_wrap(body, syms=syms), path="<s>")
    res = rewrite_program(
        tac.program,
        (MULDIV_TO_FULL_PRODUCT_DIV,),
        symbol_sorts=tac.symbol_sorts,
    )
    assert res.hits_by_rule.get("MulDivToFullProductDiv", 0) >= 1
