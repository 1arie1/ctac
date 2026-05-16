"""Tests for ``unpurify_div``."""

from __future__ import annotations

from ctac.ast.nodes import (
    ApplyExpr,
    AssignExpCmd,
    AssumeExpCmd,
    ConstExpr,
    SymbolRef,
)
from ctac.parse import parse_string
from ctac.rewrite.unpurify_div import unpurify_div


def _wrap(body: str, *, syms: str) -> str:
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


def test_short_shape_a_inline():
    """A is a plain SymbolRef inlined into both Le and Gt — no
    intermediate A bindings."""
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd Q\n"
            "\t\tAssignExpCmd tacTmp!div0!1 IntMul(Q B)\n"
            "\t\tAssignExpCmd tacTmp!div2!3 Le(tacTmp!div0!1 A)\n"
            "\t\tAssumeCmd tacTmp!div2!3 \"Division purification\"\n"
            "\t\tAssignExpCmd tacTmp!div4!5 IntAdd(Q 0x1)\n"
            "\t\tAssignExpCmd tacTmp!div6!7 IntMul(tacTmp!div4!5 B)\n"
            "\t\tAssignExpCmd tacTmp!div8!9 Gt(tacTmp!div6!7 A)\n"
            "\t\tAssumeCmd tacTmp!div8!9 \"Division purification\"\n"
            "\t\tAssertCmd Le(Q 0x100)\n"
            "\t}\n",
            syms="Q:bv256\n\tA:bv256\n\tB:bv256",
        ),
        path="<s>",
    )
    res = unpurify_div(tac.program)
    assert res.hits == 1
    cmds = res.program.blocks[0].commands
    # New Q = narrow(IntDiv(A, B)) appears.
    div_cmds = [
        c for c in cmds
        if isinstance(c, AssignExpCmd) and c.lhs == "Q"
    ]
    assert len(div_cmds) == 1
    div_rhs = div_cmds[0].rhs
    assert isinstance(div_rhs, ApplyExpr) and div_rhs.op == "Apply"
    callee, inner = div_rhs.args
    assert callee == SymbolRef("safe_math_narrow_bv256:bif")
    assert isinstance(inner, ApplyExpr) and inner.op == "IntDiv"
    assert inner.args == (SymbolRef("A"), SymbolRef("B"))
    # A B>0 guard was emitted (matches Gt(B, 0(int))).
    guard = [
        c for c in cmds
        if isinstance(c, AssumeExpCmd)
        and isinstance(c.condition, ApplyExpr)
        and c.condition.op == "Gt"
        and c.condition.args == (SymbolRef("B"), ConstExpr("0x0(int)"))
    ]
    assert len(guard) == 1
    # All "Division purification" assumes are gone.
    assert not any(
        isinstance(c, AssumeExpCmd) and "Division purification" in c.raw
        for c in cmds
    )


def test_longer_shape_with_a_binding_chain():
    """A is computed via an intermediate chain (compound expression).
    The chain is preserved; the Div references its tail."""
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd Q\n"
            "\t\tAssignExpCmd tacTmp!div0!1 IntMul(Q B)\n"
            # A chain: tmp_a = X + Y; tmp_b = narrow(tmp_a).
            "\t\tAssignExpCmd tacTmp!div2!3 IntAdd(X Y)\n"
            "\t\tAssignExpCmd tacTmp!div4!5 Apply(safe_math_narrow_bv256:bif tacTmp!div2!3)\n"
            "\t\tAssignExpCmd tacTmp!div6!7 Le(tacTmp!div0!1 tacTmp!div4!5)\n"
            "\t\tAssumeCmd tacTmp!div6!7 \"Division purification\"\n"
            "\t\tAssignExpCmd tacTmp!div8!9 IntAdd(Q 0x1)\n"
            "\t\tAssignExpCmd tacTmp!div10!11 IntMul(tacTmp!div8!9 B)\n"
            "\t\tAssignExpCmd tacTmp!div12!13 Gt(tacTmp!div10!11 tacTmp!div4!5)\n"
            "\t\tAssumeCmd tacTmp!div12!13 \"Division purification\"\n"
            "\t\tAssertCmd Le(Q 0x100)\n"
            "\t}\n",
            syms="Q:bv256\n\tX:bv256\n\tY:bv256\n\tB:bv256",
        ),
        path="<s>",
    )
    res = unpurify_div(tac.program)
    assert res.hits == 1
    cmds = res.program.blocks[0].commands
    div = next(
        c for c in cmds
        if isinstance(c, AssignExpCmd) and c.lhs == "Q"
    )
    # Wrapped: Q = narrow(IntDiv(A_term, B)), where A_term is the
    # last tmp in the chain (its def is kept and still dominates the
    # new use).
    div_rhs = div.rhs
    assert isinstance(div_rhs, ApplyExpr) and div_rhs.op == "Apply"
    _callee, inner = div_rhs.args
    assert isinstance(inner, ApplyExpr) and inner.op == "IntDiv"
    assert inner.args == (SymbolRef("tacTmp!div4!5"), SymbolRef("B"))
    # The intermediate bindings are still in the program.
    intermediate_lhses = [
        c.lhs for c in cmds if isinstance(c, AssignExpCmd)
    ]
    assert "tacTmp!div2!3" in intermediate_lhses
    assert "tacTmp!div4!5" in intermediate_lhses


def test_independent_a_chain_for_gt_side():
    """The upstream tool re-computes A independently for the Gt side
    (different tmp names, same shape). The matcher accepts this; the
    A2 chain becomes dead-after-rewrite."""
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd Q\n"
            "\t\tAssignExpCmd tacTmp!div0!1 IntMul(Q B)\n"
            "\t\tAssignExpCmd tacTmp!div2!3 IntAdd(X Y)\n"
            "\t\tAssignExpCmd tacTmp!div4!5 Apply(safe_math_narrow_bv256:bif tacTmp!div2!3)\n"
            "\t\tAssignExpCmd tacTmp!div6!7 Le(tacTmp!div0!1 tacTmp!div4!5)\n"
            "\t\tAssumeCmd tacTmp!div6!7 \"Division purification\"\n"
            "\t\tAssignExpCmd tacTmp!div8!9 IntAdd(Q 0x1)\n"
            "\t\tAssignExpCmd tacTmp!div10!11 IntMul(tacTmp!div8!9 B)\n"
            # A2 chain: SEPARATE re-computation of A for the Gt side.
            "\t\tAssignExpCmd tacTmp!div12!13 IntAdd(X Y)\n"
            "\t\tAssignExpCmd tacTmp!div14!15 Apply(safe_math_narrow_bv256:bif tacTmp!div12!13)\n"
            "\t\tAssignExpCmd tacTmp!div16!17 Gt(tacTmp!div10!11 tacTmp!div14!15)\n"
            "\t\tAssumeCmd tacTmp!div16!17 \"Division purification\"\n"
            "\t\tAssertCmd Le(Q 0x100)\n"
            "\t}\n",
            syms="Q:bv256\n\tX:bv256\n\tY:bv256\n\tB:bv256",
        ),
        path="<s>",
    )
    res = unpurify_div(tac.program)
    assert res.hits == 1


def test_no_match_when_havoc_not_followed_by_intmul():
    """Pattern requires `P1 = IntMul(Q, B)` as the very next cmd."""
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd Q\n"
            "\t\tAssumeExpCmd Le(Q 0x10)\n"
            "\t\tAssertCmd Le(Q 0x100)\n"
            "\t}\n",
            syms="Q:bv256",
        ),
        path="<s>",
    )
    res = unpurify_div(tac.program)
    assert res.hits == 0


def test_no_match_when_b_differs():
    """The two IntMul cmds must agree on B; otherwise no match."""
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd Q\n"
            "\t\tAssignExpCmd tacTmp!div0!1 IntMul(Q B)\n"
            "\t\tAssignExpCmd tacTmp!div2!3 Le(tacTmp!div0!1 A)\n"
            "\t\tAssumeCmd tacTmp!div2!3 \"Division purification\"\n"
            "\t\tAssignExpCmd tacTmp!div4!5 IntAdd(Q 0x1)\n"
            # Wrong multiplier on the (Q+1) side.
            "\t\tAssignExpCmd tacTmp!div6!7 IntMul(tacTmp!div4!5 C)\n"
            "\t\tAssignExpCmd tacTmp!div8!9 Gt(tacTmp!div6!7 A)\n"
            "\t\tAssumeCmd tacTmp!div8!9 \"Division purification\"\n"
            "\t\tAssertCmd Le(Q 0x100)\n"
            "\t}\n",
            syms="Q:bv256\n\tA:bv256\n\tB:bv256\n\tC:bv256",
        ),
        path="<s>",
    )
    res = unpurify_div(tac.program)
    assert res.hits == 0


def test_emits_trail_substitution_for_each_pattern():
    """Each recognized pattern records a ``Q -> narrow(IntDiv(A, B))``
    trail entry. ``ctac run --model`` on the original .tac uses this
    to recover Q's value when the rewriter DCE'd Q from the SMT."""
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd Q\n"
            "\t\tAssignExpCmd tacTmp!div0!1 IntMul(Q B)\n"
            "\t\tAssignExpCmd tacTmp!div2!3 Le(tacTmp!div0!1 A)\n"
            "\t\tAssumeCmd tacTmp!div2!3 \"Division purification\"\n"
            "\t\tAssignExpCmd tacTmp!div4!5 IntAdd(Q 0x1)\n"
            "\t\tAssignExpCmd tacTmp!div6!7 IntMul(tacTmp!div4!5 B)\n"
            "\t\tAssignExpCmd tacTmp!div8!9 Gt(tacTmp!div6!7 A)\n"
            "\t\tAssumeCmd tacTmp!div8!9 \"Division purification\"\n"
            "\t\tAssertCmd Le(Q 0x100)\n"
            "\t}\n",
            syms="Q:bv256\n\tA:bv256\n\tB:bv256",
        ),
        path="<s>",
    )
    res = unpurify_div(tac.program)
    assert res.hits == 1
    assert len(res.substitutions) == 1
    sub = res.substitutions[0]
    assert sub.var == "Q"
    assert sub.rule == "UnpurifyDiv"
    # Replacement is narrow(IntDiv(A, B)).
    rhs = sub.replacement
    assert isinstance(rhs, ApplyExpr) and rhs.op == "Apply"
    callee, inner = rhs.args
    assert callee == SymbolRef("safe_math_narrow_bv256:bif")
    assert isinstance(inner, ApplyExpr) and inner.op == "IntDiv"
    assert inner.args == (SymbolRef("A"), SymbolRef("B"))


def test_idempotent():
    """A second run on the unpurified program finds nothing."""
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd Q\n"
            "\t\tAssignExpCmd tacTmp!div0!1 IntMul(Q B)\n"
            "\t\tAssignExpCmd tacTmp!div2!3 Le(tacTmp!div0!1 A)\n"
            "\t\tAssumeCmd tacTmp!div2!3 \"Division purification\"\n"
            "\t\tAssignExpCmd tacTmp!div4!5 IntAdd(Q 0x1)\n"
            "\t\tAssignExpCmd tacTmp!div6!7 IntMul(tacTmp!div4!5 B)\n"
            "\t\tAssignExpCmd tacTmp!div8!9 Gt(tacTmp!div6!7 A)\n"
            "\t\tAssumeCmd tacTmp!div8!9 \"Division purification\"\n"
            "\t\tAssertCmd Le(Q 0x100)\n"
            "\t}\n",
            syms="Q:bv256\n\tA:bv256\n\tB:bv256",
        ),
        path="<s>",
    )
    once = unpurify_div(tac.program)
    twice = unpurify_div(once.program)
    assert once.hits == 1
    assert twice.hits == 0
