"""Unit tests for Ite / boolean rewrite rules."""

from __future__ import annotations

from ctac.ast.nodes import ApplyExpr, AssumeExpCmd, ConstExpr, SymbolRef
from ctac.parse import parse_string
from ctac.rewrite import rewrite_program
from ctac.rewrite.rules import (
    ARITH_CONST_FOLD,
    BOOL_ABSORB,
    DE_MORGAN,
    EQ_CONST_FOLD,
    EQ_ITE_DIST,
    EQ_REFLEXIVE,
    INT_MUL_EQ_ZERO,
    ITE_BOOL,
    ITE_SAME,
    ITE_SHARED_LEAF,
    ITE_ZERO_OR_SELF,
    MUL_ZERO_ONE_FOLD,
)


def _assume_cond(prog):
    for b in prog.blocks:
        for cmd in b.commands:
            if isinstance(cmd, AssumeExpCmd):
                return cmd.condition
    raise AssertionError("no assume in program")


def _wrap(body: str, *, syms: str = "R0:bv256\n\tR1:bv256") -> str:
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


def test_eq_const_fold_true():
    tac = parse_string(_wrap("\t\tAssumeExpCmd Eq(0x4 0x4)"), path="<s>")
    res = rewrite_program(tac.program, (EQ_CONST_FOLD,))
    assert res.hits_by_rule == {"EqFold": 1}
    assert _assume_cond(res.program) == ConstExpr("true")


def test_eq_const_fold_false():
    tac = parse_string(_wrap("\t\tAssumeExpCmd Eq(0x4 0x5)"), path="<s>")
    res = rewrite_program(tac.program, (EQ_CONST_FOLD,))
    assert _assume_cond(res.program) == ConstExpr("false")


def test_ite_same_branches():
    tac = parse_string(
        _wrap("\t\tAssumeExpCmd Ite(Eq(R0 0x1) R1 R1)"), path="<s>"
    )
    res = rewrite_program(tac.program, (ITE_SAME,))
    assert res.hits_by_rule == {"IteSame": 1}
    assert _assume_cond(res.program) == SymbolRef("R1")


def test_ite_shared_leaf_shape1_outer_then_eq_inner_else():
    """``Ite(c, X, Ite(c', Y, X))`` -> ``Ite(¬c ∧ c', Y, X)``.

    Motivating shape: 3-pred SSA φ-merge where preds 1 and 3 carry the
    same map and pred 2 differs. The outer-then equals the inner-else;
    rule re-gates on the path that produces the odd value."""
    tac = parse_string(
        _wrap(
            "\t\tAssumeExpCmd Eq(Ite(B0 R0 Ite(B1 R1 R0)) R0)",
            syms="B0:bool\n\tB1:bool\n\tR0:bv256\n\tR1:bv256",
        ),
        path="<s>",
    )
    res = rewrite_program(tac.program, (ITE_SHARED_LEAF,))
    assert res.hits_by_rule == {"IteSharedLeaf": 1}
    cond = _assume_cond(res.program)
    # Top-level: Eq(Ite(¬B0 ∧ B1, R1, R0), R0)
    assert isinstance(cond, ApplyExpr) and cond.op == "Eq"
    ite = cond.args[0]
    assert isinstance(ite, ApplyExpr) and ite.op == "Ite"
    new_cond = ite.args[0]
    assert new_cond == ApplyExpr(
        "LAnd",
        (ApplyExpr("LNot", (SymbolRef("B0"),)), SymbolRef("B1")),
    )
    assert ite.args[1] == SymbolRef("R1")
    assert ite.args[2] == SymbolRef("R0")


def test_ite_shared_leaf_shape2_outer_then_eq_inner_then():
    """``Ite(c, X, Ite(c', X, Y))`` -> ``Ite(c ∨ c', X, Y)``."""
    tac = parse_string(
        _wrap(
            "\t\tAssumeExpCmd Eq(Ite(B0 R0 Ite(B1 R0 R1)) R0)",
            syms="B0:bool\n\tB1:bool\n\tR0:bv256\n\tR1:bv256",
        ),
        path="<s>",
    )
    res = rewrite_program(tac.program, (ITE_SHARED_LEAF,))
    assert res.hits_by_rule == {"IteSharedLeaf": 1}
    cond = _assume_cond(res.program)
    ite = cond.args[0]
    assert isinstance(ite, ApplyExpr) and ite.op == "Ite"
    assert ite.args[0] == ApplyExpr("LOr", (SymbolRef("B0"), SymbolRef("B1")))
    assert ite.args[1] == SymbolRef("R0")
    assert ite.args[2] == SymbolRef("R1")


def test_ite_shared_leaf_shape3_outer_else_eq_inner_then():
    """``Ite(c, Ite(c', X, Y), X)`` -> ``Ite(c ∧ ¬c', Y, X)``."""
    tac = parse_string(
        _wrap(
            "\t\tAssumeExpCmd Eq(Ite(B0 Ite(B1 R0 R1) R0) R0)",
            syms="B0:bool\n\tB1:bool\n\tR0:bv256\n\tR1:bv256",
        ),
        path="<s>",
    )
    res = rewrite_program(tac.program, (ITE_SHARED_LEAF,))
    assert res.hits_by_rule == {"IteSharedLeaf": 1}
    cond = _assume_cond(res.program)
    ite = cond.args[0]
    assert isinstance(ite, ApplyExpr) and ite.op == "Ite"
    assert ite.args[0] == ApplyExpr(
        "LAnd",
        (SymbolRef("B0"), ApplyExpr("LNot", (SymbolRef("B1"),))),
    )
    assert ite.args[1] == SymbolRef("R1")
    assert ite.args[2] == SymbolRef("R0")


def test_ite_shared_leaf_shape4_outer_else_eq_inner_else():
    """``Ite(c, Ite(c', X, Y), Y)`` -> ``Ite(c ∧ c', X, Y)``."""
    tac = parse_string(
        _wrap(
            "\t\tAssumeExpCmd Eq(Ite(B0 Ite(B1 R0 R1) R1) R0)",
            syms="B0:bool\n\tB1:bool\n\tR0:bv256\n\tR1:bv256",
        ),
        path="<s>",
    )
    res = rewrite_program(tac.program, (ITE_SHARED_LEAF,))
    assert res.hits_by_rule == {"IteSharedLeaf": 1}
    cond = _assume_cond(res.program)
    ite = cond.args[0]
    assert isinstance(ite, ApplyExpr) and ite.op == "Ite"
    assert ite.args[0] == ApplyExpr("LAnd", (SymbolRef("B0"), SymbolRef("B1")))
    assert ite.args[1] == SymbolRef("R0")
    assert ite.args[2] == SymbolRef("R1")


def test_ite_shared_leaf_no_match_three_distinct_arms():
    """Three genuinely distinct values: rule should not fire."""
    tac = parse_string(
        _wrap(
            "\t\tAssumeExpCmd Eq(Ite(B0 R0 Ite(B1 R1 R2)) R0)",
            syms="B0:bool\n\tB1:bool\n\tR0:bv256\n\tR1:bv256\n\tR2:bv256",
        ),
        path="<s>",
    )
    res = rewrite_program(tac.program, (ITE_SHARED_LEAF,))
    assert res.hits_by_rule == {}


def test_ite_shared_leaf_cascade_handles_multiple_matches():
    """``Ite(c1, X, Ite(c2, X, Ite(c3, X, Y)))`` — three then-arms all X.
    Bottom-up walk: innermost has no nested Ite; middle matches shape 2
    (X==inner-then), folds to ``Ite(c2 ∨ c3, X, Y)``; outer then matches
    shape 2 again, folding to ``Ite(c1 ∨ c2 ∨ c3, X, Y)``. Two hits in
    one walk. Pin >=2 to confirm the cascade is bottom-up not single-shot."""
    tac = parse_string(
        _wrap(
            "\t\tAssumeExpCmd Eq(Ite(B0 R0 Ite(B1 R0 Ite(B2 R0 R1))) R0)",
            syms="B0:bool\n\tB1:bool\n\tB2:bool\n\tR0:bv256\n\tR1:bv256",
        ),
        path="<s>",
    )
    res = rewrite_program(tac.program, (ITE_SHARED_LEAF,))
    assert res.hits_by_rule.get("IteSharedLeaf", 0) >= 2
    # Final form should be a 2-arm Ite gated by an LOr-of-conditions.
    cond = _assume_cond(res.program)
    ite = cond.args[0]
    assert isinstance(ite, ApplyExpr) and ite.op == "Ite"
    assert ite.args[1] == SymbolRef("R0")
    assert ite.args[2] == SymbolRef("R1")


def test_ite_bool_true_false():
    tac = parse_string(
        _wrap("\t\tAssumeExpCmd Ite(Eq(R0 0x1) true false)"), path="<s>"
    )
    res = rewrite_program(tac.program, (ITE_BOOL,))
    assert res.hits_by_rule == {"IteBool": 1}
    # Collapses to the condition itself.
    assert _assume_cond(res.program) == ApplyExpr("Eq", (SymbolRef("R0"), ConstExpr("0x1")))


def test_ite_bool_false_true():
    tac = parse_string(
        _wrap("\t\tAssumeExpCmd Ite(Eq(R0 0x1) false true)"), path="<s>"
    )
    res = rewrite_program(tac.program, (ITE_BOOL,))
    assert _assume_cond(res.program) == ApplyExpr(
        "LNot", (ApplyExpr("Eq", (SymbolRef("R0"), ConstExpr("0x1"))),)
    )


def test_ite_bool_x_true():
    # Ite(c, X, true) -> LOr(LNot(c), X)
    tac = parse_string(
        _wrap("\t\tAssumeExpCmd Ite(Eq(R0 0x1) Eq(R1 0x1) true)"), path="<s>"
    )
    res = rewrite_program(tac.program, (ITE_BOOL,))
    got = _assume_cond(res.program)
    assert isinstance(got, ApplyExpr) and got.op == "LOr"


def test_bool_absorb_lor_true():
    tac = parse_string(
        _wrap("\t\tAssumeExpCmd LOr(Eq(R0 0x1) true)"), path="<s>"
    )
    res = rewrite_program(tac.program, (BOOL_ABSORB,))
    assert _assume_cond(res.program) == ConstExpr("true")


def test_bool_absorb_lnot_lnot():
    tac = parse_string(
        _wrap("\t\tAssumeExpCmd LNot(LNot(Eq(R0 0x1)))"), path="<s>"
    )
    res = rewrite_program(tac.program, (BOOL_ABSORB,))
    assert _assume_cond(res.program) == ApplyExpr(
        "Eq", (SymbolRef("R0"), ConstExpr("0x1"))
    )


def test_eq_ite_distribute_inner_const():
    # Eq(Ite(c, 0x0, 0x1), 0x1) -> Ite(c, Eq(0x0, 0x1), Eq(0x1, 0x1))
    tac = parse_string(
        _wrap("\t\tAssumeExpCmd Eq(Ite(Eq(R0 0x1) 0x0 0x1) 0x1)"), path="<s>"
    )
    res = rewrite_program(tac.program, (EQ_ITE_DIST,))
    assert res.hits_by_rule.get("EqIte", 0) == 1
    got = _assume_cond(res.program)
    assert isinstance(got, ApplyExpr) and got.op == "Ite"
    # Branches are Eq(0x0, 0x1) and Eq(0x1, 0x1) — still folded only by EqFold.
    assert got.args[1] == ApplyExpr("Eq", (ConstExpr("0x0"), ConstExpr("0x1")))
    assert got.args[2] == ApplyExpr("Eq", (ConstExpr("0x1"), ConstExpr("0x1")))


def test_demorgan_lor_of_nots():
    # LOr(LNot(a), LNot(b)) -> LNot(LAnd(a, b))
    tac = parse_string(
        _wrap("\t\tAssumeExpCmd LOr(LNot(Eq(R0 0x0)) LNot(Eq(R1 0x1)))"),
        path="<s>",
    )
    res = rewrite_program(tac.program, (DE_MORGAN,))
    assert res.hits_by_rule == {"DeMorgan": 1}
    got = _assume_cond(res.program)
    assert isinstance(got, ApplyExpr) and got.op == "LNot"
    inner = got.args[0]
    assert isinstance(inner, ApplyExpr) and inner.op == "LAnd"


def test_demorgan_land_of_nots():
    tac = parse_string(
        _wrap("\t\tAssumeExpCmd LAnd(LNot(Eq(R0 0x0)) LNot(Eq(R1 0x1)))"),
        path="<s>",
    )
    res = rewrite_program(tac.program, (DE_MORGAN,))
    got = _assume_cond(res.program)
    assert isinstance(got, ApplyExpr) and got.op == "LNot"
    inner = got.args[0]
    assert isinstance(inner, ApplyExpr) and inner.op == "LOr"


def test_demorgan_collapses_right_associated_chain():
    """Nested LOr-of-LNots bottom-up folds to a single outer LNot(LAnd(...))."""
    tac_src = _wrap(
        "\t\tAssumeExpCmd LOr(LNot(Eq(R0 0x0)) LOr(LNot(Eq(R1 0x0)) LNot(Eq(R0 0x1))))",
    )
    tac = parse_string(tac_src, path="<s>")
    res = rewrite_program(tac.program, (DE_MORGAN,))
    got = _assume_cond(res.program)
    # Outer is a single LNot; inside is a right-associated LAnd chain of the
    # original positive comparisons (no LNot left at leaves).
    assert isinstance(got, ApplyExpr) and got.op == "LNot"
    n_lnots = 0

    def count_lnots(e):
        nonlocal n_lnots
        if isinstance(e, ApplyExpr):
            if e.op == "LNot":
                n_lnots += 1
            for a in e.args:
                count_lnots(a)

    count_lnots(got)
    assert n_lnots == 1


def test_full_pipeline_collapses_r98_pattern():
    """The R98/R65 idiom from the target TAC collapses to a disjunction of `Ri != 0`."""
    tac_src = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tR14:bv256
\tR15:bv256
\tR16:bv256
\tR17:bv256
\tR98:bv256
}
Program {
\tBlock e Succ [] {
\t\tAssignHavocCmd R14
\t\tAssignHavocCmd R15
\t\tAssignHavocCmd R16
\t\tAssignHavocCmd R17
\t\tAssignExpCmd R98 Ite(Eq(0x0 R14) Ite(Eq(0x0 R15) Ite(Eq(0x0 R16) Ite(Eq(0x0 R17) 0x0 0x1) 0x1) 0x1) 0x1)
\t\tAssumeExpCmd Eq(R98 0x1)
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""
    from ctac.rewrite import default_pipeline

    tac = parse_string(tac_src, path="<s>")
    res = rewrite_program(tac.program, default_pipeline)
    cond = _assume_cond(res.program)
    # Shape: nested LOr of LNot(Eq(0x0, Ri)) terms. Collect the referenced symbols.
    refs: set[str] = set()

    def walk(e):
        if isinstance(e, ApplyExpr):
            for a in e.args:
                walk(a)
        elif isinstance(e, SymbolRef):
            refs.add(e.name)

    walk(cond)
    assert {"R14", "R15", "R16", "R17"}.issubset(refs)
    # Must no longer mention R98 (the original alias).
    assert "R98" not in refs
    # No Ite left in the simplified assume.
    ites = 0

    def count_ites(e):
        nonlocal ites
        if isinstance(e, ApplyExpr):
            if e.op == "Ite":
                ites += 1
            for a in e.args:
                count_ites(a)

    count_ites(cond)
    assert ites == 0


def test_eq_reflexive_folds_same_symbol():
    """``Eq(R0, R0)`` -> ``true``."""
    tac = parse_string(
        _wrap("\t\tAssumeExpCmd Eq(R0 R0)"), path="<s>"
    )
    res = rewrite_program(tac.program, (EQ_REFLEXIVE,))
    assert res.hits_by_rule == {"EqReflexive": 1}
    assert _assume_cond(res.program) == ConstExpr("true")


def test_eq_reflexive_skips_distinct_symbols():
    """``Eq(R0, R1)`` does not fold."""
    tac = parse_string(
        _wrap("\t\tAssumeExpCmd Eq(R0 R1)"), path="<s>"
    )
    res = rewrite_program(tac.program, (EQ_REFLEXIVE,))
    assert res.hits_by_rule == {}


def test_eq_reflexive_folds_same_const():
    """Structural equality covers constants too: ``Eq(0x4, 0x4)`` -> ``true``."""
    tac = parse_string(
        _wrap("\t\tAssumeExpCmd Eq(0x4 0x4)"), path="<s>"
    )
    res = rewrite_program(tac.program, (EQ_REFLEXIVE,))
    assert res.hits_by_rule == {"EqReflexive": 1}
    assert _assume_cond(res.program) == ConstExpr("true")


# ---------------------------------------------------------------------------
# IntMulEqZero: Eq(IntMul(X, K), 0) -> Eq(X, 0) when K != 0 (Int-domain only)
# ---------------------------------------------------------------------------


def test_int_mul_eq_zero_direct():
    """``Eq(IntMul(R0, 0x4(int)), 0)`` -> ``Eq(R0, 0)``."""
    tac = parse_string(
        _wrap("\t\tAssumeExpCmd Eq(IntMul(R0 0x4(int)) 0x0)"),
        path="<s>",
    )
    res = rewrite_program(tac.program, (INT_MUL_EQ_ZERO,))
    assert res.hits_by_rule == {"IntMulEqZero": 1}
    cond = _assume_cond(res.program)
    assert cond == ApplyExpr("Eq", (SymbolRef("R0"), ConstExpr("0x0")))


def test_int_mul_eq_zero_const_on_left():
    """K on the left arg of IntMul; symmetric."""
    tac = parse_string(
        _wrap("\t\tAssumeExpCmd Eq(IntMul(0x4(int) R0) 0x0)"),
        path="<s>",
    )
    res = rewrite_program(tac.program, (INT_MUL_EQ_ZERO,))
    assert res.hits_by_rule == {"IntMulEqZero": 1}
    cond = _assume_cond(res.program)
    assert cond == ApplyExpr("Eq", (SymbolRef("R0"), ConstExpr("0x0")))


def test_int_mul_eq_zero_zero_on_left():
    """Zero const on the left of the outer Eq."""
    tac = parse_string(
        _wrap("\t\tAssumeExpCmd Eq(0x0 IntMul(R0 0x4(int)))"),
        path="<s>",
    )
    res = rewrite_program(tac.program, (INT_MUL_EQ_ZERO,))
    assert res.hits_by_rule == {"IntMulEqZero": 1}


def test_int_mul_eq_zero_unsound_on_bv_mul():
    """``Mul`` (bv-modular) is NOT folded — would be unsound."""
    tac = parse_string(
        _wrap("\t\tAssumeExpCmd Eq(Mul(R0 0x4) 0x0)"),
        path="<s>",
    )
    res = rewrite_program(tac.program, (INT_MUL_EQ_ZERO,))
    assert res.hits_by_rule == {}


def test_int_mul_eq_zero_skips_zero_constant_multiplier():
    """``K == 0`` is the precondition's negation; rule abstains."""
    tac = parse_string(
        _wrap("\t\tAssumeExpCmd Eq(IntMul(R0 0x0(int)) 0x0)"),
        path="<s>",
    )
    res = rewrite_program(tac.program, (INT_MUL_EQ_ZERO,))
    assert res.hits_by_rule == {}


def test_int_mul_eq_zero_via_lookthrough():
    """The IntMul arrives via a SymbolRef whose def is the IntMul."""
    body = (
        "\t\tAssignExpCmd R1 IntMul(R0 0x4(int))\n"
        "\t\tAssumeExpCmd Eq(R1 0x0)"
    )
    tac = parse_string(_wrap(body), path="<s>")
    res = rewrite_program(tac.program, (INT_MUL_EQ_ZERO,))
    assert res.hits_by_rule == {"IntMulEqZero": 1}
    cond = _assume_cond(res.program)
    assert cond == ApplyExpr("Eq", (SymbolRef("R0"), ConstExpr("0x0")))


# ---------------------------------------------------------------------------
# IteZeroOrSelf: Ite(Eq(X,0), 0, F(X)) -> F(X) for zero-preserving F
# ---------------------------------------------------------------------------


def test_ite_zero_or_self_identity_branch():
    """``Ite(Eq(R0, 0), 0, R0)`` -> ``R0``."""
    tac = parse_string(
        _wrap("\t\tAssumeExpCmd Eq(Ite(Eq(R0 0x0) 0x0 R0) R0)"),
        path="<s>",
    )
    res = rewrite_program(tac.program, (ITE_ZERO_OR_SELF,))
    assert res.hits_by_rule == {"IteZeroOrSelf": 1}


def test_ite_zero_or_self_x_branch_then_zero_else():
    """``Ite(Eq(R0, 0), R0, 0)`` -> ``0``."""
    tac = parse_string(
        _wrap("\t\tAssumeExpCmd Eq(Ite(Eq(R0 0x0) R0 0x0) 0x0)"),
        path="<s>",
    )
    res = rewrite_program(tac.program, (ITE_ZERO_OR_SELF,))
    assert res.hits_by_rule == {"IteZeroOrSelf": 1}


def test_ite_zero_or_self_div_branch():
    """``Ite(Eq(R0, 0), 0, Div(R0, K))`` -> ``Div(R0, K)`` — K-independent."""
    tac = parse_string(
        _wrap(
            "\t\tAssumeExpCmd Eq("
            "Ite(Eq(R0 0x0) 0x0 Div(R0 0x4000)) "
            "Div(R0 0x4000)"
            ")"
        ),
        path="<s>",
    )
    res = rewrite_program(tac.program, (ITE_ZERO_OR_SELF,))
    assert res.hits_by_rule == {"IteZeroOrSelf": 1}


def test_ite_zero_or_self_div_via_lookthrough():
    """X-side branch arrives via a SymbolRef whose def is ``Div(X, K)``."""
    body = (
        "\t\tAssignExpCmd R1 Div(R0 0x4000)\n"
        "\t\tAssignExpCmd R2 Ite(Eq(R0 0x0) 0x0 R1)\n"
        "\t\tAssumeExpCmd Eq(R2 R1)"
    )
    tac = parse_string(_wrap(body), path="<s>")
    res = rewrite_program(tac.program, (ITE_ZERO_OR_SELF,))
    assert res.hits_by_rule == {"IteZeroOrSelf": 1}


def test_ite_zero_or_self_mul_branch():
    """``IntMul(X, _)`` is zero-preserving on either arg."""
    tac = parse_string(
        _wrap(
            "\t\tAssumeExpCmd Eq("
            "Ite(Eq(R0 0x0) 0x0 IntMul(0x4(int) R0)) "
            "IntMul(0x4(int) R0)"
            ")"
        ),
        path="<s>",
    )
    res = rewrite_program(tac.program, (ITE_ZERO_OR_SELF,))
    assert res.hits_by_rule == {"IteZeroOrSelf": 1}


def test_ite_zero_or_self_unrelated_branch_no_fold():
    """``Ite(Eq(R0, 0), 0, R1)`` does NOT fold — R1 is not zero-when-R0=0."""
    tac = parse_string(
        _wrap("\t\tAssumeExpCmd Eq(Ite(Eq(R0 0x0) 0x0 R1) R1)"),
        path="<s>",
    )
    res = rewrite_program(tac.program, (ITE_ZERO_OR_SELF,))
    assert res.hits_by_rule == {}


# ---------------------------------------------------------------------------
# ArithConstFold: binary const-const arithmetic / bitwise
# ---------------------------------------------------------------------------


def test_arith_const_fold_int_add():
    """``IntAdd(0x2(int), 0x3(int))`` -> ``0x5(int)`` — non-modular."""
    tac = parse_string(
        _wrap("\t\tAssumeExpCmd Eq(IntAdd(0x2(int) 0x3(int)) 0x5(int))"),
        path="<s>",
    )
    res = rewrite_program(tac.program, (ARITH_CONST_FOLD,))
    assert res.hits_by_rule.get("ArithConstFold", 0) >= 1


def test_arith_const_fold_bv_mul_wraps():
    """bv ``Mul`` folds mod 2^256."""
    huge = "0x8000000000000000000000000000000000000000000000000000000000000000"
    tac = parse_string(
        _wrap(f"\t\tAssumeExpCmd Eq(Mul({huge} 0x2) 0x0)"),
        path="<s>",
    )
    res = rewrite_program(tac.program, (ARITH_CONST_FOLD,))
    # 2^255 * 2 = 2^256 == 0 mod 2^256 — bv wrap.
    assert res.hits_by_rule.get("ArithConstFold", 0) >= 1


def test_arith_const_fold_div_zero_abstains():
    """Div by zero: rule abstains rather than introducing UB."""
    tac = parse_string(
        _wrap("\t\tAssumeExpCmd Eq(Div(0x10 0x0) 0x0)"),
        path="<s>",
    )
    res = rewrite_program(tac.program, (ARITH_CONST_FOLD,))
    assert "ArithConstFold" not in res.hits_by_rule


def test_arith_const_fold_one_symbolic_no_fold():
    """At least one symbolic operand: no fold."""
    tac = parse_string(
        _wrap("\t\tAssumeExpCmd Eq(IntAdd(R0 0x3(int)) 0x5(int))"),
        path="<s>",
    )
    res = rewrite_program(tac.program, (ARITH_CONST_FOLD,))
    assert "ArithConstFold" not in res.hits_by_rule


# ---------------------------------------------------------------------------
# MulZeroOne: X*0 -> 0; X*1 -> X
# ---------------------------------------------------------------------------


def test_mul_zero_one_int_mul_zero():
    """``IntMul(R0, 0(int))`` -> ``0(int)``."""
    tac = parse_string(
        _wrap("\t\tAssumeExpCmd Eq(IntMul(R0 0x0(int)) 0x0(int))"),
        path="<s>",
    )
    res = rewrite_program(tac.program, (MUL_ZERO_ONE_FOLD,))
    assert res.hits_by_rule == {"MulZeroOne": 1}


def test_mul_zero_one_int_mul_one_identity():
    """``IntMul(R0, 1(int))`` -> ``R0``."""
    tac = parse_string(
        _wrap("\t\tAssumeExpCmd Eq(IntMul(R0 0x1(int)) R0)"),
        path="<s>",
    )
    res = rewrite_program(tac.program, (MUL_ZERO_ONE_FOLD,))
    assert res.hits_by_rule == {"MulZeroOne": 1}


def test_mul_zero_one_bv_mul_zero():
    """``Mul(R0, 0)`` -> ``0`` — sound under bv-modular semantics."""
    tac = parse_string(
        _wrap("\t\tAssumeExpCmd Eq(Mul(R0 0x0) 0x0)"),
        path="<s>",
    )
    res = rewrite_program(tac.program, (MUL_ZERO_ONE_FOLD,))
    assert res.hits_by_rule == {"MulZeroOne": 1}


def test_mul_zero_one_no_fold_on_const_two():
    """``IntMul(R0, 2(int))`` is not absorbed."""
    tac = parse_string(
        _wrap("\t\tAssumeExpCmd Eq(IntMul(R0 0x2(int)) R0)"),
        path="<s>",
    )
    res = rewrite_program(tac.program, (MUL_ZERO_ONE_FOLD,))
    assert "MulZeroOne" not in res.hits_by_rule
