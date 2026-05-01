"""Unit tests for Ite / boolean rewrite rules."""

from __future__ import annotations

from ctac.ast.nodes import ApplyExpr, AssumeExpCmd, ConstExpr, SymbolRef
from ctac.parse import parse_string
from ctac.rewrite import rewrite_program
from ctac.rewrite.rules import (
    BOOL_ABSORB,
    DE_MORGAN,
    EQ_CONST_FOLD,
    EQ_ITE_DIST,
    ITE_BOOL,
    ITE_SAME,
    ITE_SHARED_LEAF,
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
