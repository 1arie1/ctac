"""Tests for HAVOC_EQUATE_FOLD: drop a dummy havoc + its constraints
by moving them onto the equality partner at the equality's position.

Sister to HAVOC_EQUATE_SUBST. Where SUBST forward-substitutes R -> X
at every R-use (only sound when X dominates R's uses), FOLD drops R
entirely and moves R's constraints into the position of the equality
assume — the SBF-frontend shape where X is defined AFTER R."""

from __future__ import annotations

from ctac.ast.nodes import (
    ApplyExpr,
    AssignHavocCmd,
    AssumeExpCmd,
    ConstExpr,
    SymbolRef,
)
from ctac.parse import parse_string
from ctac.rewrite import rewrite_program
from ctac.rewrite.rules import HAVOC_EQUATE_FOLD


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


def _assume_conds(prog):
    return [cmd.condition for b in prog.blocks for cmd in b.commands if isinstance(cmd, AssumeExpCmd)]


def _havoc_lhses(prog):
    return [cmd.lhs for b in prog.blocks for cmd in b.commands if isinstance(cmd, AssignHavocCmd)]


_SYMS = "R:bv256\n\tX:bv256\n\tY:bv256\n\tA:bv256\n\tZ:bv256"


def test_fold_basic_motivating_pattern():
    """The canonical SBF shape: R = havoc; assume Le(R, c); ...
    AssignExpCmd X = ...; assume Eq(R, X). R has no other uses.
    Same block. FOLD drops R + Le, rewrites Eq to Le(X, c)."""
    body = (
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd R\n"
        "\t\tAssumeExpCmd Le(R 0x800000)\n"
        "\t\tAssignHavocCmd A\n"
        "\t\tAssignExpCmd X A\n"
        "\t\tAssumeExpCmd Eq(R X)\n"
        "\t}"
    )
    tac = parse_string(_wrap(body, syms=_SYMS), path="<s>")
    res = rewrite_program(
        tac.program, (HAVOC_EQUATE_FOLD,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule == {"HavocEquateFold": 1}
    # R's havoc def + Le constraint dropped; only A's havoc remains.
    assert "R" not in _havoc_lhses(res.program)
    assert "A" in _havoc_lhses(res.program)
    # The Eq assume's condition is now Le(X, 0x800000).
    conds = _assume_conds(res.program)
    assert ApplyExpr("Le", (SymbolRef("X"), ConstExpr("0x800000"))) in conds
    # The original Le(R, c) is gone.
    for c in conds:
        assert SymbolRef("R") not in (c.args if isinstance(c, ApplyExpr) else ())


def test_fold_eq_direction_swapped():
    """Eq(X, R) (X first) also matches."""
    body = (
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd R\n"
        "\t\tAssumeExpCmd Le(R 0x800000)\n"
        "\t\tAssignHavocCmd A\n"
        "\t\tAssignExpCmd X A\n"
        "\t\tAssumeExpCmd Eq(X R)\n"
        "\t}"
    )
    tac = parse_string(_wrap(body, syms=_SYMS), path="<s>")
    res = rewrite_program(
        tac.program, (HAVOC_EQUATE_FOLD,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule == {"HavocEquateFold": 1}
    assert "R" not in _havoc_lhses(res.program)
    conds = _assume_conds(res.program)
    assert ApplyExpr("Le", (SymbolRef("X"), ConstExpr("0x800000"))) in conds


def test_fold_multiple_constraints_become_LAnd():
    """R has two constraints: Ge and Le. Both move; combined into
    LAnd at the Eq position."""
    body = (
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd R\n"
        "\t\tAssumeExpCmd Ge(R 0x10)\n"
        "\t\tAssumeExpCmd Le(R 0x100)\n"
        "\t\tAssignHavocCmd A\n"
        "\t\tAssignExpCmd X A\n"
        "\t\tAssumeExpCmd Eq(R X)\n"
        "\t}"
    )
    tac = parse_string(_wrap(body, syms=_SYMS), path="<s>")
    res = rewrite_program(
        tac.program, (HAVOC_EQUATE_FOLD,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule == {"HavocEquateFold": 1}
    assert "R" not in _havoc_lhses(res.program)
    conds = _assume_conds(res.program)
    # Single LAnd-conjunction left: LAnd(Ge(X, 0x10), Le(X, 0x100)).
    expected = ApplyExpr(
        "LAnd",
        (
            ApplyExpr("Ge", (SymbolRef("X"), ConstExpr("0x10"))),
            ApplyExpr("Le", (SymbolRef("X"), ConstExpr("0x100"))),
        ),
    )
    assert expected in conds


def test_fold_bails_no_constraints():
    """R is havoc'd with only the equality and no other constraints
    — nothing to move; rule must bail."""
    body = (
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd R\n"
        "\t\tAssignHavocCmd A\n"
        "\t\tAssignExpCmd X A\n"
        "\t\tAssumeExpCmd Eq(R X)\n"
        "\t}"
    )
    tac = parse_string(_wrap(body, syms=_SYMS), path="<s>")
    res = rewrite_program(
        tac.program, (HAVOC_EQUATE_FOLD,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule == {}


def test_fold_bails_when_X_is_dummy():
    """X is also a havoc dummy — would create R<->X cycle; rule bails."""
    body = (
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd R\n"
        "\t\tAssumeExpCmd Le(R 0x800000)\n"
        "\t\tAssignHavocCmd X\n"
        "\t\tAssumeExpCmd Eq(R X)\n"
        "\t}"
    )
    tac = parse_string(_wrap(body, syms=_SYMS), path="<s>")
    res = rewrite_program(
        tac.program, (HAVOC_EQUATE_FOLD,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule == {}


def test_fold_bails_on_assignexp_use_of_R():
    """R is used outside assumes (in an AssignExpCmd RHS) — not a
    dummy; rule must bail."""
    body = (
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd R\n"
        "\t\tAssumeExpCmd Le(R 0x800000)\n"
        "\t\tAssignHavocCmd A\n"
        "\t\tAssignExpCmd X A\n"
        "\t\tAssignExpCmd Y Add(R 0x1)\n"   # non-assume use of R
        "\t\tAssumeExpCmd Eq(R X)\n"
        "\t}"
    )
    tac = parse_string(_wrap(body, syms=_SYMS), path="<s>")
    res = rewrite_program(
        tac.program, (HAVOC_EQUATE_FOLD,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule == {}


def test_fold_bails_cross_block_constraint():
    """R def in block e, constraint Le in block e2 — different
    blocks; rule must bail (path-conditional unsoundness)."""
    body = (
        "\tBlock e Succ [e2] {\n"
        "\t\tAssignHavocCmd R\n"
        "\t\tAssignHavocCmd A\n"
        "\t\tAssignExpCmd X A\n"
        "\t\tAssumeExpCmd Eq(R X)\n"
        "\t\tJumpCmd e2\n"
        "\t}\n"
        "\tBlock e2 Succ [] {\n"
        "\t\tAssumeExpCmd Le(R 0x800000)\n"   # cross-block constraint
        "\t}"
    )
    tac = parse_string(_wrap(body, syms=_SYMS), path="<s>")
    res = rewrite_program(
        tac.program, (HAVOC_EQUATE_FOLD,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule == {}


def test_fold_bails_cross_block_def():
    """R def in block e, Eq in block e2 — different blocks; rule
    must bail (the user's stated requirement: 'assume R = X in same
    block as R')."""
    body = (
        "\tBlock e Succ [e2] {\n"
        "\t\tAssignHavocCmd R\n"
        "\t\tAssumeExpCmd Le(R 0x800000)\n"
        "\t\tJumpCmd e2\n"
        "\t}\n"
        "\tBlock e2 Succ [] {\n"
        "\t\tAssignHavocCmd A\n"
        "\t\tAssignExpCmd X A\n"
        "\t\tAssumeExpCmd Eq(R X)\n"          # cross-block from R def
        "\t}"
    )
    tac = parse_string(_wrap(body, syms=_SYMS), path="<s>")
    res = rewrite_program(
        tac.program, (HAVOC_EQUATE_FOLD,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule == {}


def test_fold_bails_cross_sort():
    """R bv256, X int — sort mismatch; rule bails."""
    body = (
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd R\n"
        "\t\tAssumeExpCmd Le(R 0x100)\n"
        "\t\tAssignHavocCmd Z\n"
        "\t\tAssignExpCmd Wint Z\n"
        "\t\tAssumeExpCmd Eq(R Wint)\n"
        "\t}"
    )
    tac = parse_string(
        _wrap(body, syms="R:bv256\n\tWint:int\n\tZ:int"), path="<s>"
    )
    res = rewrite_program(
        tac.program, (HAVOC_EQUATE_FOLD,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule == {}


def test_fold_chained_user_pattern():
    """The user's specific pattern: R65 = havoc; Le(R65, c); R67 =
    havoc; Le(R67, c); R218 = havoc + computational uses;
    assume Eq(R65, R218); assume Eq(R218, R67). The two
    `Eq(R, R218)` shapes both fold — R65 and R67 get dropped, their
    Le constraints move onto R218."""
    body = (
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd R65\n"
        "\t\tAssumeExpCmd Le(R65 0x800000)\n"
        "\t\tAssignHavocCmd R67\n"
        "\t\tAssumeExpCmd Le(R67 0x800000)\n"
        "\t\tAssignHavocCmd R218\n"           # R218 = havoc but...
        "\t\tAssignHavocCmd A\n"
        "\t\tAssignExpCmd Y Add(R218 A)\n"   # ...has a computational use
        "\t\tAssumeExpCmd Eq(R65 R218)\n"
        "\t\tAssumeExpCmd Eq(R218 R67)\n"
        "\t}"
    )
    tac = parse_string(
        _wrap(body, syms="R65:bv256\n\tR67:bv256\n\tR218:bv256\n\tA:bv256\n\tY:bv256"),
        path="<s>",
    )
    res = rewrite_program(
        tac.program, (HAVOC_EQUATE_FOLD,), symbol_sorts=tac.symbol_sorts
    )
    # Both R65 and R67 fold via the rule.
    assert res.hits_by_rule.get("HavocEquateFold", 0) >= 2
    assert "R65" not in _havoc_lhses(res.program)
    assert "R67" not in _havoc_lhses(res.program)
    assert "R218" in _havoc_lhses(res.program)


def test_fold_dsa_valid_and_no_use_before_def():
    """Output remains DSA-valid and use-before-def clean."""
    from ctac.analysis import analyze_dsa, analyze_use_before_def, extract_def_use

    body = (
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd R\n"
        "\t\tAssumeExpCmd Le(R 0x800000)\n"
        "\t\tAssignHavocCmd A\n"
        "\t\tAssignExpCmd X A\n"
        "\t\tAssumeExpCmd Eq(R X)\n"
        "\t}"
    )
    tac = parse_string(_wrap(body, syms=_SYMS), path="<s>")
    res = rewrite_program(
        tac.program, (HAVOC_EQUATE_FOLD,), symbol_sorts=tac.symbol_sorts
    )
    du = extract_def_use(res.program)
    ubd = analyze_use_before_def(res.program, def_use=du)
    dsa = analyze_dsa(res.program, def_use=du)
    assert not ubd.issues, ubd.issues
    assert not dsa.issues, dsa.issues
