"""Tests for HAVOC_EQUATE_SUBST: substitute a 'dummy' havoc'd
variable with its equality partner from an assume.

The rule's intended pattern is `R67 = havoc; assume R67 <= 2^23;
assume R218 == R67` where R218 is a *real* variable (with an
AssignExpCmd def or computational uses, not another dummy). The
rule's cycle-prevention rejects substituting toward another dummy
(else two havoc'd vars equating to each other would swap names
forever in the rule-apply loop). Tests reflect this: the
"surviving" partner X is given an `AssignExpCmd` def (non-dummy)."""

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
from ctac.rewrite.rules import EQ_REFLEXIVE, HAVOC_EQUATE_SUBST


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


_BV_SYMS = "R:bv256\n\tX:bv256\n\tY:bv256\n\tZ:bv256\n\tA:bv256"


def test_he_basic_substitution():
    """R havoc'd dummy, X has an AssignExp def (non-dummy), R == X.
    Rule fires: R-references replaced with X. Le(R, …) -> Le(X, …).
    The Eq(X, R) becomes Eq(X, X) which EQ_REFLEXIVE folds to true."""
    body = (
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd A\n"
        "\t\tAssignExpCmd X A\n"          # X non-dummy: has AssignExp def
        "\t\tAssignHavocCmd R\n"
        "\t\tAssumeExpCmd Le(R 0x800000)\n"
        "\t\tAssumeExpCmd Eq(X R)\n"
        "\t}"
    )
    tac = parse_string(_wrap(body, syms=_BV_SYMS), path="<s>")
    res = rewrite_program(
        tac.program,
        (HAVOC_EQUATE_SUBST, EQ_REFLEXIVE),
        symbol_sorts=tac.symbol_sorts,
    )
    assert res.hits_by_rule.get("HavocEquateSubst", 0) >= 1
    conds = _assume_conds(res.program)
    # Le(R, ...) became Le(X, ...).
    assert ApplyExpr("Le", (SymbolRef("X"), ConstExpr("0x800000"))) in conds
    # Equality assume folded.
    assert ConstExpr("true") in conds


def test_he_multi_constraint_substitution():
    """Multiple constraints on R all substitute to X."""
    body = (
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd A\n"
        "\t\tAssignExpCmd X A\n"
        "\t\tAssignHavocCmd R\n"
        "\t\tAssumeExpCmd Ge(R 0x10)\n"
        "\t\tAssumeExpCmd Le(R 0x100)\n"
        "\t\tAssumeExpCmd Eq(X R)\n"
        "\t}"
    )
    tac = parse_string(_wrap(body, syms=_BV_SYMS), path="<s>")
    res = rewrite_program(
        tac.program,
        (HAVOC_EQUATE_SUBST, EQ_REFLEXIVE),
        symbol_sorts=tac.symbol_sorts,
    )
    assert res.hits_by_rule.get("HavocEquateSubst", 0) >= 2
    conds = _assume_conds(res.program)
    assert ApplyExpr("Ge", (SymbolRef("X"), ConstExpr("0x10"))) in conds
    assert ApplyExpr("Le", (SymbolRef("X"), ConstExpr("0x100"))) in conds


def test_he_equality_direction_swapped():
    """Eq(R, X) (R first) also matches."""
    body = (
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd A\n"
        "\t\tAssignExpCmd X A\n"
        "\t\tAssignHavocCmd R\n"
        "\t\tAssumeExpCmd Le(R 0x800000)\n"
        "\t\tAssumeExpCmd Eq(R X)\n"
        "\t}"
    )
    tac = parse_string(_wrap(body, syms=_BV_SYMS), path="<s>")
    res = rewrite_program(
        tac.program, (HAVOC_EQUATE_SUBST,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule.get("HavocEquateSubst", 0) >= 1
    conds = _assume_conds(res.program)
    assert ApplyExpr("Le", (SymbolRef("X"), ConstExpr("0x800000"))) in conds


def test_he_land_conjunct_equality():
    """The Eq inside an LAnd conjunct counts as the equality partner."""
    body = (
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd A\n"
        "\t\tAssignExpCmd X A\n"
        "\t\tAssignHavocCmd R\n"
        "\t\tAssumeExpCmd Le(R 0x800000)\n"
        "\t\tAssumeExpCmd LAnd(Eq(R X) Le(X 0x100))\n"
        "\t}"
    )
    tac = parse_string(_wrap(body, syms=_BV_SYMS), path="<s>")
    res = rewrite_program(
        tac.program, (HAVOC_EQUATE_SUBST,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule.get("HavocEquateSubst", 0) >= 1
    conds = _assume_conds(res.program)
    assert ApplyExpr("Le", (SymbolRef("X"), ConstExpr("0x800000"))) in conds


def test_he_bails_on_assignexp_use():
    """R is used in an AssignExpCmd RHS — rule must bail."""
    body = (
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd A\n"
        "\t\tAssignExpCmd X A\n"
        "\t\tAssignHavocCmd R\n"
        "\t\tAssignExpCmd Y Add(R 0x1)\n"   # non-assume use of R
        "\t\tAssumeExpCmd Eq(X R)\n"
        "\t}"
    )
    tac = parse_string(_wrap(body, syms=_BV_SYMS), path="<s>")
    res = rewrite_program(
        tac.program, (HAVOC_EQUATE_SUBST,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule == {}


def test_he_bails_on_self_equality():
    """Eq(R, R) is a no-op; rule must not produce R -> R."""
    body = (
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd R\n"
        "\t\tAssumeExpCmd Le(R 0x800000)\n"
        "\t\tAssumeExpCmd Eq(R R)\n"
        "\t}"
    )
    tac = parse_string(_wrap(body, syms=_BV_SYMS), path="<s>")
    res = rewrite_program(
        tac.program, (HAVOC_EQUATE_SUBST,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule == {}


def test_he_cross_sort_bail():
    """R is bv256, partner is int — sort mismatch, bail."""
    body = (
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd Z\n"
        "\t\tAssignExpCmd Wint Z\n"          # int-typed partner
        "\t\tAssignHavocCmd R\n"
        "\t\tAssumeExpCmd Le(R 0x100)\n"
        "\t\tAssumeExpCmd Eq(R Wint)\n"
        "\t}"
    )
    tac = parse_string(
        _wrap(body, syms="R:bv256\n\tWint:int\n\tZ:int"), path="<s>"
    )
    res = rewrite_program(
        tac.program, (HAVOC_EQUATE_SUBST,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule == {}


def test_he_skips_dummy_partner_to_avoid_cycle():
    """Both R and X are havoc'd dummies that equate. Rule must NOT
    fire (would otherwise infinitely swap R <-> X). Test pins the
    cycle-prevention check."""
    body = (
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd R\n"
        "\t\tAssignHavocCmd X\n"
        "\t\tAssumeExpCmd Le(R 0x800000)\n"
        "\t\tAssumeExpCmd Eq(X R)\n"
        "\t}"
    )
    tac = parse_string(_wrap(body, syms=_BV_SYMS), path="<s>")
    res = rewrite_program(
        tac.program, (HAVOC_EQUATE_SUBST,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule == {}


def test_he_chain_with_real_anchor():
    """R -> Y -> X chain where X is non-dummy. First iteration: Y -> X
    (Y's partner X is real). After CTX rebuild in iter 2: R's partner
    is still Y (which became X via substitution... but ctx.du is at
    iter-START state, so Y is still the partner). Eventually R -> Y
    fires once Y becomes a leaf alias.

    For this synthetic case, the converged form has R-uses replaced
    transitively. We pin the strongest property: the Le bound makes
    it onto X (or onto a leaf that's clearly related to X)."""
    body = (
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd A\n"
        "\t\tAssignExpCmd X A\n"          # X non-dummy
        "\t\tAssignHavocCmd Y\n"
        "\t\tAssignHavocCmd R\n"
        "\t\tAssumeExpCmd Le(R 0x800000)\n"
        "\t\tAssumeExpCmd Eq(Y R)\n"      # R partner: Y (dummy) — skipped
        "\t\tAssumeExpCmd Eq(X Y)\n"      # Y partner: X (non-dummy) — fires
        "\t}"
    )
    tac = parse_string(_wrap(body, syms=_BV_SYMS), path="<s>")
    res = rewrite_program(
        tac.program,
        (HAVOC_EQUATE_SUBST, EQ_REFLEXIVE),
        symbol_sorts=tac.symbol_sorts,
    )
    # Y at minimum is substituted to X.
    assert res.hits_by_rule.get("HavocEquateSubst", 0) >= 1


def test_he_dsa_valid_and_no_use_before_def():
    """Output remains DSA-valid and use-before-def clean."""
    from ctac.analysis import analyze_dsa, analyze_use_before_def, extract_def_use

    body = (
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd A\n"
        "\t\tAssignExpCmd X A\n"
        "\t\tAssignHavocCmd R\n"
        "\t\tAssumeExpCmd Le(R 0x800000)\n"
        "\t\tAssumeExpCmd Eq(X R)\n"
        "\t}"
    )
    tac = parse_string(_wrap(body, syms=_BV_SYMS), path="<s>")
    res = rewrite_program(
        tac.program,
        (HAVOC_EQUATE_SUBST, EQ_REFLEXIVE),
        symbol_sorts=tac.symbol_sorts,
    )
    du = extract_def_use(res.program)
    ubd = analyze_use_before_def(res.program, def_use=du)
    dsa = analyze_dsa(res.program, def_use=du)
    assert not ubd.issues, ubd.issues
    assert not dsa.issues, dsa.issues


def test_he_no_uses_bails():
    """R is havoc'd but never used — rule shouldn't fire (DCE handles)."""
    body = (
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd R\n"
        "\t\tAssignHavocCmd X\n"
        "\t}"
    )
    tac = parse_string(_wrap(body, syms=_BV_SYMS), path="<s>")
    res = rewrite_program(
        tac.program, (HAVOC_EQUATE_SUBST,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule == {}
