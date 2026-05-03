"""Tests for ctac.rewrite.rules.bool_fold.BOOL_CONST_FOLD."""

from __future__ import annotations

from ctac.ast.nodes import ApplyExpr, AssumeExpCmd, ConstExpr, SymbolRef
from ctac.parse import parse_string
from ctac.rewrite import rewrite_program
from ctac.rewrite.rules.bool_fold import BOOL_CONST_FOLD


def _wrap(body: str, *, syms: str = "B0:bool\n\tB1:bool") -> str:
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


def _assume_cond(prog):
    for b in prog.blocks:
        for cmd in b.commands:
            if isinstance(cmd, AssumeExpCmd):
                return cmd.condition
    raise AssertionError("no assume in program")


def _fold(body: str):
    """Parse + rewrite via BOOL_CONST_FOLD; return the assume condition."""
    tac = parse_string(_wrap(body), path="<s>")
    res = rewrite_program(tac.program, (BOOL_CONST_FOLD,))
    return _assume_cond(res.program), res


T = ConstExpr("true")
F = ConstExpr("false")


def test_lnot_true():
    cond, res = _fold("\t\tAssumeExpCmd LNot(true)")
    assert cond == F
    assert res.hits_by_rule == {"BOOL_FOLD": 1}


def test_lnot_false():
    cond, _ = _fold("\t\tAssumeExpCmd LNot(false)")
    assert cond == T


def test_lnot_non_const_unchanged():
    cond, res = _fold("\t\tAssumeExpCmd LNot(B0)")
    assert cond == ApplyExpr("LNot", (SymbolRef("B0"),))
    assert res.total_hits == 0


def test_land_with_false_short_circuits():
    cond, _ = _fold("\t\tAssumeExpCmd LAnd(true LAnd(false B0))")
    assert cond == F


def test_land_drops_true_operands():
    cond, _ = _fold("\t\tAssumeExpCmd LAnd(true B0)")
    assert cond == SymbolRef("B0")


def test_land_all_true_collapses_to_true():
    cond, _ = _fold("\t\tAssumeExpCmd LAnd(true true)")
    assert cond == T


def test_land_no_consts_unchanged():
    cond, res = _fold("\t\tAssumeExpCmd LAnd(B0 B1)")
    assert cond == ApplyExpr("LAnd", (SymbolRef("B0"), SymbolRef("B1")))
    assert res.total_hits == 0


def test_lor_with_true_short_circuits():
    cond, _ = _fold("\t\tAssumeExpCmd LOr(false true)")
    assert cond == T


def test_lor_drops_false_operands():
    cond, _ = _fold("\t\tAssumeExpCmd LOr(false B0)")
    assert cond == SymbolRef("B0")


def test_lor_all_false_collapses_to_false():
    cond, _ = _fold("\t\tAssumeExpCmd LOr(false false)")
    assert cond == F


def test_lor_no_consts_unchanged():
    cond, res = _fold("\t\tAssumeExpCmd LOr(B0 B1)")
    assert cond == ApplyExpr("LOr", (SymbolRef("B0"), SymbolRef("B1")))
    assert res.total_hits == 0


def test_eq_two_true_consts():
    cond, _ = _fold("\t\tAssumeExpCmd Eq(true true)")
    assert cond == T


def test_eq_true_false():
    cond, _ = _fold("\t\tAssumeExpCmd Eq(true false)")
    assert cond == F


def test_eq_with_one_non_const_unchanged():
    cond, res = _fold("\t\tAssumeExpCmd Eq(true B0)")
    assert cond == ApplyExpr("Eq", (T, SymbolRef("B0")))
    assert res.total_hits == 0


def test_ite_true_picks_then():
    cond, _ = _fold("\t\tAssumeExpCmd Ite(true B0 B1)")
    assert cond == SymbolRef("B0")


def test_ite_false_picks_else():
    cond, _ = _fold("\t\tAssumeExpCmd Ite(false B0 B1)")
    assert cond == SymbolRef("B1")


def test_ite_non_const_guard_unchanged():
    cond, res = _fold("\t\tAssumeExpCmd Ite(B0 true false)")
    assert cond == ApplyExpr("Ite", (SymbolRef("B0"), T, F))
    assert res.total_hits == 0


def test_partial_land_fold_keeps_remaining_args():
    cond, _ = _fold("\t\tAssumeExpCmd LAnd(true LAnd(B0 LAnd(B1 true)))")
    # Engine recurses; both interior LAnds get folded, then outer.
    # Expected: B0 LAnd B1 (after all consts are dropped)
    assert cond == ApplyExpr("LAnd", (SymbolRef("B0"), SymbolRef("B1")))


def test_compound_demorgan_like():
    """LNot of a folded false stays at true."""
    cond, _ = _fold("\t\tAssumeExpCmd LNot(LAnd(false B0))")
    assert cond == T


def test_unrelated_op_returns_none():
    cond, res = _fold(
        "\t\tAssumeExpCmd Eq(B0 B1)",
    )
    # Eq over non-bool-const operands isn't folded.
    assert res.total_hits == 0
    assert cond == ApplyExpr("Eq", (SymbolRef("B0"), SymbolRef("B1")))
