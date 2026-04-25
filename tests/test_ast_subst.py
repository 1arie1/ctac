"""Tests for ctac.ast.subst.subst_symbol."""

from __future__ import annotations

from ctac.ast.nodes import ApplyExpr, ConstExpr, SymbolRef
from ctac.ast.subst import subst_symbol


def test_symbol_ref_matched():
    assert subst_symbol(SymbolRef("X"), {"X": "X_new"}) == SymbolRef("X_new")


def test_symbol_ref_unmatched():
    out = subst_symbol(SymbolRef("Y"), {"X": "X_new"})
    assert out == SymbolRef("Y")


def test_const_expr_passthrough():
    out = subst_symbol(ConstExpr("0x5"), {"X": "X_new"})
    assert out == ConstExpr("0x5")


def test_apply_expr_recurses():
    expr = ApplyExpr(op="Add", args=(SymbolRef("X"), ConstExpr("0x1")))
    out = subst_symbol(expr, {"X": "X_new"})
    assert out == ApplyExpr(op="Add", args=(SymbolRef("X_new"), ConstExpr("0x1")))


def test_nested_apply_expr():
    inner = ApplyExpr(op="Mul", args=(SymbolRef("X"), SymbolRef("Y")))
    outer = ApplyExpr(op="Add", args=(inner, SymbolRef("X")))
    out = subst_symbol(outer, {"X": "X_new"})
    assert out == ApplyExpr(
        op="Add",
        args=(
            ApplyExpr(op="Mul", args=(SymbolRef("X_new"), SymbolRef("Y"))),
            SymbolRef("X_new"),
        ),
    )


def test_no_change_returns_same_object():
    # Optimisation: when the substitution doesn't fire, the expression
    # is returned unchanged (helps callers detect "did anything change").
    expr = ApplyExpr(op="Add", args=(SymbolRef("Y"), ConstExpr("0x1")))
    out = subst_symbol(expr, {"X": "X_new"})
    assert out is expr


def test_empty_mapping_is_noop():
    expr = ApplyExpr(op="Add", args=(SymbolRef("X"), ConstExpr("0x1")))
    out = subst_symbol(expr, {})
    assert out is expr


def test_multiple_mappings_applied():
    expr = ApplyExpr(op="Sub", args=(SymbolRef("X"), SymbolRef("Y")))
    out = subst_symbol(expr, {"X": "X_new", "Y": "Y_new"})
    assert out == ApplyExpr(op="Sub", args=(SymbolRef("X_new"), SymbolRef("Y_new")))
