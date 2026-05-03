"""Symbol substitution over TAC expressions."""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import replace

from ctac.ast.nodes import ApplyExpr, ConstExpr, SymbolRef, TacExpr


def subst_symbol_to_expr(
    expr: TacExpr, mapping: Mapping[str, TacExpr]
) -> TacExpr:
    """Return a copy of ``expr`` with every ``SymbolRef`` whose name is
    in ``mapping`` replaced by the mapped expression.

    Distinct from :func:`subst_symbol` (which renames SymbolRefs):
    this substitutes a ``SymbolRef`` for an arbitrary expression
    (typically ``ConstExpr``). Used by ``ctac pin``'s ``--bind`` and
    auto-RC-bind passes.

    Recursively descends into :class:`ApplyExpr` arguments. Substituted
    expressions are NOT re-traversed (mappings should not contain
    self-references; cycle-handling is not provided).
    """
    if not mapping:
        return expr
    if isinstance(expr, SymbolRef):
        rep = mapping.get(expr.name)
        if rep is None:
            return expr
        return rep
    if isinstance(expr, ConstExpr):
        return expr
    if isinstance(expr, ApplyExpr):
        new_args = tuple(subst_symbol_to_expr(a, mapping) for a in expr.args)
        if new_args == expr.args:
            return expr
        return replace(expr, args=new_args)
    return expr


def subst_symbol(expr: TacExpr, mapping: Mapping[str, str]) -> TacExpr:
    """Return a copy of ``expr`` with every ``SymbolRef`` whose name is
    in ``mapping`` replaced by a ``SymbolRef`` carrying the mapped name.

    Recursively descends into :class:`ApplyExpr` arguments.
    :class:`ConstExpr` and :class:`SymbolRef`-not-in-mapping nodes are
    returned unchanged. Subclasses of :class:`SymbolRef`
    (e.g. ``SymbolWeakRef``) preserve their concrete type.
    """
    if not mapping:
        return expr
    if isinstance(expr, SymbolRef):
        new_name = mapping.get(expr.name)
        if new_name is None or new_name == expr.name:
            return expr
        return replace(expr, name=new_name)
    if isinstance(expr, ConstExpr):
        return expr
    if isinstance(expr, ApplyExpr):
        new_args = tuple(subst_symbol(a, mapping) for a in expr.args)
        if new_args == expr.args:
            return expr
        return replace(expr, args=new_args)
    return expr
