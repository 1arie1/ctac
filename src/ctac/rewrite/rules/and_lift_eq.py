"""Pattern: ``LAnd(Ge(X, c), Eq(X, c)) -> Eq(X, c)``.

The bv decrement idiom ``Add(BV256_MAX, R)`` lowered via
``ADD_BV_MAX_TO_ITE`` produces ``Ite(R >= 1, R - 1, BV256_MAX)``.
A surrounding ``Eq(_, 0)`` then distributes through the Ite via
``EqIte``, the ``Eq(BV256_MAX, 0) = false`` arm folds, ``IteBool``
collapses ``Ite(c, T, false)`` to ``LAnd(c, T)``, and ``EqSubZero``
normalizes the surviving ``Eq(IntSub(R, 1), 0)`` conjunct to
``Eq(R, 1)``. The result is ``LAnd(Ge(R, 1), Eq(R, 1))`` —
structurally awkward, but logically just ``R == 1``.

This rule recognises the shape and lifts it to the bare equality
(generally ``Eq(X, c)``). The simplified form unblocks downstream
rules (``EqIte``, ``IteSame``, ``SelectOverStore``) that key on a
singleton equality. ``LAND_EQ_CONST_PRUNE`` covers the same shape
when ``X`` is a plain symbol; this rule carries the compound-``X``
case (the decrement host is often a ``narrow(...)`` expression).

Soundness: ``Eq(X, c)`` already implies ``X ≥ c`` (equality decides
any comparison against the same operand pair), so the ``Ge(X, c)``
conjunct is redundant.
"""

from __future__ import annotations

from ctac.ast.nodes import ApplyExpr, TacExpr
from ctac.rewrite.context import RewriteCtx
from ctac.rewrite.framework import Rule
from ctac.rewrite.rules.common import const_to_int


def _match_ge_const(expr: TacExpr) -> "tuple[TacExpr, int] | None":
    """Match ``Ge(X, c)`` (constant on the right). Returns ``(X, c)``."""
    if not (
        isinstance(expr, ApplyExpr)
        and expr.op == "Ge"
        and len(expr.args) == 2
    ):
        return None
    c = const_to_int(expr.args[1])
    if c is None:
        return None
    return expr.args[0], c


def _match_eq_const(expr: TacExpr) -> "tuple[TacExpr, int, TacExpr] | None":
    """Match ``Eq(X, c)`` / ``Eq(c, X)`` with ``c`` constant.

    Returns ``(X, c_int, eq_expr)`` where ``eq_expr`` is the original
    ``Eq`` node so callers can preserve its lexical form.
    """
    if not (
        isinstance(expr, ApplyExpr)
        and expr.op == "Eq"
        and len(expr.args) == 2
    ):
        return None
    a, b = expr.args
    c = const_to_int(b)
    if c is not None:
        return a, c, expr
    c = const_to_int(a)
    if c is not None:
        return b, c, expr
    return None


def _rewrite_and_lift_eq(expr: TacExpr, _ctx: RewriteCtx) -> TacExpr | None:
    if not (
        isinstance(expr, ApplyExpr)
        and expr.op == "LAnd"
        and len(expr.args) == 2
    ):
        return None
    for i, j in ((0, 1), (1, 0)):
        ge = _match_ge_const(expr.args[i])
        eq = _match_eq_const(expr.args[j])
        if ge is None or eq is None:
            continue
        x_ge, c_ge = ge
        x_eq, c_eq, eq_expr = eq
        if c_ge != c_eq or x_ge != x_eq:
            continue
        return eq_expr
    return None


AND_LIFT_EQ_DECREMENT = Rule(
    name="AndLiftEq",
    fn=_rewrite_and_lift_eq,
    description=(
        "LAnd(Ge(X, c), Eq(X, c)) -> Eq(X, c). The Eq already implies "
        "Ge(X, c), so the conjunction collapses. Recovers the "
        "singleton-equality shape after the bv decrement idiom "
        "(Add(BV256_MAX, X)) was unfolded by ADD_BV_MAX_TO_ITE and "
        "EqSubZero normalized the difference-vs-zero conjunct."
    ),
)
