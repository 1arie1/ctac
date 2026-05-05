"""Pattern: ``LAnd(Ge(X, c), Eq(IntSub(X, c), 0)) -> Eq(X, c)``.

The bv decrement idiom ``Add(BV256_MAX, R)`` lowered via
``ADD_BV_MAX_TO_ITE`` produces ``Ite(R >= 1, R - 1, BV256_MAX)``.
A surrounding ``Eq(_, 0)`` then distributes through the Ite via
``EqIte``, the ``Eq(BV256_MAX, 0) = false`` arm folds, and ``IteBool``
collapses ``Ite(c, T, false)`` to ``LAnd(c, T)``. The result is
``LAnd(Ge(R, 1), Eq(IntSub(R, 1), 0))`` — structurally awkward, but
logically just ``R == 1``.

This rule recognises the shape and lifts it back to ``Eq(R, 1)``
(generally ``Eq(X, c)``). The simplified form unblocks downstream
rules (``EqIte``, ``IteSame``, ``SelectOverStore``) that were keying
on a singleton equality before the decrement was unfolded.

Soundness: ``Eq(IntSub(X, c), 0)`` ⟺ ``X = c``, which already implies
``X ≥ c``, so the ``Ge(X, c)`` conjunct is redundant. ``IntSub`` runs
in the unbounded Int domain so there's no wrap to worry about.
"""

from __future__ import annotations

from ctac.ast.nodes import ApplyExpr, ConstExpr, TacExpr
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


def _match_int_sub_eq_zero(
    expr: TacExpr,
) -> "tuple[TacExpr, int, ConstExpr] | None":
    """Match ``Eq(IntSub(X, c), 0)`` / ``Eq(0, IntSub(X, c))``.

    Returns ``(X, c_int, c_const)`` where ``c_const`` is the original
    :class:`ConstExpr` so callers can preserve its lexical form.
    """
    if not (
        isinstance(expr, ApplyExpr)
        and expr.op == "Eq"
        and len(expr.args) == 2
    ):
        return None
    a, b = expr.args
    if const_to_int(a) == 0:
        sub = b
    elif const_to_int(b) == 0:
        sub = a
    else:
        return None
    if not (
        isinstance(sub, ApplyExpr)
        and sub.op == "IntSub"
        and len(sub.args) == 2
        and isinstance(sub.args[1], ConstExpr)
    ):
        return None
    c = const_to_int(sub.args[1])
    if c is None:
        return None
    return sub.args[0], c, sub.args[1]


def _rewrite_and_lift_eq(expr: TacExpr, _ctx: RewriteCtx) -> TacExpr | None:
    if not (
        isinstance(expr, ApplyExpr)
        and expr.op == "LAnd"
        and len(expr.args) == 2
    ):
        return None
    for i, j in ((0, 1), (1, 0)):
        ge = _match_ge_const(expr.args[i])
        eq = _match_int_sub_eq_zero(expr.args[j])
        if ge is None or eq is None:
            continue
        x_ge, c_ge = ge
        x_eq, c_eq, c_const = eq
        if c_ge != c_eq or x_ge != x_eq:
            continue
        return ApplyExpr("Eq", (x_ge, c_const))
    return None


AND_LIFT_EQ_DECREMENT = Rule(
    name="AndLiftEq",
    fn=_rewrite_and_lift_eq,
    description=(
        "LAnd(Ge(X, c), Eq(IntSub(X, c), 0)) -> Eq(X, c). The Eq "
        "already implies Ge(X, c), so the conjunction collapses. "
        "Recovers the singleton-equality shape after the bv decrement "
        "idiom (Add(BV256_MAX, X)) was unfolded by ADD_BV_MAX_TO_ITE."
    ),
)
