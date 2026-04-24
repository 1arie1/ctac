"""Ite / boolean rewrite rules.

These collaborate to collapse patterns like::

    R98 = Ite(c1, Ite(c2, Ite(c3, Ite(c4, 0x0, 0x1), 0x1), 0x1), 0x1)
    assume Eq(R98, 0x1)

into a disjunction of the branch conditions. The trick is to distribute the
outer ``Eq`` into the ``Ite`` branches, fold ``Eq(const, const)`` to bool
literals, and collapse Ites whose branches are ``true``/``false``.

Individual rules are tiny and generally useful beyond this one pattern:
the driver's fixed-point loop composes them.
"""

from __future__ import annotations

from ctac.ast.nodes import ApplyExpr, ConstExpr, TacExpr
from ctac.rewrite.context import RewriteCtx
from ctac.rewrite.framework import Rule
from ctac.rewrite.range_infer import infer_expr_range
from ctac.rewrite.rules.common import const_to_int

_TRUE = ConstExpr("true")
_FALSE = ConstExpr("false")


def _is_true(e: TacExpr) -> bool:
    return isinstance(e, ConstExpr) and e.value.strip() == "true"


def _is_false(e: TacExpr) -> bool:
    return isinstance(e, ConstExpr) and e.value.strip() == "false"


def _is_ite(e: TacExpr) -> bool:
    return isinstance(e, ApplyExpr) and e.op == "Ite" and len(e.args) == 3


def _rewrite_eq_const_fold(expr: TacExpr, _ctx: RewriteCtx) -> TacExpr | None:
    """``Eq(const, const)`` folds to ``true`` / ``false``."""
    if not (isinstance(expr, ApplyExpr) and expr.op == "Eq" and len(expr.args) == 2):
        return None
    a, b = expr.args
    if not (isinstance(a, ConstExpr) and isinstance(b, ConstExpr)):
        return None
    # Bool literal comparisons.
    a_true, a_false = _is_true(a), _is_false(a)
    b_true, b_false = _is_true(b), _is_false(b)
    if (a_true or a_false) and (b_true or b_false):
        return _TRUE if (a_true == b_true) else _FALSE
    va = const_to_int(a)
    vb = const_to_int(b)
    if va is None or vb is None:
        return None
    return _TRUE if va == vb else _FALSE


def _rewrite_eq_ite_distribute(expr: TacExpr, ctx: RewriteCtx) -> TacExpr | None:
    """``Eq(Ite(c, T, E), V)`` -> ``Ite(c, Eq(T, V), Eq(E, V))`` (and symmetric)."""
    if not (isinstance(expr, ApplyExpr) and expr.op == "Eq" and len(expr.args) == 2):
        return None
    a, b = expr.args
    a_lt = ctx.lookthrough(a)
    if _is_ite(a_lt):
        assert isinstance(a_lt, ApplyExpr)
        cond, then, els = a_lt.args
        return ApplyExpr(
            "Ite",
            (cond, ApplyExpr("Eq", (then, b)), ApplyExpr("Eq", (els, b))),
        )
    b_lt = ctx.lookthrough(b)
    if _is_ite(b_lt):
        assert isinstance(b_lt, ApplyExpr)
        cond, then, els = b_lt.args
        return ApplyExpr(
            "Ite",
            (cond, ApplyExpr("Eq", (a, then)), ApplyExpr("Eq", (a, els))),
        )
    return None


_ADD_OPS = frozenset({"Add", "IntAdd"})
_SUB_OPS = frozenset({"Sub", "IntSub"})


def _rewrite_add_ite_distribute(expr: TacExpr, ctx: RewriteCtx) -> TacExpr | None:
    """``Add(Ite(c, T, E), Y)`` -> ``Ite(c, Add(T, Y), Add(E, Y))`` (and symmetric).

    Applies to both ``Add`` and ``IntAdd``, and peels
    ``safe_math_narrow_bvN`` wrappers so e.g. ``narrow(IntAdd(X,
    Ite(c, T, E)))`` also distributes. Distribution is sound in int,
    bv, and mixed semantics — the Ite selects an operand and the outer
    op commutes with branch selection.
    """
    if not (isinstance(expr, ApplyExpr) and expr.op in _ADD_OPS and len(expr.args) == 2):
        return None
    op = expr.op
    a, b = expr.args
    a_lt = ctx.peel_narrow(a)
    if _is_ite(a_lt):
        assert isinstance(a_lt, ApplyExpr)
        cond, then, els = a_lt.args
        return ApplyExpr(
            "Ite",
            (cond, ApplyExpr(op, (then, b)), ApplyExpr(op, (els, b))),
        )
    b_lt = ctx.peel_narrow(b)
    if _is_ite(b_lt):
        assert isinstance(b_lt, ApplyExpr)
        cond, then, els = b_lt.args
        return ApplyExpr(
            "Ite",
            (cond, ApplyExpr(op, (a, then)), ApplyExpr(op, (a, els))),
        )
    return None


def _rewrite_sub_ite_distribute_left(expr: TacExpr, ctx: RewriteCtx) -> TacExpr | None:
    """``Sub(Ite(c, T, E), Y)`` -> ``Ite(c, Sub(T, Y), Sub(E, Y))``.

    Applies to both ``Sub`` and ``IntSub``; peels narrows on the LHS.
    Sub is non-commutative, so LHS and RHS Ite are separate rules.
    """
    if not (isinstance(expr, ApplyExpr) and expr.op in _SUB_OPS and len(expr.args) == 2):
        return None
    op = expr.op
    a, b = expr.args
    a_lt = ctx.peel_narrow(a)
    if not _is_ite(a_lt):
        return None
    assert isinstance(a_lt, ApplyExpr)
    cond, then, els = a_lt.args
    return ApplyExpr(
        "Ite",
        (cond, ApplyExpr(op, (then, b)), ApplyExpr(op, (els, b))),
    )


def _rewrite_sub_ite_distribute_right(expr: TacExpr, ctx: RewriteCtx) -> TacExpr | None:
    """``Sub(X, Ite(c, T, E))`` -> ``Ite(c, Sub(X, T), Sub(X, E))``."""
    if not (isinstance(expr, ApplyExpr) and expr.op in _SUB_OPS and len(expr.args) == 2):
        return None
    op = expr.op
    a, b = expr.args
    b_lt = ctx.peel_narrow(b)
    if not _is_ite(b_lt):
        return None
    assert isinstance(b_lt, ApplyExpr)
    cond, then, els = b_lt.args
    return ApplyExpr(
        "Ite",
        (cond, ApplyExpr(op, (a, then)), ApplyExpr(op, (a, els))),
    )


def _rewrite_ite_same(expr: TacExpr, _ctx: RewriteCtx) -> TacExpr | None:
    """``Ite(c, X, X)`` -> ``X``."""
    if not _is_ite(expr):
        return None
    assert isinstance(expr, ApplyExpr)
    _cond, then, els = expr.args
    if then == els:
        return then
    return None


def _rewrite_ite_bool(expr: TacExpr, _ctx: RewriteCtx) -> TacExpr | None:
    """Collapse Ite whose branches include a ``true`` / ``false`` literal."""
    if not _is_ite(expr):
        return None
    assert isinstance(expr, ApplyExpr)
    cond, then, els = expr.args
    if _is_true(then) and _is_false(els):
        return cond
    if _is_false(then) and _is_true(els):
        return ApplyExpr("LNot", (cond,))
    if _is_true(then):
        return ApplyExpr("LOr", (cond, els))
    if _is_false(then):
        return ApplyExpr("LAnd", (ApplyExpr("LNot", (cond,)), els))
    if _is_true(els):
        return ApplyExpr("LOr", (ApplyExpr("LNot", (cond,)), then))
    if _is_false(els):
        return ApplyExpr("LAnd", (cond, then))
    return None


_CMP_OPS = frozenset({"Ge", "Gt", "Le", "Lt", "Eq", "Ne"})


def _eval_cmp_from_range(
    cond: TacExpr, ctx: RewriteCtx
) -> bool | None:
    """Return True/False if ``cond`` is a comparison that range-inference
    decides unambiguously; None otherwise.

    Handles only binary comparisons whose operands both have an inferred
    range. No effort is made to reason about boolean combinations — those
    collapse via the driver's bottom-up traversal once the inner
    comparisons fold.
    """
    if not isinstance(cond, ApplyExpr) or cond.op not in _CMP_OPS or len(cond.args) != 2:
        return None
    a_r = infer_expr_range(cond.args[0], ctx)
    b_r = infer_expr_range(cond.args[1], ctx)
    if a_r is None or b_r is None:
        return None
    a_lo, a_hi = a_r
    b_lo, b_hi = b_r
    op = cond.op
    if op == "Ge":
        if a_lo >= b_hi:
            return True
        if a_hi < b_lo:
            return False
    elif op == "Gt":
        if a_lo > b_hi:
            return True
        if a_hi <= b_lo:
            return False
    elif op == "Le":
        if a_hi <= b_lo:
            return True
        if a_lo > b_hi:
            return False
    elif op == "Lt":
        if a_hi < b_lo:
            return True
        if a_lo >= b_hi:
            return False
    elif op == "Eq":
        if a_lo == a_hi == b_lo == b_hi:
            return True
        if a_hi < b_lo or b_hi < a_lo:
            return False
    elif op == "Ne":
        if a_hi < b_lo or b_hi < a_lo:
            return True
        if a_lo == a_hi == b_lo == b_hi:
            return False
    return None


def _rewrite_ite_cond_fold(expr: TacExpr, ctx: RewriteCtx) -> TacExpr | None:
    """``Ite(cond, then, else)`` -> ``then`` if range analysis proves ``cond``
    is always true, ``else`` if always false."""
    if not _is_ite(expr):
        return None
    assert isinstance(expr, ApplyExpr)
    cond, then, els = expr.args
    truth = _eval_cmp_from_range(cond, ctx)
    if truth is True:
        return then
    if truth is False:
        return els
    return None


_LNOT_CMP_FLIP = {"Lt": "Ge", "Le": "Gt", "Gt": "Le", "Ge": "Lt"}


def _rewrite_bool_absorb(expr: TacExpr, _ctx: RewriteCtx) -> TacExpr | None:
    """``LOr``/``LAnd``/``LNot`` simplifications with ``true``/``false`` and negated comparisons."""
    if not isinstance(expr, ApplyExpr):
        return None
    if expr.op == "LOr" and len(expr.args) == 2:
        a, b = expr.args
        if _is_true(a) or _is_true(b):
            return _TRUE
        if _is_false(a):
            return b
        if _is_false(b):
            return a
    elif expr.op == "LAnd" and len(expr.args) == 2:
        a, b = expr.args
        if _is_false(a) or _is_false(b):
            return _FALSE
        if _is_true(a):
            return b
        if _is_true(b):
            return a
    elif expr.op == "LNot" and len(expr.args) == 1:
        inner = expr.args[0]
        if _is_true(inner):
            return _FALSE
        if _is_false(inner):
            return _TRUE
        if isinstance(inner, ApplyExpr) and inner.op == "LNot" and len(inner.args) == 1:
            return inner.args[0]
        if (
            isinstance(inner, ApplyExpr)
            and inner.op in _LNOT_CMP_FLIP
            and len(inner.args) == 2
        ):
            return ApplyExpr(_LNOT_CMP_FLIP[inner.op], inner.args)
    return None


def _rewrite_demorgan(expr: TacExpr, _ctx: RewriteCtx) -> TacExpr | None:
    """De Morgan: ``LOr(!A, !B) -> !LAnd(A, B)``; ``LAnd(!A, !B) -> !LOr(A, B)``.

    Applied bottom-up, turns right-associated chains like
    ``LOr(!a, LOr(!b, LOr(!c, !d)))`` into ``!LAnd(a, LAnd(b, LAnd(c, d)))``.
    """
    if not isinstance(expr, ApplyExpr) or len(expr.args) != 2:
        return None
    if expr.op not in {"LOr", "LAnd"}:
        return None
    a, b = expr.args
    if not (
        isinstance(a, ApplyExpr) and a.op == "LNot" and len(a.args) == 1
        and isinstance(b, ApplyExpr) and b.op == "LNot" and len(b.args) == 1
    ):
        return None
    dual = "LAnd" if expr.op == "LOr" else "LOr"
    return ApplyExpr("LNot", (ApplyExpr(dual, (a.args[0], b.args[0])),))


EQ_CONST_FOLD = Rule(
    name="EqFold",
    fn=_rewrite_eq_const_fold,
    description="Eq(const, const) -> true|false.",
)
EQ_ITE_DIST = Rule(
    name="EqIte",
    fn=_rewrite_eq_ite_distribute,
    description="Eq(Ite(c, T, E), V) -> Ite(c, Eq(T, V), Eq(E, V)).",
)
ADD_ITE_DIST = Rule(
    name="AddIte",
    fn=_rewrite_add_ite_distribute,
    description="Add(Ite(c, T, E), Y) -> Ite(c, Add(T, Y), Add(E, Y)) (and symmetric).",
)
SUB_ITE_DIST_LEFT = Rule(
    name="SubIteLeft",
    fn=_rewrite_sub_ite_distribute_left,
    description="Sub(Ite(c, T, E), Y) -> Ite(c, Sub(T, Y), Sub(E, Y)).",
)
SUB_ITE_DIST_RIGHT = Rule(
    name="SubIteRight",
    fn=_rewrite_sub_ite_distribute_right,
    description="Sub(X, Ite(c, T, E)) -> Ite(c, Sub(X, T), Sub(X, E)).",
)
ITE_SAME = Rule(
    name="IteSame",
    fn=_rewrite_ite_same,
    description="Ite(c, X, X) -> X.",
)
ITE_BOOL = Rule(
    name="IteBool",
    fn=_rewrite_ite_bool,
    description="Collapse Ite with true/false literal branches into bool ops.",
)
ITE_COND_FOLD = Rule(
    name="IteCondFold",
    fn=_rewrite_ite_cond_fold,
    description=(
        "Ite(cond, T, E) -> T when range-inference proves cond is always "
        "true; -> E when always false. Uses infer_expr_range on both sides "
        "of a binary comparison."
    ),
)
BOOL_ABSORB = Rule(
    name="BoolAbsorb",
    fn=_rewrite_bool_absorb,
    description="LOr/LAnd absorb true/false; LNot of true/false/LNot collapses.",
)
DE_MORGAN = Rule(
    name="DeMorgan",
    fn=_rewrite_demorgan,
    description="LOr(!A, !B) -> !LAnd(A, B); dual for LAnd(!A, !B).",
)
