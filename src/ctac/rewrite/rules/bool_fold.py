"""Boolean constant folding for ``LNot`` / ``LAnd`` / ``LOr`` / ``Eq`` /
``Ite`` over Bool ``ConstExpr`` operands.

Registered in ``simplify_pipeline`` (so ``ctac rw`` collapses any
``Ite(true, X, _) -> X`` / ``Ite(false, _, Y) -> Y`` and the
sibling Bool-combinator folds it sees) and reused by ``ctac pin``'s
cleanup pass after ``--bind`` substitution replaces ``SymbolRef``
booleans with constants.

Soundness: every reduction is a Boolean tautology over the constants
``true`` and ``false``. ``Eq`` over two ``ConstExpr`` operands of any
kind reduces to ``true`` / ``false`` only when both have identical
serialized values; we don't attempt cross-kind equality reasoning
(e.g. ``Eq(0, false)`` stays put).

The rewrite engine handles recursion and fixpoint; this rule only
matches at the top of the inspected expression.
"""

from __future__ import annotations

from ctac.ast.nodes import ApplyExpr, ConstExpr, TacExpr
from ctac.rewrite.context import RewriteCtx
from ctac.rewrite.framework import Rule
from ctac.rewrite.rules.common import const_to_int


def _is_bool_const(e: TacExpr) -> bool:
    return isinstance(e, ConstExpr) and e.value in ("true", "false")


def _bool_value(e: ConstExpr) -> bool:
    return e.value == "true"


_TRUE = ConstExpr("true")
_FALSE = ConstExpr("false")


def _rewrite_bool_const_fold(expr: TacExpr, ctx: RewriteCtx) -> TacExpr | None:
    if not isinstance(expr, ApplyExpr):
        return None
    op, args = expr.op, expr.args

    if op == "LNot":
        if len(args) != 1 or not _is_bool_const(args[0]):
            return None
        return _FALSE if _bool_value(args[0]) else _TRUE  # type: ignore[arg-type]

    if op == "LAnd":
        # If any constant operand is false, the whole conjunction is false.
        if any(_is_bool_const(a) and not _bool_value(a) for a in args):  # type: ignore[arg-type]
            return _FALSE
        # Drop true constants; if all dropped, result is true.
        survivors = tuple(a for a in args if not (_is_bool_const(a) and _bool_value(a)))  # type: ignore[arg-type]
        if not survivors:
            return _TRUE
        if len(survivors) == 1:
            return survivors[0]
        if len(survivors) < len(args):
            return ApplyExpr("LAnd", survivors)
        return None

    if op == "LOr":
        # If any constant operand is true, the whole disjunction is true.
        if any(_is_bool_const(a) and _bool_value(a) for a in args):  # type: ignore[arg-type]
            return _TRUE
        # Drop false constants; if all dropped, result is false.
        survivors = tuple(
            a for a in args if not (_is_bool_const(a) and not _bool_value(a))  # type: ignore[arg-type]
        )
        if not survivors:
            return _FALSE
        if len(survivors) == 1:
            return survivors[0]
        if len(survivors) < len(args):
            return ApplyExpr("LOr", survivors)
        return None

    if op == "Eq":
        if (
            len(args) == 2
            and _is_bool_const(args[0])
            and _is_bool_const(args[1])
        ):
            same = _bool_value(args[0]) == _bool_value(args[1])  # type: ignore[arg-type]
            return _TRUE if same else _FALSE
        return None

    if op == "Ite":
        # Ite(true, X, _) -> X ; Ite(false, _, Y) -> Y
        if len(args) == 3 and _is_bool_const(args[0]):
            return args[1] if _bool_value(args[0]) else args[2]  # type: ignore[arg-type]
        return None

    return None


BOOL_CONST_FOLD = Rule(
    name="BOOL_FOLD",
    fn=_rewrite_bool_const_fold,
    description=(
        "Constant-fold Boolean operators: LNot/LAnd/LOr/Eq/Ite when "
        "Bool ConstExpr operands determine the result. Used by pin's "
        "cleanup pass after --bind substitution."
    ),
)


# XOR_BOOL_INT_EQ: the SBF carry-consistency check XORs two 0/1-int
# encoded booleans and tests the result against 0 or 1::
#
#     R = BWXOr(Ite(p, 1, 0), Ite(q, 1, 0));  assume R == 0
#
# Over {0, 1} the XOR is 0 iff the booleans agree, so the test is
# boolean equality: Eq(BWXOr(..), 0) <=> Eq(p, q) and
# Eq(BWXOr(..), 1) <=> LNot(Eq(p, q)). Removes the BWXOr from the
# live cone -- and with it the bv256_xor UF axiom instance the
# encoder would otherwise emit.


def _match_int_bool(e: TacExpr) -> TacExpr | None:
    """``Ite(c, 1, 0)``; returns ``c``."""
    if not (isinstance(e, ApplyExpr) and e.op == "Ite" and len(e.args) == 3):
        return None
    c, t, f = e.args
    if const_to_int(t) == 1 and const_to_int(f) == 0:
        return c
    return None


def _rewrite_xor_bool_int_eq(
    expr: TacExpr, ctx: RewriteCtx
) -> TacExpr | None:
    if not (
        isinstance(expr, ApplyExpr)
        and expr.op == "Eq"
        and len(expr.args) == 2
    ):
        return None
    a, b = expr.args
    k = const_to_int(b)
    xor = a
    if k is None:
        k = const_to_int(a)
        xor = b
    if k not in (0, 1):
        return None
    xor_in = ctx.lookthrough(xor)
    if not (
        isinstance(xor_in, ApplyExpr)
        and xor_in.op == "BWXOr"
        and len(xor_in.args) == 2
    ):
        return None
    p = _match_int_bool(ctx.lookthrough(xor_in.args[0]))
    q = _match_int_bool(ctx.lookthrough(xor_in.args[1]))
    if p is None or q is None:
        return None
    iff = ApplyExpr("Eq", (p, q))
    if k == 0:
        return iff
    return ApplyExpr("LNot", (iff,))


XOR_BOOL_INT_EQ = Rule(
    name="XorBoolIntEq",
    fn=_rewrite_xor_bool_int_eq,
    description=(
        "Eq(BWXOr(Ite(p, 1, 0), Ite(q, 1, 0)), 0) -> Eq(p, q) (and "
        "the == 1 dual to LNot). The 0/1-int XOR carry-consistency "
        "check is boolean equality; drops the bv256_xor UF axiom."
    ),
)
