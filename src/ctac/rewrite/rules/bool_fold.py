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
