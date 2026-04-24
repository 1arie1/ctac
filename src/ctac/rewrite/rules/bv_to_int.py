"""Lower bv-modular arithmetic to int-arithmetic when provably in-range.

Background
----------

Sea_vc lowers bv256 ``Add`` / ``Sub`` / ``Mul`` as
``(mod (op a b) BV256_MOD)`` to preserve wraparound semantics under
Int logic. When interval inference proves the result already fits in
``[0, 2^256 - 1]`` the ``mod`` is vacuous — the bv-modular op equals
the int op. Rewriting to the ``Int<Op>`` variant moves that decision
up into the rewriter (where sort and range facts live) and lets
sea_vc emit the bare expression.

Rules
-----

- ``MUL_BV_TO_INT``: ``Mul(a, b) -> IntMul(a, b)`` when the inferred
  range of the product is in ``[0, 2^256)``.
- ``ADD_BV_TO_INT``: ``Add(a, b) -> IntAdd(a, b)`` likewise.
- ``ADD_BV_MAX_DEC``: ``Add(BV256_MAX, X) -> IntSub(X, 1)`` when
  ``X >= 1``. The two's-complement "subtract 1 via -1" idiom:
  ``(2^256 - 1) + X = X - 1 (mod 2^256)`` exactly when ``X >= 1``.

``Sub`` is intentionally out of scope — it wraps when ``a < b``,
which simple interval inference rarely disproves, so lifting it
needs a stronger invariant than we have today.
"""

from __future__ import annotations

from ctac.ast.nodes import ApplyExpr, ConstExpr, TacExpr
from ctac.rewrite.context import RewriteCtx
from ctac.rewrite.framework import Rule
from ctac.rewrite.range_infer import infer_expr_range
from ctac.rewrite.rules.common import const_to_int

_BV256_MOD = 1 << 256
_BV256_MAX = _BV256_MOD - 1


def _fits_in_bv256(expr: ApplyExpr, ctx: RewriteCtx) -> bool:
    r = infer_expr_range(expr, ctx)
    if r is None:
        return False
    lo, hi = r
    return lo >= 0 and hi < _BV256_MOD


def _rewrite_mul_bv_to_int(expr: TacExpr, ctx: RewriteCtx) -> TacExpr | None:
    if not isinstance(expr, ApplyExpr) or expr.op != "Mul" or len(expr.args) != 2:
        return None
    if not _fits_in_bv256(expr, ctx):
        return None
    return ApplyExpr("IntMul", expr.args)


def _rewrite_add_bv_to_int(expr: TacExpr, ctx: RewriteCtx) -> TacExpr | None:
    if not isinstance(expr, ApplyExpr) or expr.op != "Add" or len(expr.args) != 2:
        return None
    if not _fits_in_bv256(expr, ctx):
        return None
    return ApplyExpr("IntAdd", expr.args)


def _rewrite_add_bv_max_dec(expr: TacExpr, ctx: RewriteCtx) -> TacExpr | None:
    # `(2^256 - 1) + X` wraps to `X - 1` in bv256 exactly when `X >= 1`.
    # At `X = 0` the wrap doesn't happen and the bv result is BV256_MAX.
    if not isinstance(expr, ApplyExpr) or expr.op != "Add" or len(expr.args) != 2:
        return None
    a, b = expr.args
    a_val = const_to_int(a) if isinstance(a, ConstExpr) else None
    b_val = const_to_int(b) if isinstance(b, ConstExpr) else None
    if a_val == _BV256_MAX:
        other = b
    elif b_val == _BV256_MAX:
        other = a
    else:
        return None
    r = infer_expr_range(other, ctx)
    if r is None or r[0] < 1:
        return None
    return ApplyExpr("IntSub", (other, ConstExpr("0x1")))


MUL_BV_TO_INT = Rule(
    name="MUL_BV_TO_INT",
    fn=_rewrite_mul_bv_to_int,
    description=(
        "Mul(a, b) -> IntMul(a, b) when the range of the product fits in "
        "[0, 2^256). Elides sea_vc's outer `(mod ... BV256_MOD)` wrap."
    ),
)


ADD_BV_TO_INT = Rule(
    name="ADD_BV_TO_INT",
    fn=_rewrite_add_bv_to_int,
    description=(
        "Add(a, b) -> IntAdd(a, b) when the range of the sum fits in "
        "[0, 2^256). Elides sea_vc's outer `(mod ... BV256_MOD)` wrap."
    ),
)


ADD_BV_MAX_DEC = Rule(
    name="ADD_BV_MAX_DEC",
    fn=_rewrite_add_bv_max_dec,
    description=(
        "Add(BV256_MAX, X) -> IntSub(X, 1) when X >= 1. The bv256 "
        "two's-complement '-1' idiom: `(2^256 - 1) + X` wraps to "
        "`X - 1` exactly when X >= 1."
    ),
)
