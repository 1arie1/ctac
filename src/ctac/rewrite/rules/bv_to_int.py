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

``Sub`` is intentionally out of scope — it wraps when ``a < b``,
which simple interval inference rarely disproves, so lifting it
needs a stronger invariant than we have today.
"""

from __future__ import annotations

from ctac.ast.nodes import ApplyExpr, TacExpr
from ctac.rewrite.context import RewriteCtx
from ctac.rewrite.framework import Rule
from ctac.rewrite.range_infer import infer_expr_range

_BV256_MOD = 1 << 256


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
