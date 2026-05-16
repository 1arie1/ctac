"""SAR_TO_SHR_NONNEG: rewrite ``ShiftRightArithmetical(x, k)`` to
``ShiftRightLogical(x, k)`` when range analysis proves ``x``'s top
bit is zero.

For bv256 values, arithmetic right shift differs from logical right
shift only when the operand's top bit (bit 255) is set — the SAR
fills the high ``k`` bits with the sign bit, while LSHR fills with
zeros. When ``infer_expr_range(x)`` returns ``(lo, hi)`` with
``hi < 2^255``, the top bit is provably zero, so SAR and LSHR
produce the same result.

This is the typical shape after ``R = Mod(_, 2^64)`` (clamp to 64
bits, way below ``2^255``) — the sea encoder doesn't natively lower
SAR; this rule lets the logical-shift path (``int.bv256_lshr``,
constant-folded to division by ``2^k``) handle it instead.
"""

from __future__ import annotations

from ctac.ast.nodes import ApplyExpr, TacExpr
from ctac.rewrite.context import RewriteCtx
from ctac.rewrite.framework import Rule
from ctac.rewrite.range_infer import infer_expr_range


_BV256_HALF = 1 << 255  # top bit threshold


def _rewrite_sar_to_shr_nonneg(
    expr: TacExpr, ctx: RewriteCtx
) -> TacExpr | None:
    if not (
        isinstance(expr, ApplyExpr)
        and expr.op == "ShiftRightArithmetical"
        and len(expr.args) == 2
    ):
        return None
    x, _k = expr.args
    rng = infer_expr_range(x, ctx)
    if rng is None:
        return None
    lo, hi = rng
    if lo < 0 or hi >= _BV256_HALF:
        return None
    return ApplyExpr("ShiftRightLogical", expr.args)


SAR_TO_SHR_NONNEG = Rule(
    name="SarToShrNonneg",
    fn=_rewrite_sar_to_shr_nonneg,
    description=(
        "ShiftRightArithmetical(x, k) -> ShiftRightLogical(x, k) "
        "when infer_expr_range(x) proves x < 2^255 (top bit zero). "
        "The two shifts agree on every non-negative bv256 value; "
        "elides the SAR operator the sea encoder doesn't lower."
    ),
)
