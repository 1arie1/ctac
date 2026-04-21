"""Bit-field canonicalization rules.

N1: expand ``BWAnd(X, ((1<<w)-1) << lo)`` into the div-mod-mul form that
R1 and the generic div rules can then simplify further.
"""

from __future__ import annotations

from ctac.ast.bit_mask import shifted_contiguous_mask
from ctac.ast.nodes import ApplyExpr, ConstExpr, TacExpr
from ctac.rewrite.context import RewriteCtx
from ctac.rewrite.framework import Rule
from ctac.rewrite.rules.common import BWAND_OP, const_to_int, is_apply_of, reformat_const


def _rewrite_n1(expr: TacExpr, _ctx: RewriteCtx) -> TacExpr | None:
    """``BWAnd(X, mask)`` with ``mask = ((1<<w)-1) << lo`` and ``lo > 0``."""
    if not is_apply_of(expr, BWAND_OP, 2):
        return None
    assert isinstance(expr, ApplyExpr)
    a, b = expr.args
    mask_val = const_to_int(b)
    if mask_val is not None:
        target, mask_expr = a, b
    else:
        mask_val = const_to_int(a)
        if mask_val is None:
            return None
        target, mask_expr = b, a
    decoded = shifted_contiguous_mask(mask_val)
    if decoded is None:
        return None
    lo, w = decoded
    if lo == 0:
        # Unshifted low-mask `BWAnd(X, 2^w - 1)` is `Mod(X, 2^w)` but keeping the
        # BWAnd form avoids turning low-byte masks into div/mod/mul; skip for MVP.
        return None
    assert isinstance(mask_expr, ConstExpr)
    two_lo = 1 << lo
    two_w = 1 << w
    two_lo_const = reformat_const(mask_expr, two_lo)
    two_w_const = reformat_const(mask_expr, two_w)
    div_expr = ApplyExpr("Div", (target, two_lo_const))
    mod_expr = ApplyExpr("Mod", (div_expr, two_w_const))
    return ApplyExpr("Mul", (mod_expr, two_lo_const))


N1_SHIFTED_BWAND = Rule(
    name="N1",
    fn=_rewrite_n1,
    description="Expand shifted-contiguous BWAnd into Mul(Mod(Div(X, 2^lo), 2^w), 2^lo).",
)
