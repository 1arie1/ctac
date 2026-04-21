"""Bit-field canonicalization rules.

- N1: expand ``BWAnd(X, ((1<<w)-1) << lo)`` (``lo > 0``) into the div-mod-mul
  form that R1 and the generic div rules can then simplify further.
- N2: ``BWAnd(X, 2^w - 1) -> Mod(X, 2^w)`` (the low-mask, ``lo = 0``, case).
- N3: ``BWAnd(X, 2^256 - 2^k) -> Mul(Div(X, 2^k), 2^k)`` (clear-low-k mask).
- N4: ``ShiftRightLogical(X, k_const) -> Div(X, 2^k)``.

Promotes the SMT-emission-time normalizations at ``sea_vc.py:614-648`` to
TAC-level rewrites so R6's ceiling-div matcher can key on canonical
``Mod`` / ``Div`` shapes rather than duplicating the bit-op recognition.
"""

from __future__ import annotations

from ctac.ast.bit_mask import (
    high_mask_clear_low_k,
    low_mask_width,
    shifted_contiguous_mask,
)
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


def _bwand_target_and_mask(expr: TacExpr) -> tuple[TacExpr, ConstExpr, int] | None:
    """Match ``BWAnd(X, const)`` / ``BWAnd(const, X)`` and return ``(X, const_node, value)``."""
    if not is_apply_of(expr, BWAND_OP, 2):
        return None
    assert isinstance(expr, ApplyExpr)
    a, b = expr.args
    mv = const_to_int(b)
    if mv is not None:
        assert isinstance(b, ConstExpr)
        return a, b, mv
    mv = const_to_int(a)
    if mv is not None:
        assert isinstance(a, ConstExpr)
        return b, a, mv
    return None


def _rewrite_n2_low_mask(expr: TacExpr, _ctx: RewriteCtx) -> TacExpr | None:
    """``BWAnd(X, 2^w - 1) -> Mod(X, 2^w)`` for ``w >= 1``."""
    m = _bwand_target_and_mask(expr)
    if m is None:
        return None
    target, mask_expr, mask_val = m
    w = low_mask_width(mask_val)
    if w is None or w == 0:
        # w==0 means mask==0; `BWAnd(X, 0) = 0`, handled separately if desired.
        return None
    modulus = reformat_const(mask_expr, 1 << w)
    return ApplyExpr("Mod", (target, modulus))


def _rewrite_n3_high_mask(expr: TacExpr, _ctx: RewriteCtx) -> TacExpr | None:
    """``BWAnd(X, 2^256 - 2^k) -> Mul(Div(X, 2^k), 2^k)`` for the 256-bit domain."""
    m = _bwand_target_and_mask(expr)
    if m is None:
        return None
    target, mask_expr, mask_val = m
    k = high_mask_clear_low_k(mask_val, width=256)
    if k is None or k == 0:
        return None
    pow_k = reformat_const(mask_expr, 1 << k)
    return ApplyExpr("Mul", (ApplyExpr("Div", (target, pow_k)), pow_k))


def _rewrite_n4_shr_const(expr: TacExpr, _ctx: RewriteCtx) -> TacExpr | None:
    """``ShiftRightLogical(X, k) -> Div(X, 2^k)`` for constant positive ``k``."""
    if not (isinstance(expr, ApplyExpr) and expr.op == "ShiftRightLogical" and len(expr.args) == 2):
        return None
    target, shift_expr = expr.args
    k = const_to_int(shift_expr)
    if k is None or k <= 0:
        return None
    assert isinstance(shift_expr, ConstExpr)
    pow_k = reformat_const(shift_expr, 1 << k)
    return ApplyExpr("Div", (target, pow_k))


N2_LOW_MASK = Rule(
    name="N2",
    fn=_rewrite_n2_low_mask,
    description="BWAnd(X, 2^w - 1) -> Mod(X, 2^w).",
)

N3_HIGH_MASK = Rule(
    name="N3",
    fn=_rewrite_n3_high_mask,
    description="BWAnd(X, 2^256 - 2^k) -> Mul(Div(X, 2^k), 2^k).",
)

N4_SHR_CONST = Rule(
    name="N4",
    fn=_rewrite_n4_shr_const,
    description="ShiftRightLogical(X, k_const) -> Div(X, 2^k).",
)
