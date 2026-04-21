"""Div-focused TAC rewrites.

R2 - nested constant ``Div`` fusion.
R3 - common-factor cancellation ``Div(Mul(c, A), c) -> A``.
R1 - bit-field strip ``Mul(Mod(Div(X, 2^k), 2^n), 2^k) -> X`` when
     ``X`` is provably in ``[0, 2^(k+n) - 1]``.
"""

from __future__ import annotations

from ctac.ast.nodes import ApplyExpr, ConstExpr, TacExpr
from ctac.rewrite.context import RewriteCtx
from ctac.rewrite.framework import Rule
from ctac.rewrite.range_infer import infer_expr_range
from ctac.rewrite.rules.common import (
    DIV_OPS,
    MUL_OPS,
    const_to_int,
    is_apply_in,
    log2_if_pow2,
    reformat_const,
)


def _matching_mul_op(div_op: str) -> str:
    return "IntMul" if div_op == "IntDiv" else "Mul"


def _rewrite_r2(expr: TacExpr, ctx: RewriteCtx) -> TacExpr | None:
    """``Div(Div(A, c1), c2) -> Div(A, c1*c2)`` for ``c1, c2 > 0``."""
    if not is_apply_in(expr, DIV_OPS, 2):
        return None
    assert isinstance(expr, ApplyExpr)
    outer_num, outer_den = expr.args
    c2 = const_to_int(outer_den)
    if c2 is None or c2 <= 0:
        return None
    inner = ctx.lookthrough(outer_num)
    if not is_apply_in(inner, DIV_OPS, 2):
        return None
    assert isinstance(inner, ApplyExpr)
    if inner.op != expr.op:
        return None
    a, inner_den = inner.args
    c1 = const_to_int(inner_den)
    if c1 is None or c1 <= 0:
        return None
    assert isinstance(outer_den, ConstExpr)
    return ApplyExpr(expr.op, (a, reformat_const(outer_den, c1 * c2)))


def _rewrite_r3(expr: TacExpr, ctx: RewriteCtx) -> TacExpr | None:
    """``Div(Mul(c, A), c) -> A`` and ``Div(Mul(A, c), c) -> A`` for ``c > 0``."""
    if not is_apply_in(expr, DIV_OPS, 2):
        return None
    assert isinstance(expr, ApplyExpr)
    num, den = expr.args
    c_den = const_to_int(den)
    if c_den is None or c_den <= 0:
        return None
    num_expanded = ctx.lookthrough(num)
    if not is_apply_in(num_expanded, MUL_OPS, 2):
        return None
    assert isinstance(num_expanded, ApplyExpr)
    if num_expanded.op != _matching_mul_op(expr.op):
        return None
    a, b = num_expanded.args
    c_a = const_to_int(a)
    c_b = const_to_int(b)
    if c_a is not None and c_a == c_den and c_a > 0:
        return b
    if c_b is not None and c_b == c_den and c_b > 0:
        return a
    return None


def _match_div_pow2(expr: TacExpr, ctx: RewriteCtx) -> tuple[TacExpr, int] | None:
    inner = ctx.lookthrough(expr)
    if not is_apply_in(inner, DIV_OPS, 2):
        return None
    assert isinstance(inner, ApplyExpr)
    x, c_e = inner.args
    c = const_to_int(c_e)
    if c is None:
        return None
    k = log2_if_pow2(c)
    if k is None:
        return None
    return x, k


def _match_mod_pow2(expr: TacExpr, ctx: RewriteCtx) -> tuple[TacExpr, int] | None:
    inner = ctx.lookthrough(expr)
    if not isinstance(inner, ApplyExpr) or inner.op != "Mod" or len(inner.args) != 2:
        return None
    inner_arg, c_e = inner.args
    c = const_to_int(c_e)
    if c is None:
        return None
    n = log2_if_pow2(c)
    if n is None:
        return None
    return inner_arg, n


def _rewrite_r1(expr: TacExpr, ctx: RewriteCtx) -> TacExpr | None:
    """``Mul(Mod(Div(X, 2^k), 2^n), 2^k) -> X`` when ``X`` is in ``[0, 2^(k+n) - 1]``."""
    if not isinstance(expr, ApplyExpr) or expr.op != "Mul" or len(expr.args) != 2:
        return None
    a, b = expr.args
    mul_c = const_to_int(b)
    mod_arg: TacExpr = a
    if mul_c is None:
        mul_c = const_to_int(a)
        mod_arg = b
    if mul_c is None:
        return None
    k2 = log2_if_pow2(mul_c)
    if k2 is None or k2 == 0:
        return None
    mod_match = _match_mod_pow2(mod_arg, ctx)
    if mod_match is None:
        return None
    div_arg, n = mod_match
    if n == 0:
        return None
    div_match = _match_div_pow2(div_arg, ctx)
    if div_match is None:
        return None
    x_expr, k1 = div_match
    if k1 != k2:
        return None
    bound = 1 << (k1 + n)
    r = infer_expr_range(x_expr, ctx)
    if r is None:
        return None
    lo, hi = r
    if lo < 0 or hi >= bound:
        return None
    return x_expr


R2_DIV_FUSE = Rule(
    name="R2",
    fn=_rewrite_r2,
    description="Nested constant Div fusion: Div(Div(A, c1), c2) -> Div(A, c1*c2).",
)

R3_DIV_MUL_CANCEL = Rule(
    name="R3",
    fn=_rewrite_r3,
    description="Common-factor cancellation: Div(Mul(c, A), c) -> A.",
)

R1_BITFIELD_STRIP = Rule(
    name="R1",
    fn=_rewrite_r1,
    description="Bit-field strip: Mul(Mod(Div(X, 2^k), 2^n), 2^k) -> X when X fits.",
)
