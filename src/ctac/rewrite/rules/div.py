"""Div-focused TAC rewrites.

R2 - nested constant ``Div`` fusion.
R3 - common-factor cancellation ``Div(Mul(c, A), c) -> A``.
R1 - bit-field strip ``Mul(Mod(Div(X, 2^k), 2^n), 2^k) -> X`` when
     ``X`` is provably in ``[0, 2^(k+n) - 1]``.
R4 - eliminate ``Div`` from comparisons when the divisor is a positive
     integer constant.
"""

from __future__ import annotations

from ctac.ast.nodes import ApplyExpr, ConstExpr, TacExpr
from ctac.rewrite.context import RewriteCtx
from ctac.rewrite.framework import Rule
from ctac.rewrite.range_infer import infer_expr_range
from ctac.rewrite.rules.common import (
    DIV_OPS,
    MUL_OPS,
    as_int_const,
    const_to_int,
    is_apply_in,
    log2_if_pow2,
    reformat_const,
)

_CMP_OPS = frozenset({"Lt", "Le", "Gt", "Ge", "Eq"})
_CMP_FLIP_OPERANDS = {"Lt": "Gt", "Le": "Ge", "Gt": "Lt", "Ge": "Le", "Eq": "Eq"}


def _matching_mul_op(div_op: str) -> str:
    return "IntMul" if div_op == "IntDiv" else "Mul"


_FACTOR_CONSUMED = object()  # sentinel: extraction reduces expression to 1


def _extract_const_factor(
    expr: TacExpr, factor: int, ctx: RewriteCtx
) -> TacExpr | object | None:
    """Try to peel a positive integer ``factor`` from ``expr``.

    Descends through ``ctx.lookthrough`` (static defs + ``safe_math_narrow``)
    and nested ``Mul``/``IntMul`` nodes. Returns ``None`` if ``factor`` does
    not evenly divide ``expr``, :data:`_FACTOR_CONSUMED` if the whole
    expression *is* the factor, or the reduced expression otherwise.
    """
    e = ctx.lookthrough(expr)
    if isinstance(e, ConstExpr):
        v = const_to_int(e)
        if v is None or v <= 0 or v % factor != 0:
            return None
        q = v // factor
        if q == 1:
            return _FACTOR_CONSUMED
        return reformat_const(e, q)
    if isinstance(e, ApplyExpr) and e.op in MUL_OPS and len(e.args) == 2:
        a, b = e.args
        new_a = _extract_const_factor(a, factor, ctx)
        if new_a is _FACTOR_CONSUMED:
            return b
        if new_a is not None:
            assert isinstance(new_a, (ConstExpr, ApplyExpr)) or hasattr(new_a, "name")
            return ApplyExpr(e.op, (new_a, b))
        new_b = _extract_const_factor(b, factor, ctx)
        if new_b is _FACTOR_CONSUMED:
            return a
        if new_b is not None:
            assert isinstance(new_b, (ConstExpr, ApplyExpr)) or hasattr(new_b, "name")
            return ApplyExpr(e.op, (a, new_b))
    return None


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
    """``Div(X, c)`` -> ``X / c`` when ``c`` is a positive integer constant and
    ``c`` can be peeled from ``X``'s multiplicative structure.

    Generalizes the simple ``Div(Mul(c, A), c) -> A`` case: the factor may be
    buried in nested ``Mul``/``IntMul`` or reachable through static defs and
    ``safe_math_narrow`` wrappers (via :meth:`RewriteCtx.lookthrough`).
    Example: ``Div(Mul(R53, narrow(Mul(c, R13))), c) -> Mul(R53, R13)``.
    """
    if not is_apply_in(expr, DIV_OPS, 2):
        return None
    assert isinstance(expr, ApplyExpr)
    num, den = expr.args
    c = const_to_int(den)
    if c is None or c <= 0:
        return None
    result = _extract_const_factor(num, c, ctx)
    if result is None:
        return None
    if result is _FACTOR_CONSUMED:
        # Numerator was exactly the factor; Div(c, c) = 1.
        return reformat_const(den, 1)
    assert isinstance(result, (ConstExpr, ApplyExpr)) or hasattr(result, "name")
    return result  # type: ignore[return-value]


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


def _rewrite_r4(expr: TacExpr, ctx: RewriteCtx) -> TacExpr | None:
    """Eliminate Div from comparisons with a positive-constant divisor.

    For B > 0 (Euclidean division):
      Lt(Div(A, B), C) -> Lt(A, B*C)
      Le(Div(A, B), C) -> Lt(A, B*(C+1))
      Gt(Div(A, B), C) -> Ge(A, B*(C+1))
      Ge(Div(A, B), C) -> Ge(A, B*C)
      Eq(Div(A, B), C) -> LAnd(Ge(A, B*C), Lt(A, B*(C+1)))

    The rewrite always emits ``IntMul``/``IntAdd`` and tags the divisor /
    ``1`` constants as ``(int)`` so the resulting arithmetic is exact
    (no bv-modular overflow). This is sound because Div on integers and
    Euclidean Div on unsigned bv agree when the value fits.

    When Div is on the right-hand side we first flip the comparison so
    Div ends up on the left, then apply the appropriate form.
    """
    if not (isinstance(expr, ApplyExpr) and expr.op in _CMP_OPS and len(expr.args) == 2):
        return None
    a, b = expr.args
    a_lt = ctx.lookthrough(a)
    b_lt = ctx.lookthrough(b)
    a_is_div = isinstance(a_lt, ApplyExpr) and a_lt.op in DIV_OPS and len(a_lt.args) == 2
    b_is_div = isinstance(b_lt, ApplyExpr) and b_lt.op in DIV_OPS and len(b_lt.args) == 2
    # Fire only when exactly one side is a Div (avoid the both-div / neither case).
    if a_is_div == b_is_div:
        return None

    op = expr.op
    if a_is_div:
        div_expr = a_lt
        other = b
    else:
        div_expr = b_lt
        other = a
        op = _CMP_FLIP_OPERANDS[op]

    assert isinstance(div_expr, ApplyExpr)
    num, den = div_expr.args
    den_val = const_to_int(den)
    if den_val is None or den_val <= 0:
        return None

    assert isinstance(den, ConstExpr)
    den_int = as_int_const(den, den_val)
    one_int = as_int_const(den, 1)

    def scale(x: TacExpr) -> TacExpr:
        return ApplyExpr("IntMul", (den_int, x))

    def plus_one(x: TacExpr) -> TacExpr:
        return ApplyExpr("IntAdd", (x, one_int))

    if op == "Lt":
        return ApplyExpr("Lt", (num, scale(other)))
    if op == "Le":
        return ApplyExpr("Lt", (num, scale(plus_one(other))))
    if op == "Gt":
        return ApplyExpr("Ge", (num, scale(plus_one(other))))
    if op == "Ge":
        return ApplyExpr("Ge", (num, scale(other)))
    if op == "Eq":
        return ApplyExpr(
            "LAnd",
            (
                ApplyExpr("Ge", (num, scale(other))),
                ApplyExpr("Lt", (num, scale(plus_one(other)))),
            ),
        )
    return None


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

R4_DIV_IN_CMP = Rule(
    name="R4",
    fn=_rewrite_r4,
    description="Eliminate Div from comparison: Lt(Div(A, B), C) -> Lt(A, B*C) etc.",
)
