"""SIGN_EXTEND_UNWRAP: fold ``unwrap_twos_complement_256(SignExtend(b, x))``
to an Int-domain ``Ite`` over linear arms.

Pattern
-------

Sea encoder doesn't natively lower TAC's ``SignExtend`` operator
(EVM/SBF convention: byte index ``b`` selects the sign bit at position
``8*(b+1)-1``). In practice the operator only ever appears wrapped by
``unwrap_twos_complement_256:bif`` and typically preceded by a
``Mod(_, 2^w)`` reduction, e.g.::

    R = Mod(X, 2^64)
    I = IntMul(-1, unwrap_twos_complement_256(SignExtend(7, R)))

The semantics of ``unwrap_twos_complement_256(SignExtend(b, x))``,
with ``w = 8*(b+1)``, ``low = x mod 2^w``::

    Ite(Lt(low, 2^(w-1)), low, low - 2^w)

— the standard "interpret the low ``w`` bits as a signed two's-complement
integer" form. Linear in both arms; LIA-friendly.

Range-tightened form
--------------------

When :func:`infer_expr_range` proves ``0 <= x < 2^w`` (the common case
when ``x`` is the result of ``Mod(_, 2^w)``), the inner ``Mod`` is
vacuous and we emit::

    Ite(Lt(x, 2^(w-1)), x, IntSub(x, 2^w))

Otherwise the rule still fires but with an explicit ``Mod`` around
``x``.

Conditions
----------

1. Host shape is ``Apply(unwrap_twos_complement_256:bif, inner)`` where
   ``inner`` is ``SignExtend(b, x)`` with ``b`` a ``ConstExpr`` in
   ``[0, 31]`` (EVM/SBF byte indices).
2. No range gate is required for correctness — the unconditional
   ``Mod`` form is sound; the range check is purely an optimization.

Effect
------

Replaces the host expression with the ``Ite`` form. Downstream
``ITE_COND_FOLD`` / ``RANGE_FOLD`` collapse the Ite when range
analysis pins the condition (e.g., ``x < 2^(w-1)`` known).
"""

from __future__ import annotations

from ctac.analysis.symbols import canonical_symbol
from ctac.ast.nodes import ApplyExpr, ConstExpr, SymbolRef, TacExpr
from ctac.rewrite.context import RewriteCtx
from ctac.rewrite.framework import Rule
from ctac.rewrite.range_infer import infer_expr_range
from ctac.rewrite.rules.common import const_to_int


_UNWRAP_NAME = "unwrap_twos_complement_256:bif"
# EVM/SBF byte indices: ``b ∈ [0, 30]`` cover 8..248-bit sign positions.
# ``b == 31`` would be a no-op against bv256; we still handle it
# uniformly via the same Ite form for completeness.
_MAX_BYTE_INDEX = 31


def _match_unwrap_signextend(
    expr: TacExpr,
) -> tuple[int, TacExpr] | None:
    if not (isinstance(expr, ApplyExpr) and expr.op == "Apply"):
        return None
    if len(expr.args) != 2:
        return None
    callee, inner = expr.args
    if not (isinstance(callee, SymbolRef) and callee.name == _UNWRAP_NAME):
        return None
    if not (
        isinstance(inner, ApplyExpr)
        and inner.op == "SignExtend"
        and len(inner.args) == 2
    ):
        return None
    b_expr, x = inner.args
    b = const_to_int(b_expr)
    if b is None or b < 0 or b > _MAX_BYTE_INDEX:
        return None
    return b, x


def _rewrite_sign_extend_unwrap(
    expr: TacExpr, ctx: RewriteCtx
) -> TacExpr | None:
    match = _match_unwrap_signextend(expr)
    if match is None:
        return None
    b, x = match
    width = 8 * (b + 1)
    two_w = 1 << width
    two_w_minus_1 = 1 << (width - 1)

    # Pick ``low`` either as ``x`` (when range proves it's already
    # masked) or as ``Mod(x, 2^w)`` (general form).
    rng = infer_expr_range(x, ctx)
    low: TacExpr
    if rng is not None and rng[0] >= 0 and rng[1] < two_w:
        low = x
    else:
        low = ApplyExpr("Mod", (x, ConstExpr(f"0x{two_w:x}")))

    # Ite(Lt(low, 2^(w-1)), low, IntSub(low, 2^w)).
    cond = ApplyExpr("Lt", (low, ConstExpr(f"0x{two_w_minus_1:x}")))
    neg_arm = ApplyExpr(
        "IntSub", (low, ConstExpr(f"0x{two_w:x}(int)"))
    )
    return ApplyExpr("Ite", (cond, low, neg_arm))


SIGN_EXTEND_UNWRAP = Rule(
    name="SignExtendUnwrap",
    fn=_rewrite_sign_extend_unwrap,
    description=(
        "Fold Apply(unwrap_twos_complement_256:bif, SignExtend(b, x)) "
        "to Int-domain Ite(Lt(low, 2^(w-1)), low, low - 2^w), with "
        "w = 8*(b+1) and low = x when range proves 0 <= x < 2^w else "
        "Mod(x, 2^w). Avoids needing native SignExtend support in the "
        "sea encoder."
    ),
)


# NEG_S64_ZERO_TEST: the SBF saturating-sub lowering tests "is the
# negated i64 value zero" through a full sign-domain round trip::
#
#     y = Mod(x, 2^64)
#     f = Ite(Lt(y, 2^63), y, IntSub(y, 2^64))        # from_s64(y)
#     Eq(Ite(Eq(y, 2^63), x, wrap_256(IntMul(-1, f))), 0)
#
# Given y = x mod 2^64, the whole test is equivalent to ``Eq(y, 0)``:
#
# - Guard false (y != 2^63): f = from_s64(y) lies in (-2^63, 2^63)
#   and is a bijective image of y there, so f == 0 iff y == 0;
#   negation preserves zero-ness, and wrap_256 of a value v with
#   |v| < 2^63 < 2^256 is 0 iff v == 0. Arm == 0 iff y == 0.
# - Guard true (y == 2^63): the arm tests x == 0, but x mod 2^64 ==
#   2^63 != 0 forces x != 0 — the test is false, and so is y == 0.
#
# The rewrite drops the from_s64 / wrap chain from the live cone,
# keeping the zero-test in the bv domain where downstream Ite/bool
# rules and the LIA core can use it.

_WRAP_NAME = "wrap_twos_complement_256:bif"
_TWO_63 = 1 << 63
_TWO_64 = 1 << 64


def _eq_other_side(expr: TacExpr, value: int) -> TacExpr | None:
    """``Eq(a, b)`` with one side a const equal to ``value`` (either
    orientation): return the other side."""
    if not (
        isinstance(expr, ApplyExpr)
        and expr.op == "Eq"
        and len(expr.args) == 2
    ):
        return None
    a, b = expr.args
    if const_to_int(b) == value:
        return a
    if const_to_int(a) == value:
        return b
    return None


def _canon_sym(expr: TacExpr) -> str | None:
    if isinstance(expr, SymbolRef):
        return canonical_symbol(expr.name)
    return None


def _match_neg_s64_zero_test(
    expr: TacExpr, ctx: RewriteCtx
) -> SymbolRef | None:
    """Return the chunk symbol ``y`` when ``expr`` is the negated-s64
    zero test over ``y = Mod(x, 2^64)``."""
    e = _eq_other_side(expr, 0)
    if e is None:
        return None
    host = ctx.lookthrough(e)
    if not (
        isinstance(host, ApplyExpr)
        and host.op == "Ite"
        and len(host.args) == 3
    ):
        return None
    g, x, w = host.args
    x_name = _canon_sym(x)
    if x_name is None:
        return None

    y = _eq_other_side(ctx.lookthrough(g), _TWO_63)
    if y is None:
        return None
    y_name = _canon_sym(y)
    if y_name is None:
        return None

    w_in = ctx.lookthrough(w)
    if not (
        isinstance(w_in, ApplyExpr)
        and w_in.op == "Apply"
        and len(w_in.args) == 2
        and isinstance(w_in.args[0], SymbolRef)
        and w_in.args[0].name == _WRAP_NAME
    ):
        return None
    n = ctx.lookthrough(w_in.args[1])
    if not (
        isinstance(n, ApplyExpr) and n.op == "IntMul" and len(n.args) == 2
    ):
        return None
    a, b = n.args
    if const_to_int(a) == -1:
        f = b
    elif const_to_int(b) == -1:
        f = a
    else:
        return None

    f_in = ctx.lookthrough(f)
    if not (
        isinstance(f_in, ApplyExpr)
        and f_in.op == "Ite"
        and len(f_in.args) == 3
    ):
        return None
    cond, then_arm, else_arm = f_in.args
    cond_in = ctx.lookthrough(cond)
    if not (
        isinstance(cond_in, ApplyExpr)
        and cond_in.op == "Lt"
        and len(cond_in.args) == 2
        and _canon_sym(cond_in.args[0]) == y_name
        and const_to_int(cond_in.args[1]) == _TWO_63
    ):
        return None
    if _canon_sym(then_arm) != y_name:
        return None
    if not (
        isinstance(else_arm, ApplyExpr)
        and else_arm.op == "IntSub"
        and len(else_arm.args) == 2
        and _canon_sym(else_arm.args[0]) == y_name
        and const_to_int(else_arm.args[1]) == _TWO_64
    ):
        return None

    # The chunk relation that ties the guard-true arm to y: either the
    # guard arm IS y (the value being negated is already a low chunk;
    # y = y mod 2^64 needs range to prove y < 2^64), or the guard-arm
    # symbol x is the wide source y was extracted from.
    if x_name == y_name:
        rng = infer_expr_range(y, ctx)
        if rng is None or rng[1] is None or rng[1] >= _TWO_64 or rng[0] < 0:
            return None
        assert isinstance(y, SymbolRef)
        return y
    y_def = ctx.lookthrough(y)
    if not (
        isinstance(y_def, ApplyExpr)
        and y_def.op in {"Mod", "IntMod"}
        and len(y_def.args) == 2
        and _canon_sym(y_def.args[0]) == x_name
        and const_to_int(y_def.args[1]) == _TWO_64
    ):
        return None
    assert isinstance(y, SymbolRef)
    return y


def _rewrite_neg_s64_zero_test(
    expr: TacExpr, ctx: RewriteCtx
) -> TacExpr | None:
    y = _match_neg_s64_zero_test(expr, ctx)
    if y is None:
        return None
    return ApplyExpr("Eq", (y, ConstExpr("0x0")))


NEG_S64_ZERO_TEST = Rule(
    name="NegS64ZeroTest",
    fn=_rewrite_neg_s64_zero_test,
    description=(
        "Collapse Eq(Ite(Eq(y, 2^63), x, wrap_256(IntMul(-1, "
        "from_s64(y)))), 0) to Eq(y, 0) when y = Mod(x, 2^64). The "
        "saturating-sub 'negated i64 is zero' test; the sign-domain "
        "round trip preserves zero-ness exactly."
    ),
)


# WRAP_COMPARE_LIFT: an order comparison or equality between a
# ``wrap_256`` application and a constant lifts to an Int-domain
# predicate on the wrap's argument::
#
#     Cmp(wrap_256(v), c)   with   range(v) = [lo, hi]
#
# wrap_256(v) = v mod 2^256 (Euclidean). Under the gates
#
#     hi < 2^256        and        lo > c - 2^256
#
# the wrap has exactly two regimes on range(v): identity for v >= 0,
# and v + 2^256 (a value > c, since v > c - 2^256) for v < 0. Hence:
#
#     Eq(wrap(v), c)  <=>  Eq(v, c)            (negative regime: wrap(v)
#                                               lands in (c, 2^256), != c)
#     Lt(wrap(v), c)  <=>  0 <= v && v < c
#     Le(wrap(v), c)  <=>  0 <= v && v <= c
#     Gt(wrap(v), c)  <=>  v > c || v < 0
#     Ge(wrap(v), c)  <=>  v >= c || v < 0
#
# When ``lo >= 0`` the sign guard is dropped (wrap is the identity).
# The typical source is the SBF signed-arithmetic lowering comparing a
# re-encoded i64 against a small constant (``to_s256(I) < 10``); the
# lift removes the mod-2^256 opacity so LIA sees the linear argument.
#
# In practice the wrap usually sits inside an Ite arm (the neg_s64
# gadget guard), so the rule also distributes the comparison over an
# Ite operand — ``Cmp(Ite(g, a, b), c) <=> Ite(g, Cmp(a, c),
# Cmp(b, c))``, sound for any total predicate — gated on at least one
# arm (recursively) lifting, so distribution never duplicates a
# comparison without paying for itself.

_TWO_256 = 1 << 256
_INT_ZERO = ConstExpr("0x0(int)")
_CMP_FLIP = {"Lt": "Gt", "Le": "Ge", "Gt": "Lt", "Ge": "Le", "Eq": "Eq"}


def _match_wrap_apply(expr: TacExpr) -> TacExpr | None:
    if (
        isinstance(expr, ApplyExpr)
        and expr.op == "Apply"
        and len(expr.args) == 2
        and isinstance(expr.args[0], SymbolRef)
        and expr.args[0].name == _WRAP_NAME
    ):
        return expr.args[1]
    return None


def _lift_direct(
    op: str, v: TacExpr, c: int, c_expr: TacExpr, ctx: RewriteCtx
) -> TacExpr | None:
    """The core lift of ``Cmp(wrap(v), c)``; None when range gates fail."""
    rng = infer_expr_range(v, ctx)
    if rng is None or rng[0] is None or rng[1] is None:
        return None
    lo, hi = rng
    if hi >= _TWO_256 or lo <= c - _TWO_256:
        return None
    nonneg = lo >= 0
    if op == "Eq":
        return ApplyExpr("Eq", (v, c_expr))
    if op in ("Lt", "Le"):
        cmp = ApplyExpr(op, (v, c_expr))
        if nonneg:
            return cmp
        return ApplyExpr("LAnd", (ApplyExpr("Le", (_INT_ZERO, v)), cmp))
    # Gt / Ge: every negative v wraps above c (v > c - 2^256).
    cmp = ApplyExpr(op, (v, c_expr))
    if nonneg:
        return cmp
    return ApplyExpr("LOr", (cmp, ApplyExpr("Lt", (v, _INT_ZERO))))


def _lift_operand(
    op: str, operand: TacExpr, c: int, c_expr: TacExpr, ctx: RewriteCtx
) -> TacExpr | None:
    """Lift ``Cmp(operand, c)``: directly when ``operand`` is (or
    looks through to) a wrap application, or by distributing over an
    Ite operand when at least one arm lifts. None when nothing lifts
    (the caller keeps the original comparison)."""
    seen = ctx.lookthrough(operand)
    v = _match_wrap_apply(seen)
    if v is not None:
        return _lift_direct(op, v, c, c_expr, ctx)
    if not (
        isinstance(seen, ApplyExpr) and seen.op == "Ite" and len(seen.args) == 3
    ):
        return None
    guard, then_arm, else_arm = seen.args
    lifted_then = _lift_operand(op, then_arm, c, c_expr, ctx)
    lifted_else = _lift_operand(op, else_arm, c, c_expr, ctx)
    if lifted_then is None and lifted_else is None:
        return None
    return ApplyExpr(
        "Ite",
        (
            guard,
            lifted_then
            if lifted_then is not None
            else ApplyExpr(op, (then_arm, c_expr)),
            lifted_else
            if lifted_else is not None
            else ApplyExpr(op, (else_arm, c_expr)),
        ),
    )


def _rewrite_wrap_compare_lift(
    expr: TacExpr, ctx: RewriteCtx
) -> TacExpr | None:
    if not (
        isinstance(expr, ApplyExpr)
        and expr.op in _CMP_FLIP
        and len(expr.args) == 2
    ):
        return None
    a, b = expr.args
    # Normalize to Cmp(operand, c) with the constant on the right.
    op = expr.op
    operand, c_expr = a, b
    c = const_to_int(c_expr)
    if c is None or isinstance(a, ConstExpr):
        c = const_to_int(a)
        operand, c_expr = b, a
        op = _CMP_FLIP[op]
    if c is None or c < 0 or c >= _TWO_256:
        return None
    return _lift_operand(op, operand, c, c_expr, ctx)


WRAP_COMPARE_LIFT = Rule(
    name="WrapCompareLift",
    fn=_rewrite_wrap_compare_lift,
    description=(
        "Lift Cmp(wrap_256(v), c) to an Int-domain predicate on v "
        "(with a sign guard when range allows v < 0), gated on "
        "range(v) within (c - 2^256, 2^256). Removes the mod-2^256 "
        "opacity from comparisons of re-encoded signed values."
    ),
)
