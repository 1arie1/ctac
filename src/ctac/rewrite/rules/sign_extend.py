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


def _match_gadget_shape(
    host: TacExpr, ctx: RewriteCtx
) -> tuple[SymbolRef, TacExpr] | None:
    """Structural match of the negation gadget
    ``Ite(Eq(y, 2^63), x, wrap_256(IntMul(-1, from_s64(y))))``,
    WITHOUT the chunk relation tying ``x`` to ``y`` (callers add
    their own evidence). Returns ``(y, x)``."""
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

    assert isinstance(y, SymbolRef)
    return y, x


def _chunk_evidence(y: SymbolRef, x: TacExpr, ctx: RewriteCtx) -> bool:
    """Evidence for the chunk relation ``y = x mod 2^64``: either the
    guard arm IS y (the value being negated is already a low chunk;
    y = y mod 2^64 needs range to prove y < 2^64), or the guard-arm
    symbol x is the wide source y was extracted from."""
    x_name = _canon_sym(x)
    y_name = canonical_symbol(y.name)
    if x_name == y_name:
        rng = infer_expr_range(y, ctx)
        return not (
            rng is None or rng[1] is None or rng[1] >= _TWO_64 or rng[0] < 0
        )
    y_def = ctx.lookthrough(y)
    return (
        isinstance(y_def, ApplyExpr)
        and y_def.op in {"Mod", "IntMod"}
        and len(y_def.args) == 2
        and _canon_sym(y_def.args[0]) == x_name
        and const_to_int(y_def.args[1]) == _TWO_64
    )


def _match_neg_s64_gadget(
    host: TacExpr, ctx: RewriteCtx
) -> tuple[SymbolRef, TacExpr] | None:
    """Shape plus chunk evidence. Returns ``(y, x)``."""
    match = _match_gadget_shape(host, ctx)
    if match is None:
        return None
    y, x = match
    if not _chunk_evidence(y, x, ctx):
        return None
    return y, x


def _rewrite_neg_s64_zero_test(
    expr: TacExpr, ctx: RewriteCtx
) -> TacExpr | None:
    e = _eq_other_side(expr, 0)
    if e is None:
        return None
    match = _match_neg_s64_gadget(ctx.lookthrough(e), ctx)
    if match is None:
        return None
    y, _x = match
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


# NEG_S64_LOW_CHUNK / NEG_S64_SIGN_TEST: the remaining consumers of
# the negation gadget n = Ite(Eq(y, 2^63), x, wrap_256(-from_s64(y))).
#
# Low chunk -- ``Mod(n, 2^64)``. Both gadget arms agree on the value
# ``(2^64 - y) mod 2^64`` (the wrapped two's-complement negation of
# the chunk):
#
# - edge arm (y == 2^63): x mod 2^64 = y = 2^63 = 2^64 - 2^63;
# - else arm: wrap(-from_s64(y)) mod 2^64 = (-y) mod 2^64, because
#   2^64 divides 2^256 and from_s64(y) is congruent to y mod 2^64.
#
# Emitted as ``Ite(Eq(y, 0), 0, Sub(2^64, y))`` -- linear arms, no
# sign-domain residue. No range gate on x is needed (everything
# passes through mod 2^64).
#
# Sign test -- ``Slt(n, 0)`` (bv256 signed-negative, i.e. n >= 2^255):
#
# - edge arm: n = x, and the gate range(x) < 2^255 forces false;
# - else arm: wrap(v) >= 2^255 with v = -from_s64(y) in (-2^63, 2^63]
#   holds iff v < 0 iff from_s64(y) > 0 iff 0 < y < 2^63.
#
# So ``Slt(n, 0) <=> 0 < y && y < 2^63`` and the non-negative dual
# ``Sle(0, n) <=> y == 0 || y >= 2^63``. Gate: range(x) < 2^255 (the
# edge arm passes x through verbatim; without the bound, x's sign bit
# could be set while the predicate on y says "non-negative").

_TWO_255 = 1 << 255
_TWO_63_CONST = ConstExpr("0x8000000000000000")
_TWO_64_CONST = ConstExpr("0x10000000000000000")


def _chunk_expr_of(e: TacExpr, ctx: RewriteCtx) -> TacExpr | None:
    """The 2^64-chunk of ``e`` in closed form, when ``e`` is built
    from the negation gadget: the gadget itself (chunk is
    ``(-y) mod 2^64``), a bv ``Add`` of the gadget and a constant
    carry ``c`` in (0, 2^64) (chunk is ``(c - y) mod 2^64`` — Add
    wraps mod 2^256 and 2^64 divides 2^256), or an ``Ite`` whose
    arms both reduce (the carry-select shape ``Ite(B0, n, n + 1)``).
    None when the shape isn't covered — the caller abstains."""
    e_in = ctx.lookthrough(e)
    match = _match_neg_s64_gadget(e_in, ctx)
    if match is not None:
        y, _x = match
        # (-y) mod 2^64 = Ite(y == 0, 0, 2^64 - y).
        return ApplyExpr(
            "Ite",
            (
                ApplyExpr("Eq", (y, ConstExpr("0x0"))),
                ConstExpr("0x0"),
                ApplyExpr("Sub", (_TWO_64_CONST, y)),
            ),
        )
    if isinstance(e_in, ApplyExpr) and e_in.op == "Add" and len(e_in.args) == 2:
        a, b = e_in.args
        c = const_to_int(b)
        if c is None:
            c, a = const_to_int(a), b
        if c is None or c <= 0 or c >= _TWO_64:
            return None
        match = _match_neg_s64_gadget(ctx.lookthrough(a), ctx)
        if match is None:
            return None
        y, _x = match
        # (c - y) mod 2^64 = Ite(y <= c, c - y, 2^64 + c - y);
        # neither Sub wraps (y <= c on the left, y < 2^64 <= 2^64 + c
        # on the right).
        c_const = ConstExpr(f"0x{c:x}")
        high_const = ConstExpr(f"0x{_TWO_64 + c:x}")
        return ApplyExpr(
            "Ite",
            (
                ApplyExpr("Le", (y, c_const)),
                ApplyExpr("Sub", (c_const, y)),
                ApplyExpr("Sub", (high_const, y)),
            ),
        )
    if isinstance(e_in, ApplyExpr) and e_in.op == "Ite" and len(e_in.args) == 3:
        guard, then_arm, else_arm = e_in.args
        then_chunk = _chunk_expr_of(then_arm, ctx)
        if then_chunk is None:
            return None
        else_chunk = _chunk_expr_of(else_arm, ctx)
        if else_chunk is None:
            return None
        return ApplyExpr("Ite", (guard, then_chunk, else_chunk))
    return None


def _rewrite_neg_s64_low_chunk(
    expr: TacExpr, ctx: RewriteCtx
) -> TacExpr | None:
    if not (
        isinstance(expr, ApplyExpr)
        and expr.op == "Mod"
        and len(expr.args) == 2
        and const_to_int(expr.args[1]) == _TWO_64
    ):
        return None
    return _chunk_expr_of(expr.args[0], ctx)


def _rewrite_neg_s64_sign_test(
    expr: TacExpr, ctx: RewriteCtx
) -> TacExpr | None:
    if not (isinstance(expr, ApplyExpr) and len(expr.args) == 2):
        return None
    # Normalize the four zero-threshold orientations to "n negative?".
    a, b = expr.args
    if expr.op in ("Slt", "Sge") and const_to_int(b) == 0:
        n, negative_form = a, expr.op == "Slt"
    elif expr.op in ("Sgt", "Sle") and const_to_int(a) == 0:
        n, negative_form = b, expr.op == "Sgt"
    else:
        return None
    match = _match_neg_s64_gadget(ctx.lookthrough(n), ctx)
    if match is None:
        return None
    y, x = match
    rng = infer_expr_range(x, ctx)
    if rng is None or rng[1] is None or rng[1] >= _TWO_255 or rng[0] < 0:
        return None
    if negative_form:
        return ApplyExpr(
            "LAnd",
            (
                ApplyExpr("Lt", (ConstExpr("0x0"), y)),
                ApplyExpr("Lt", (y, _TWO_63_CONST)),
            ),
        )
    return ApplyExpr(
        "LOr",
        (
            ApplyExpr("Eq", (y, ConstExpr("0x0"))),
            ApplyExpr("Ge", (y, _TWO_63_CONST)),
        ),
    )


NEG_S64_LOW_CHUNK = Rule(
    name="NegS64LowChunk",
    fn=_rewrite_neg_s64_low_chunk,
    description=(
        "Mod(neg_s64_gadget(x), 2^64) -> Ite(Eq(y, 0), 0, "
        "Sub(2^64, y)): both gadget arms agree on the wrapped "
        "two's-complement negation of the chunk."
    ),
)

NEG_S64_SIGN_TEST = Rule(
    name="NegS64SignTest",
    fn=_rewrite_neg_s64_sign_test,
    description=(
        "Slt(neg_s64_gadget(x), 0) -> 0 < y && y < 2^63 (and the "
        "Sle/Sgt/Sge duals), gated on range(x) < 2^255 for the "
        "pass-through edge arm."
    ),
)


# NEG_S64_DOUBLE: the negation gadget applied to its own output --
# the abs lowering negates the already-negated low limb to recover
# the magnitude. With L the original chunk and y' = (-L) mod 2^64
# the negated one, the outer gadget value is, case by case:
#
# - L == 0:            y' = 0,  wrap(-from_s64(0)) = 0 = L
# - L in (0, 2^63):    y' = 2^64 - L in (2^63, 2^64),
#                      from_s64(y') = -L, wrap(L) = L
# - L == 2^63:         y' = 2^63, edge arm passes x' = inner edge
#                      value = L (gated below)
# - L in (2^63, 2^64): y' = 2^64 - L in (0, 2^63),
#                      wrap(L - 2^64) = 2^256 + L - 2^64
#
# i.e. the 64->256-bit sign extension of L, except the i64::MIN
# pattern (L = 2^63) stays unextended:
#
#     Ite(Le(L, 2^63), L, Add(L, 2^256 - 2^64))
#
# Two evidence forms tie the outer chunk y' to the inner gadget:
# the standard chunk relation (y' def still Mod(x', 2^64)), or y'
# def already rewritten by NEG_S64_LOW_CHUNK to its emit shape
# Ite(Eq(L, 0), 0, Sub(2^64, L)) over the same L. The edge arm
# additionally needs the inner pass-through x to BE the chunk
# (x == L, or range < 2^64 which pins x = L given x mod 2^64 = L).

_SIGN_EXT_CONST = ConstExpr(f"0x{(1 << 256) - (1 << 64):x}")


def _match_low_chunk_shape(
    e: TacExpr, ctx: RewriteCtx
) -> SymbolRef | None:
    """NEG_S64_LOW_CHUNK's emit shape ``Ite(Eq(y, 0), 0,
    Sub(2^64, y))``; returns ``y``."""
    if not (isinstance(e, ApplyExpr) and e.op == "Ite" and len(e.args) == 3):
        return None
    g, t, el = e.args
    y = _eq_other_side(ctx.lookthrough(g), 0)
    if not isinstance(y, SymbolRef):
        return None
    if const_to_int(t) != 0:
        return None
    if not (
        isinstance(el, ApplyExpr)
        and el.op == "Sub"
        and len(el.args) == 2
        and const_to_int(el.args[0]) == _TWO_64
        and _canon_sym(el.args[1]) == canonical_symbol(y.name)
    ):
        return None
    return y


def _rewrite_neg_s64_double(
    expr: TacExpr, ctx: RewriteCtx
) -> TacExpr | None:
    shape = _match_gadget_shape(expr, ctx)
    if shape is None:
        return None
    y_outer, x_outer = shape
    inner = _match_neg_s64_gadget(ctx.lookthrough(x_outer), ctx)
    if inner is None:
        return None
    y2, x_inner = inner
    y2_name = canonical_symbol(y2.name)
    if not _chunk_evidence(y_outer, x_outer, ctx):
        lc = _match_low_chunk_shape(ctx.lookthrough(y_outer), ctx)
        if lc is None or canonical_symbol(lc.name) != y2_name:
            return None
    if _canon_sym(x_inner) != y2_name:
        rng = infer_expr_range(x_inner, ctx)
        if rng is None or rng[1] is None or rng[1] >= _TWO_64 or rng[0] < 0:
            return None
    return ApplyExpr(
        "Ite",
        (
            ApplyExpr("Le", (y2, _TWO_63_CONST)),
            y2,
            ApplyExpr("Add", (y2, _SIGN_EXT_CONST)),
        ),
    )


NEG_S64_DOUBLE = Rule(
    name="NegS64Double",
    fn=_rewrite_neg_s64_double,
    description=(
        "neg_s64_gadget(neg_s64_gadget(L)) -> Ite(Le(L, 2^63), L, "
        "Add(L, 2^256 - 2^64)): the abs lowering's double negation "
        "is the 64->256 sign extension of the chunk, with the "
        "i64::MIN pattern unextended."
    ),
)


# SIGNED_CMP_NEG_ONE: comparisons against the signed -1 pattern
# (0xff..ff = 2^256 - 1) normalize to the zero threshold: in the
# signed order -1 is the immediate predecessor of 0, so
# ``x <=s -1  <=>  x <s 0`` and ``x >s -1  <=>  0 <=s x``.
# Unconditional order reasoning; the payoff is that the zero-threshold
# forms are what NEG_S64_SIGN_TEST matches.

_SIGNED_MINUS_ONE = (1 << 256) - 1


def _rewrite_signed_cmp_neg_one(
    expr: TacExpr, ctx: RewriteCtx
) -> TacExpr | None:
    if not (
        isinstance(expr, ApplyExpr)
        and expr.op in ("Slt", "Sle", "Sgt", "Sge")
        and len(expr.args) == 2
    ):
        return None
    a, b = expr.args
    zero = ConstExpr("0x0")
    if expr.op == "Sle" and const_to_int(b) == _SIGNED_MINUS_ONE:
        return ApplyExpr("Slt", (a, zero))
    if expr.op == "Sge" and const_to_int(a) == _SIGNED_MINUS_ONE:
        return ApplyExpr("Slt", (b, zero))
    if expr.op == "Sgt" and const_to_int(b) == _SIGNED_MINUS_ONE:
        return ApplyExpr("Sle", (zero, a))
    if expr.op == "Slt" and const_to_int(a) == _SIGNED_MINUS_ONE:
        return ApplyExpr("Sle", (zero, b))
    return None


SIGNED_CMP_NEG_ONE = Rule(
    name="SignedCmpNegOne",
    fn=_rewrite_signed_cmp_neg_one,
    description=(
        "Normalize signed comparisons against -1 (0xff..ff) to the "
        "zero threshold: x <=s -1 -> x <s 0, x >s -1 -> 0 <=s x."
    ),
)
