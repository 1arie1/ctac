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

from dataclasses import dataclass

from ctac.analysis.symbols import canonical_symbol
from ctac.ast.nodes import ApplyExpr, ConstExpr, SymbolRef, TacExpr
from ctac.rewrite.context import RewriteCtx
from ctac.rewrite.framework import Rule
from ctac.rewrite.range_infer import infer_expr_range
from ctac.rewrite.rules.common import DIV_OPS, const_to_int, eq_modulo_meta


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
# negated i<w> value zero" through a full sign-domain round trip
# (w in {64, 128, 256}; the i64 instance shown)::
#
#     y = Mod(x, 2^64)
#     f = Ite(Lt(y, 2^63), y, IntSub(y, 2^64))        # from_s64(y)
#     Eq(Ite(Eq(y, 2^63), x, wrap_256(IntMul(-1, f))), 0)
#
# Given y = x mod 2^w, the whole test is equivalent to ``Eq(y, 0)``:
#
# - Guard false (y != 2^(w-1)): f = from_s<w>(y) lies in
#   (-2^(w-1), 2^(w-1)) and is a bijective image of y there, so
#   f == 0 iff y == 0; negation preserves zero-ness, and wrap_256 of
#   a value v with |v| < 2^(w-1) <= 2^255 < 2^256 is 0 iff v == 0.
#   Arm == 0 iff y == 0.
# - Guard true (y == 2^(w-1)): the arm tests x == 0, but x mod 2^w ==
#   2^(w-1) != 0 forces x != 0 — the test is false, and so is y == 0.
#
# The rewrite drops the from_s<w> / wrap chain from the live cone,
# keeping the zero-test in the bv domain where downstream Ite/bool
# rules and the LIA core can use it.

_WRAP_NAME = "wrap_twos_complement_256:bif"


@dataclass(frozen=True)
class _Width:
    """Constants of one signed-chunk width ``w``: the sign-bit
    threshold ``2^(w-1)``, the modulus ``2^w``, and the w->256
    sign-extension offset ``2^256 - 2^w`` (zero at w == 256)."""

    bits: int
    half: int
    full: int
    half_const: ConstExpr
    full_const: ConstExpr
    sign_ext_value: int
    sign_ext_const: ConstExpr


def _mk_width(bits: int) -> _Width:
    half = 1 << (bits - 1)
    full = 1 << bits
    sign_ext_value = (1 << 256) - full
    return _Width(
        bits=bits,
        half=half,
        full=full,
        half_const=ConstExpr(f"0x{half:x}"),
        full_const=ConstExpr(f"0x{full:x}"),
        sign_ext_value=sign_ext_value,
        sign_ext_const=ConstExpr(f"0x{sign_ext_value:x}"),
    )


# Common SBF/EVM signed widths only -- no arbitrary-width machinery.
# Halves (2^63, 2^127, 2^255) and fulls (2^64, 2^128, 2^256) are
# pairwise disjoint, so width detection from a constant is
# unambiguous.
_WIDTHS = tuple(_mk_width(b) for b in (64, 128, 256))
_WIDTH_BY_HALF = {w.half: w for w in _WIDTHS}
_WIDTH_BY_FULL = {w.full: w for w in _WIDTHS}
# The sign-extension emit family (NEG_S64_DOUBLE's output and its
# consumers) excludes w == 256: the offset degenerates to 0 and the
# ``z <= 2^(w-1)`` arm is no longer all-positive in bv256, breaking
# the band derivations.
_SIGN_EXT_WIDTHS = tuple(w for w in _WIDTHS if w.bits < 256)


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


_UNWRAP_BIF_WIDTHS = {
    "unwrap_twos_complement_64:bif": 64,
    "unwrap_twos_complement_128:bif": 128,
    "unwrap_twos_complement_256:bif": 256,
}


def _match_from_s(
    e: TacExpr, ctx: RewriteCtx
) -> tuple[SymbolRef, _Width] | None:
    """The from_s<w> reinterpretation
    ``Ite(Lt(y, 2^(w-1)), y, IntSub(y, 2^w))``, or the equivalent
    concept bif ``Apply(unwrap_twos_complement_<w>:bif, y)`` (the
    bif is DEFINED as that total linear form); returns ``(y, w)``."""
    if (
        isinstance(e, ApplyExpr)
        and e.op == "Apply"
        and len(e.args) == 2
        and isinstance(e.args[0], SymbolRef)
        and isinstance(e.args[1], SymbolRef)
    ):
        bits = _UNWRAP_BIF_WIDTHS.get(e.args[0].name)
        if bits is not None:
            return e.args[1], _WIDTH_BY_FULL[1 << bits]
        return None
    if not (isinstance(e, ApplyExpr) and e.op == "Ite" and len(e.args) == 3):
        return None
    cond, then_arm, else_arm = e.args
    y_name = _canon_sym(then_arm)
    if y_name is None:
        return None
    if not (
        isinstance(else_arm, ApplyExpr)
        and else_arm.op == "IntSub"
        and len(else_arm.args) == 2
        and _canon_sym(else_arm.args[0]) == y_name
    ):
        return None
    width = _WIDTH_BY_FULL.get(const_to_int(else_arm.args[1]))
    if width is None:
        return None
    cond_in = ctx.lookthrough(cond)
    if not (
        isinstance(cond_in, ApplyExpr)
        and cond_in.op == "Lt"
        and len(cond_in.args) == 2
        and _canon_sym(cond_in.args[0]) == y_name
        and const_to_int(cond_in.args[1]) == width.half
    ):
        return None
    assert isinstance(then_arm, SymbolRef)
    return then_arm, width


def _eq_half_other_side(
    expr: TacExpr,
) -> tuple[TacExpr, _Width] | None:
    """``Eq(a, b)`` with one side the sign-bit threshold ``2^(w-1)``
    of a supported width (either orientation): return the other side
    and the width."""
    if not (
        isinstance(expr, ApplyExpr)
        and expr.op == "Eq"
        and len(expr.args) == 2
    ):
        return None
    a, b = expr.args
    width = _WIDTH_BY_HALF.get(const_to_int(b))
    if width is not None:
        return a, width
    width = _WIDTH_BY_HALF.get(const_to_int(a))
    if width is not None:
        return b, width
    return None


def _match_gadget_shape(
    host: TacExpr, ctx: RewriteCtx
) -> tuple[SymbolRef, TacExpr, _Width] | None:
    """Structural match of the negation gadget
    ``Ite(Eq(y, 2^(w-1)), x, wrap_256(IntMul(-1, from_s<w>(y))))``,
    WITHOUT the chunk relation tying ``x`` to ``y`` (callers add
    their own evidence). Returns ``(y, x, w)``."""
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

    edge = _eq_half_other_side(ctx.lookthrough(g))
    if edge is None:
        return None
    y, width = edge
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

    f_match = _match_from_s(ctx.lookthrough(f), ctx)
    if f_match is None:
        return None
    f_y, f_width = f_match
    if canonical_symbol(f_y.name) != y_name or f_width is not width:
        return None

    assert isinstance(y, SymbolRef)
    return y, x, width


def _chunk_evidence(
    y: SymbolRef, x: TacExpr, ctx: RewriteCtx, width: _Width
) -> bool:
    """Evidence for the chunk relation ``y = x mod 2^w``: either the
    guard arm IS y (the value being negated is already a low chunk;
    y = y mod 2^w needs range to prove y < 2^w), or the guard-arm
    symbol x is the wide source y was extracted from."""
    x_name = _canon_sym(x)
    y_name = canonical_symbol(y.name)
    if x_name == y_name:
        rng = infer_expr_range(y, ctx)
        return not (
            rng is None
            or rng[1] is None
            or rng[1] >= width.full
            or rng[0] < 0
        )
    y_def = ctx.lookthrough(y)
    return (
        isinstance(y_def, ApplyExpr)
        and y_def.op in {"Mod", "IntMod"}
        and len(y_def.args) == 2
        and _canon_sym(y_def.args[0]) == x_name
        and const_to_int(y_def.args[1]) == width.full
    )


def _match_neg_gadget(
    host: TacExpr, ctx: RewriteCtx
) -> tuple[SymbolRef, TacExpr, _Width] | None:
    """Shape plus chunk evidence. Returns ``(y, x, w)``."""
    match = _match_gadget_shape(host, ctx)
    if match is None:
        return None
    y, x, width = match
    if not _chunk_evidence(y, x, ctx, width):
        return None
    return y, x, width


def _rewrite_neg_s64_zero_test(
    expr: TacExpr, ctx: RewriteCtx
) -> TacExpr | None:
    e = _eq_other_side(expr, 0)
    if e is None:
        return None
    match = _match_neg_gadget(ctx.lookthrough(e), ctx)
    if match is None:
        return None
    y, _x, _width = match
    return ApplyExpr("Eq", (y, ConstExpr("0x0")))


NEG_S64_ZERO_TEST = Rule(
    name="NegS64ZeroTest",
    fn=_rewrite_neg_s64_zero_test,
    description=(
        "Collapse Eq(Ite(Eq(y, 2^(w-1)), x, wrap_256(IntMul(-1, "
        "from_s<w>(y)))), 0) to Eq(y, 0) when y = Mod(x, 2^w), "
        "w in {64, 128, 256}. The saturating-sub 'negated i<w> is "
        "zero' test; the sign-domain round trip preserves zero-ness "
        "exactly."
    ),
)


# Gadget-plus-one consumers. The i128 helper's increment-then-test
# idiom applies the bv Add(_, 1) to a gadget value before comparing:
#
#     Eq(Add(gadget(x, y), 1), 0)    and    Le(Add(gadget(x, y), 1), c)
#
# With chunk evidence y = x mod 2^w, the +1 regimes of
# v = (gadget + 1) mod 2^256 are:
#
#     y == 0          v = 1
#     y == 1          v = 0                      (the wrap-to-zero case)
#     1 < y < 2^(w-1) v = 2^256 - y + 1          (huge)
#     y == 2^(w-1)    v = x + 1                  (MIN arm; x ≡ 2^(w-1)
#                                                 mod 2^w, so no wrap)
#     y > 2^(w-1)     v = 2^w - y + 1            (in [2, 2^(w-1)])
#
# Hence Eq(v, 0) <=> Eq(y, 1) unconditionally (the chunk congruence
# kills the MIN arm: x + 1 ≢ 0 mod 2^w), and for a constant
# c in [1, 2^256 - 2^(w-1)]:
#
#     Le(v, c) <=> y <= 1
#                  \/ y >= max(2^(w-1) + 1, 2^w + 1 - c)
#                  \/ (y == 2^(w-1) /\ x <= c - 1)
#
# where the MIN-arm disjunct is emitted only when c - 1 >= 2^(w-1)
# (below that, x ≡ 2^(w-1) mod 2^w forces x > c - 1 — pruned at emit
# rather than left for a fold that has no shallow evidence on x).
# Both lemmas are z3-checked at every width in the test file.


def _match_gadget_plus_one(
    expr: TacExpr, ctx: RewriteCtx
) -> tuple[SymbolRef, TacExpr, _Width] | None:
    """``Add(gadget, 1)`` (the wrapping bv Add, either operand
    order); the gadget side resolves through lookthrough and must
    carry chunk evidence. Returns ``(y, x, w)``."""
    if not (
        isinstance(expr, ApplyExpr)
        and expr.op == "Add"
        and len(expr.args) == 2
    ):
        return None
    a, b = expr.args
    if const_to_int(b) == 1:
        host = a
    elif const_to_int(a) == 1:
        host = b
    else:
        return None
    return _match_neg_gadget(ctx.lookthrough(host), ctx)


def _rewrite_neg_s64_plus_one_zero_test(
    expr: TacExpr, ctx: RewriteCtx
) -> TacExpr | None:
    e = _eq_other_side(expr, 0)
    if e is None:
        return None
    match = _match_gadget_plus_one(ctx.lookthrough(e), ctx)
    if match is None:
        return None
    y, _x, _width = match
    return ApplyExpr("Eq", (y, ConstExpr("0x1")))


def _rewrite_neg_s64_plus_one_cmp_lift(
    expr: TacExpr, ctx: RewriteCtx
) -> TacExpr | None:
    if not (
        isinstance(expr, ApplyExpr)
        and expr.op in {"Le", "Lt"}
        and len(expr.args) == 2
    ):
        return None
    lhs, rhs = expr.args
    c = const_to_int(rhs)
    if c is None:
        return None
    if expr.op == "Lt":
        c = c - 1
    if c < 1:
        # Le(v, 0) is the zero test's shape; Lt(v, 0) never holds.
        return None
    match = _match_gadget_plus_one(ctx.lookthrough(lhs), ctx)
    if match is None:
        return None
    y, x, width = match
    if c > _TWO_256 - width.half:
        # The mid regime (huge values) would dip under c.
        return None
    k = max(width.half + 1, width.full + 1 - c)
    band: TacExpr = ApplyExpr(
        "LOr",
        (
            ApplyExpr("Le", (y, ConstExpr("0x1"))),
            ApplyExpr("Ge", (y, ConstExpr(f"0x{k:x}"))),
        ),
    )
    if c - 1 >= width.half:
        min_arm = ApplyExpr(
            "LAnd",
            (
                ApplyExpr("Eq", (y, width.half_const)),
                ApplyExpr("Le", (x, ConstExpr(f"0x{c - 1:x}"))),
            ),
        )
        band = ApplyExpr("LOr", (band, min_arm))
    return band


NEG_S64_PLUS_ONE_ZERO_TEST = Rule(
    name="NegS64PlusOneZeroTest",
    fn=_rewrite_neg_s64_plus_one_zero_test,
    description=(
        "Eq(Add(gadget(x, y), 1), 0) -> Eq(y, 1) when y = Mod(x, "
        "2^w). The +1 wraps the negated chunk to zero exactly at "
        "y == 1; the chunk congruence kills the i<w>::MIN arm."
    ),
)
NEG_S64_PLUS_ONE_CMP_LIFT = Rule(
    name="NegS64PlusOneCmpLift",
    fn=_rewrite_neg_s64_plus_one_cmp_lift,
    description=(
        "Le/Lt(Add(gadget(x, y), 1), c) -> band on y (plus a MIN-arm "
        "residue on x when c reaches the sign half). Removes the "
        "increment-then-compare gadget opacity so LIA sees chunk "
        "bands."
    ),
)


# Bare Int-negation band consumer. The no-overflow assumes carry the
# negated signed value WITHOUT the wrap round trip:
#
#     Cmp(IntMul(-1, from_s<w>(y)), c)        (Int domain, no mod)
#
# With chunk evidence y in [0, 2^w), v = -from_s<w>(y) has two
# regimes: v = -y (non-positive) for y < 2^(w-1) and v = 2^w - y
# (in [1, 2^(w-1)]) for y >= 2^(w-1). Every comparison against an
# int const c becomes a band on y (H = 2^(w-1), F = 2^w):
#
#     Le(v, c):  c >= H: true;  c == 0: y < H;
#                0 < c < H: y < H \/ y >= F - c;
#                c < 0: false if -c >= H else -c <= y < H
#     Ge(v, c):  c <= -(H-1): true;
#                c == 0: y == 0 \/ y >= H;
#                -(H-1) < c < 0: y <= -c \/ y >= H;
#                c > 0: false if F - c < H else H <= y <= F - c
#     Eq(v, c):  c == 0: y == 0;  0 < c <= H: y == F - c;
#                -(H-1) <= c < 0: y == -c;  else false
#
# Lt / Gt reduce to Le(c-1) / Ge(c+1) over Int. The whole table is
# z3-checked at every width in the test file. (Eq with c == 0 is
# also reachable via INT_MUL_EQ_ZERO + FROM_S64_ZERO_TEST — same
# result either way.)


def _match_neg_from_s(
    e: TacExpr, ctx: RewriteCtx
) -> tuple[SymbolRef, _Width] | None:
    """``IntMul(-1, from_s<w>(y))`` via lookthrough, with ``y`` a
    ranged w-chunk. Returns ``(y, w)``."""
    n = ctx.lookthrough(e)
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
    m = _match_from_s(ctx.lookthrough(f), ctx)
    if m is None:
        return None
    y, width = m
    if not _ranged_in_width(y, ctx, width):
        return None
    return y, width


def _hex_const(k: int) -> ConstExpr:
    return ConstExpr(f"0x{k:x}")


def _neg_from_s_le_band(y: SymbolRef, width: _Width, c: int) -> TacExpr:
    if c >= width.half:
        return ConstExpr("true")
    lt_h = ApplyExpr("Lt", (y, width.half_const))
    if c == 0:
        return lt_h
    if c > 0:
        return ApplyExpr(
            "LOr", (lt_h, ApplyExpr("Ge", (y, _hex_const(width.full - c))))
        )
    if -c >= width.half:
        return ConstExpr("false")
    return ApplyExpr(
        "LAnd", (ApplyExpr("Ge", (y, _hex_const(-c))), lt_h)
    )


def _neg_from_s_ge_band(y: SymbolRef, width: _Width, c: int) -> TacExpr:
    if c <= 0:
        if -c >= width.half - 1:
            return ConstExpr("true")
        first: TacExpr = (
            ApplyExpr("Eq", (y, ConstExpr("0x0")))
            if c == 0
            else ApplyExpr("Le", (y, _hex_const(-c)))
        )
        return ApplyExpr(
            "LOr", (first, ApplyExpr("Ge", (y, width.half_const)))
        )
    if width.full - c < width.half:
        return ConstExpr("false")
    return ApplyExpr(
        "LAnd",
        (
            ApplyExpr("Ge", (y, width.half_const)),
            ApplyExpr("Le", (y, _hex_const(width.full - c))),
        ),
    )


def _neg_from_s_eq_band(y: SymbolRef, width: _Width, c: int) -> TacExpr:
    if c == 0:
        return ApplyExpr("Eq", (y, ConstExpr("0x0")))
    if 0 < c <= width.half:
        return ApplyExpr("Eq", (y, _hex_const(width.full - c)))
    if -(width.half - 1) <= c < 0:
        return ApplyExpr("Eq", (y, _hex_const(-c)))
    return ConstExpr("false")


_NEG_FROM_S_OPS = frozenset({"Le", "Lt", "Ge", "Gt", "Eq"})


def _rewrite_neg_from_s_cmp_lift(
    expr: TacExpr, ctx: RewriteCtx
) -> TacExpr | None:
    if not (
        isinstance(expr, ApplyExpr)
        and expr.op in _NEG_FROM_S_OPS
        and len(expr.args) == 2
    ):
        return None
    a, b = expr.args
    op = expr.op
    c = const_to_int(b)
    host = a
    if c is None:
        c = const_to_int(a)
        host = b
        if c is None:
            return None
        op = _CMP_FLIP[op]
    m = _match_neg_from_s(host, ctx)
    if m is None:
        return None
    y, width = m
    if op == "Lt":
        op, c = "Le", c - 1
    elif op == "Gt":
        op, c = "Ge", c + 1
    if op == "Le":
        return _neg_from_s_le_band(y, width, c)
    if op == "Ge":
        return _neg_from_s_ge_band(y, width, c)
    return _neg_from_s_eq_band(y, width, c)


NEG_FROM_S_CMP_LIFT = Rule(
    name="NegFromSCmpLift",
    fn=_rewrite_neg_from_s_cmp_lift,
    description=(
        "Cmp(IntMul(-1, from_s<w>(y)), c) -> band on y when y is a "
        "ranged w-chunk. The Int-domain negated signed value in the "
        "no-overflow assumes; removes the from_s opacity so LIA sees "
        "chunk bands."
    ),
)


# Negation-chunk band consumer. The materialized unsigned negation
# chunk ``(-y) mod 2^w`` appears as
#
#     Ite(g, 0, IntSub(2^w, y))      with g  <=>  Eq(y, 0)
#
# where the guard is either the direct zero test (possibly behind a
# purify TB symbol) or its R4-lifted form ``Lt(x, 2^w)`` when ``y``'s
# def is ``Div(x, 2^w)`` (``x < 2^w  <=>  x / 2^w == 0`` for
# non-negative ``x`` — z3-checked alongside the band table). With
# chunk evidence ``y in [0, 2^w)``, ``v = (-y) mod 2^w`` is 0 at
# ``y == 0`` and ``2^w - y in [1, 2^w-1]`` elsewhere, so order
# compares against an int const become bands on ``y`` (F = 2^w):
#
#     Le(v, c):  c < 0: false;  c >= F-1: true;  c == 0: y == 0;
#                else: y == 0 \/ y >= F - c
#     Ge(v, c):  c <= 0: true;  c > F-1: false;
#                else: 1 <= y <= F - c
#
# Lt / Gt reduce to Le(c-1) / Ge(c+1) over Int. Eq is deliberately
# NOT handled: ``Eq(Ite(...), c)`` is EQ_ITE_DIST's territory (the
# const arm folds, so distribution fires first bottom-up) and the
# distributed pieces resolve through EqSubZero + the existing zero
# tests. Order compares have no distribution rule, so the lift owns
# them. Bands on a Div-defined ``y`` get lifted further to
# X-windows by R4 in the final phase.


def _guard_is_y_zero(
    g: TacExpr, y: SymbolRef, ctx: RewriteCtx, width: _Width
) -> bool:
    g_in = ctx.lookthrough(g)
    z = _eq_other_side(g_in, 0)
    if z is not None and _canon_sym(z) == canonical_symbol(y.name):
        return True
    if (
        isinstance(g_in, ApplyExpr)
        and g_in.op == "Lt"
        and len(g_in.args) == 2
        and const_to_int(g_in.args[1]) == width.full
    ):
        x_name = _canon_sym(g_in.args[0])
        if x_name is None:
            return False
        y_def = ctx.lookthrough(y)
        return (
            isinstance(y_def, ApplyExpr)
            and y_def.op in DIV_OPS
            and len(y_def.args) == 2
            and _canon_sym(y_def.args[0]) == x_name
            and const_to_int(y_def.args[1]) == width.full
        )
    return False


def _match_neg_chunk(
    e: TacExpr, ctx: RewriteCtx
) -> tuple[SymbolRef, _Width] | None:
    """``Ite(g, 0, IntSub(2^w, y))`` with ``g <=> Eq(y, 0)`` and
    ``y`` a ranged w-chunk. Returns ``(y, w)``."""
    host = ctx.lookthrough(e)
    if not (
        isinstance(host, ApplyExpr)
        and host.op == "Ite"
        and len(host.args) == 3
    ):
        return None
    g, zero_arm, sub = host.args
    if const_to_int(zero_arm) != 0:
        return None
    if not (
        isinstance(sub, ApplyExpr)
        and sub.op in ("IntSub", "Sub")
        and len(sub.args) == 2
        and isinstance(sub.args[1], SymbolRef)
    ):
        return None
    y = sub.args[1]
    width = _WIDTH_BY_FULL.get(const_to_int(sub.args[0]))
    if width is None:
        return None
    if not _guard_is_y_zero(g, y, ctx, width):
        return None
    if not _ranged_in_width(y, ctx, width):
        return None
    return y, width


def _neg_chunk_le_band(y: SymbolRef, width: _Width, c: int) -> TacExpr:
    if c < 0:
        return ConstExpr("false")
    if c >= width.full - 1:
        return ConstExpr("true")
    is_zero = ApplyExpr("Eq", (y, ConstExpr("0x0")))
    if c == 0:
        return is_zero
    return ApplyExpr(
        "LOr", (is_zero, ApplyExpr("Ge", (y, _hex_const(width.full - c))))
    )


def _neg_chunk_ge_band(y: SymbolRef, width: _Width, c: int) -> TacExpr:
    if c <= 0:
        return ConstExpr("true")
    if c > width.full - 1:
        return ConstExpr("false")
    return ApplyExpr(
        "LAnd",
        (
            ApplyExpr("Ge", (y, ConstExpr("0x1"))),
            ApplyExpr("Le", (y, _hex_const(width.full - c))),
        ),
    )


_NEG_CHUNK_OPS = frozenset({"Le", "Lt", "Ge", "Gt"})


def _rewrite_neg_chunk_cmp_lift(
    expr: TacExpr, ctx: RewriteCtx
) -> TacExpr | None:
    if not (isinstance(expr, ApplyExpr) and len(expr.args) == 2):
        return None
    if expr.op == "Eq":
        # Pre-R4 sign-test form: the SBF `>> (w-1)` idiom arrives as
        # ``Eq(Div(negchunk, k), 0)`` (N4-canonicalized), and R4 only
        # exposes the order compare in the final fold loop — after
        # the consumer phases. Compose the one-step Euclidean
        # reduction ``Div(v, k) == 0  <=>  v < k`` (v >= 0, k > 0)
        # into the consumer so the lift fires in one run.
        e = _eq_other_side(expr, 0)
        if e is None:
            return None
        d = ctx.lookthrough(e)
        if not (
            isinstance(d, ApplyExpr)
            and d.op in DIV_OPS
            and len(d.args) == 2
        ):
            return None
        k = const_to_int(d.args[1])
        if k is None or k <= 0:
            return None
        m = _match_neg_chunk(d.args[0], ctx)
        if m is None:
            return None
        y, width = m
        return _neg_chunk_le_band(y, width, k - 1)
    if expr.op not in _NEG_CHUNK_OPS:
        return None
    a, b = expr.args
    op = expr.op
    c = const_to_int(b)
    host = a
    if c is None:
        c = const_to_int(a)
        host = b
        if c is None:
            return None
        op = _CMP_FLIP[op]
    m = _match_neg_chunk(host, ctx)
    if m is None:
        return None
    y, width = m
    if op == "Lt":
        op, c = "Le", c - 1
    elif op == "Gt":
        op, c = "Ge", c + 1
    if op == "Le":
        return _neg_chunk_le_band(y, width, c)
    return _neg_chunk_ge_band(y, width, c)


NEG_CHUNK_CMP_LIFT = Rule(
    name="NegChunkCmpLift",
    fn=_rewrite_neg_chunk_cmp_lift,
    description=(
        "Order compare on the materialized negation chunk "
        "Ite(Eq(y, 0), 0, IntSub(2^w, y)) lifts to a band on y "
        "(guard also matched in its R4-lifted Lt(x, 2^w) form for "
        "y = Div(x, 2^w)). Bands on a Div-defined y reach R4 for "
        "the X-window lift."
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
# the width-w negation gadget
# n = Ite(Eq(y, 2^(w-1)), x, wrap_256(-from_s<w>(y))).
#
# Low chunk -- ``Mod(n, 2^w)``. Both gadget arms agree on the value
# ``(2^w - y) mod 2^w`` (the wrapped two's-complement negation of
# the chunk):
#
# - edge arm (y == 2^(w-1)): x mod 2^w = y = 2^(w-1) = 2^w - 2^(w-1);
# - else arm: wrap(-from_s<w>(y)) mod 2^w = (-y) mod 2^w, because
#   2^w divides 2^256 and from_s<w>(y) is congruent to y mod 2^w.
#
# Emitted as ``Ite(Eq(y, 0), 0, Sub(2^w, y))`` -- linear arms, no
# sign-domain residue. No range gate on x is needed (everything
# passes through mod 2^w).
#
# Sign test -- ``Slt(n, 0)`` (bv256 signed-negative, i.e. n >= 2^255):
#
# - edge arm: n = x, and the gate range(x) < 2^255 forces false;
# - else arm: wrap(v) >= 2^255 with v = -from_s<w>(y) in
#   (-2^(w-1), 2^(w-1)) holds iff v < 0 iff from_s<w>(y) > 0 iff
#   0 < y < 2^(w-1)  (for v >= 0, v < 2^(w-1) <= 2^255; for v < 0,
#   wrap(v) = 2^256 + v > 2^256 - 2^(w-1) >= 2^255 -- both bounds
#   hold at every supported width including 256).
#
# So ``Slt(n, 0) <=> 0 < y && y < 2^(w-1)`` and the non-negative dual
# ``Sle(0, n) <=> y == 0 || y >= 2^(w-1)``. Gate: range(x) < 2^255
# (the edge arm passes x through verbatim; without the bound, x's
# sign bit could be set while the predicate on y says "non-negative").

_TWO_255 = 1 << 255


def _chunk_expr_of(
    e: TacExpr, ctx: RewriteCtx, width: _Width
) -> TacExpr | None:
    """The 2^w-chunk of ``e`` in closed form, when ``e`` is built
    from the width-w negation gadget: the gadget itself (chunk is
    ``(-y) mod 2^w``), a bv ``Add`` of the gadget and a constant
    carry ``c`` in (0, 2^w) (chunk is ``(c - y) mod 2^w`` — Add
    wraps mod 2^256 and 2^w divides 2^256), or an ``Ite`` whose
    arms both reduce (the carry-select shape ``Ite(B0, n, n + 1)``).
    None when the shape isn't covered — the caller abstains."""
    e_in = ctx.lookthrough(e)
    match = _match_neg_gadget(e_in, ctx)
    if match is not None and match[2] is width:
        y, _x, _w = match
        # (-y) mod 2^w = Ite(y == 0, 0, 2^w - y).
        return ApplyExpr(
            "Ite",
            (
                ApplyExpr("Eq", (y, ConstExpr("0x0"))),
                ConstExpr("0x0"),
                ApplyExpr("Sub", (width.full_const, y)),
            ),
        )
    if isinstance(e_in, ApplyExpr) and e_in.op == "Add" and len(e_in.args) == 2:
        a, b = e_in.args
        c = const_to_int(b)
        if c is None:
            c, a = const_to_int(a), b
        if c is None or c <= 0 or c >= width.full:
            return None
        match = _match_neg_gadget(ctx.lookthrough(a), ctx)
        if match is None or match[2] is not width:
            return None
        y, _x, _w = match
        # (c - y) mod 2^w = Ite(y <= c, c - y, 2^w + c - y);
        # neither Sub wraps (y <= c on the left, y < 2^w <= 2^w + c
        # on the right).
        c_const = ConstExpr(f"0x{c:x}")
        high_const = ConstExpr(f"0x{width.full + c:x}")
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
        then_chunk = _chunk_expr_of(then_arm, ctx, width)
        if then_chunk is None:
            return None
        else_chunk = _chunk_expr_of(else_arm, ctx, width)
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
    ):
        return None
    width = _WIDTH_BY_FULL.get(const_to_int(expr.args[1]))
    if width is None:
        return None
    return _chunk_expr_of(expr.args[0], ctx, width)


def _rewrite_neg_s64_sign_test(
    expr: TacExpr, ctx: RewriteCtx
) -> TacExpr | None:
    if not (isinstance(expr, ApplyExpr) and len(expr.args) == 2):
        return None
    # Normalize all eight zero-threshold orientations to one of
    # "lt" (n <s 0), "le", "gt", "ge".
    a, b = expr.args
    if const_to_int(b) == 0:
        n = a
        rel = {"Slt": "lt", "Sle": "le", "Sgt": "gt", "Sge": "ge"}.get(
            expr.op
        )
    elif const_to_int(a) == 0:
        n = b
        rel = {"Slt": "gt", "Sle": "ge", "Sgt": "lt", "Sge": "le"}.get(
            expr.op
        )
    else:
        return None
    if rel is None:
        return None
    match = _match_neg_gadget(ctx.lookthrough(n), ctx)
    if match is None:
        return None
    y, x, width = match
    rng = infer_expr_range(x, ctx)
    if rng is None or rng[1] is None or rng[1] >= _TWO_255 or rng[0] < 0:
        return None
    # The gadget value is negative iff 0 < y < 2^(w-1), zero iff
    # y == 0 (the zero-test lemma), positive iff y >= 2^(w-1) (the
    # edge arm passes x = y under the range gate).
    zero = ConstExpr("0x0")
    if rel == "lt":
        return ApplyExpr(
            "LAnd",
            (
                ApplyExpr("Lt", (zero, y)),
                ApplyExpr("Lt", (y, width.half_const)),
            ),
        )
    if rel == "ge":
        return ApplyExpr(
            "LOr",
            (
                ApplyExpr("Eq", (y, zero)),
                ApplyExpr("Ge", (y, width.half_const)),
            ),
        )
    if rel == "gt":
        return ApplyExpr("Ge", (y, width.half_const))
    return ApplyExpr("Lt", (y, width.half_const))


NEG_S64_LOW_CHUNK = Rule(
    name="NegS64LowChunk",
    fn=_rewrite_neg_s64_low_chunk,
    description=(
        "Mod(neg_gadget(x), 2^w) -> Ite(Eq(y, 0), 0, "
        "Sub(2^w, y)): both gadget arms agree on the wrapped "
        "two's-complement negation of the chunk (w in "
        "{64, 128, 256})."
    ),
)

NEG_S64_SIGN_TEST = Rule(
    name="NegS64SignTest",
    fn=_rewrite_neg_s64_sign_test,
    description=(
        "Slt(neg_gadget(x), 0) -> 0 < y && y < 2^(w-1) (and the "
        "Sle/Sgt/Sge duals), gated on range(x) < 2^255 for the "
        "pass-through edge arm."
    ),
)


# NEG_S64_DOUBLE: the negation gadget applied to its own output --
# the abs lowering negates the already-negated low limb to recover
# the magnitude. With L the original chunk and y' = (-L) mod 2^w
# the negated one, the outer gadget value is, case by case (h =
# 2^(w-1), f = 2^w):
#
# - L == 0:        y' = 0,  wrap(-from_s<w>(0)) = 0 = L
# - L in (0, h):   y' = f - L in (h, f),
#                  from_s<w>(y') = -L, wrap(L) = L
# - L == h:        y' = h, edge arm passes x' = inner edge
#                  value = L (gated below)
# - L in (h, f):   y' = f - L in (0, h),
#                  wrap(L - f) = 2^256 + L - f
#
# i.e. the w->256-bit sign extension of L, except the iw::MIN
# pattern (L = 2^(w-1)) stays unextended:
#
#     Ite(Le(L, 2^(w-1)), L, Add(L, 2^256 - 2^w))
#
# Two evidence forms tie the outer chunk y' to the inner gadget:
# the standard chunk relation (y' def still Mod(x', 2^w)), or y'
# def already rewritten by NEG_S64_LOW_CHUNK to its emit shape
# Ite(Eq(L, 0), 0, Sub(2^w, L)) over the same L. The edge arm
# additionally needs the inner pass-through x to BE the chunk
# (x == L, or range < 2^w which pins x = L given x mod 2^w = L).
# Inner and outer gadgets must agree on the width.
#
# Carry composition (the high-limb un-borrow): the outer gadget's
# input is x' = n1 + c with n1 the inner gadget and c a 0/1 carry
# (conditional ``Ite(g, n1, n1 + 1)`` or unconditional ``n1 + 1``).
# Then y' = (c - y2) mod 2^w and the value is the sign extension of
# z = (-y') mod 2^w = (y2 - c) mod 2^w, uniformly:
#
# - off-edge: wrap(-from_s<w>(y')) is the s256 encoding of
#   -from_s<w> of the negated chunk -- the same bijection argument
#   as the plain case, with z in place of L.
# - outer edge (y' == h), carry branch: y2 = h + 1, the inner
#   gadget is off ITS edge, n1 = wrap(-from_s<w>(h+1)) = h - 1,
#   x' = h = z exactly (no inner gate needed on this branch).
# - outer edge, no-carry branch: y2 = h, inner at its edge,
#   x' = x_inner -- pinned to h by the inner edge gate.


def _match_low_chunk_shape(
    e: TacExpr, ctx: RewriteCtx, width: _Width
) -> SymbolRef | None:
    """NEG_S64_LOW_CHUNK's emit shape ``Ite(Eq(y, 0), 0,
    Sub(2^w, y))`` at the given width; returns ``y``."""
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
        and const_to_int(el.args[0]) == width.full
        and _canon_sym(el.args[1]) == canonical_symbol(y.name)
    ):
        return None
    return y


def _inner_edge_gate(
    x_inner: TacExpr, y2_name: str, ctx: RewriteCtx, width: _Width
) -> bool:
    """The inner gadget's pass-through arm must BE the chunk at the
    edge: x == y2, or range(x) <= 2^w. The bound may include 2^w
    itself -- the edge condition x mod 2^w == 2^(w-1) rules it out,
    so any x <= 2^w with that chunk is exactly 2^(w-1) (the carry
    sum R2549 + 1 reaches 2^w, which the strict bound rejected)."""
    if _canon_sym(x_inner) == y2_name:
        return True
    rng = infer_expr_range(x_inner, ctx)
    return not (
        rng is None or rng[1] is None or rng[1] > width.full or rng[0] < 0
    )


def _match_carry_of_gadget(
    e: TacExpr, ctx: RewriteCtx
) -> tuple[TacExpr | None, SymbolRef, TacExpr, _Width] | None:
    """The carry composition over the inner gadget:
    ``Ite(g, n1, Add(n1, 1))`` (conditional un-borrow) or
    ``Add(n1, 1)`` (unconditional), with ``n1`` the inner negation
    gadget. Returns ``(g_or_None, y2, x_inner, w)``."""
    g: TacExpr | None = None
    n1: TacExpr | None = None
    if isinstance(e, ApplyExpr) and e.op == "Ite" and len(e.args) == 3:
        g, then_arm, else_arm = e.args
        if not (
            isinstance(else_arm, ApplyExpr)
            and else_arm.op == "Add"
            and len(else_arm.args) == 2
        ):
            return None
        a, b = else_arm.args
        if const_to_int(b) == 1 and _canon_sym(a) == _canon_sym(then_arm):
            n1 = then_arm
        elif const_to_int(a) == 1 and _canon_sym(b) == _canon_sym(then_arm):
            n1 = then_arm
        else:
            return None
    elif isinstance(e, ApplyExpr) and e.op == "Add" and len(e.args) == 2:
        a, b = e.args
        if const_to_int(b) == 1:
            n1 = a
        elif const_to_int(a) == 1:
            n1 = b
        else:
            return None
    else:
        return None
    inner = _match_neg_gadget(ctx.lookthrough(n1), ctx)
    if inner is None:
        return None
    y2, x_inner, width = inner
    return g, y2, x_inner, width


def _match_carry_chunk_shape(
    e: TacExpr, ctx: RewriteCtx, y2_name: str, width: _Width
) -> bool:
    """NEG_S64_LOW_CHUNK's carry emit ``Ite(Le(y2, 1), Sub(1, y2),
    Sub(2^w + 1, y2))`` over the given chunk."""
    if not (isinstance(e, ApplyExpr) and e.op == "Ite" and len(e.args) == 3):
        return False
    g, t, el = e.args
    g_in = ctx.lookthrough(g)
    if not (
        isinstance(g_in, ApplyExpr)
        and g_in.op == "Le"
        and len(g_in.args) == 2
        and _canon_sym(g_in.args[0]) == y2_name
        and const_to_int(g_in.args[1]) == 1
    ):
        return False
    if not (
        isinstance(t, ApplyExpr)
        and t.op == "Sub"
        and len(t.args) == 2
        and const_to_int(t.args[0]) == 1
        and _canon_sym(t.args[1]) == y2_name
    ):
        return False
    return (
        isinstance(el, ApplyExpr)
        and el.op == "Sub"
        and len(el.args) == 2
        and const_to_int(el.args[0]) == width.full + 1
        and _canon_sym(el.args[1]) == y2_name
    )


def _match_carry_chunk_emit(
    e: TacExpr,
    ctx: RewriteCtx,
    y2_name: str,
    g: TacExpr | None,
    width: _Width,
) -> bool:
    """The chunk-expression emit matching the carry composition: for a
    conditional carry, ``Ite(g', plain_chunk(y2), carry_chunk(y2))``
    with ``g'`` the same condition; for an unconditional one, the
    carry-chunk shape alone."""
    if g is None:
        return _match_carry_chunk_shape(e, ctx, y2_name, width)
    if not (isinstance(e, ApplyExpr) and e.op == "Ite" and len(e.args) == 3):
        return False
    g2, t, el = e.args
    if not eq_modulo_meta(g2, g):
        return False
    lc = _match_low_chunk_shape(t, ctx, width)
    if lc is None or canonical_symbol(lc.name) != y2_name:
        return False
    return _match_carry_chunk_shape(el, ctx, y2_name, width)


def _cancelled_carry_chunk_evidence(
    y_outer: SymbolRef,
    y2: SymbolRef,
    g: TacExpr | None,
    ctx: RewriteCtx,
    width: _Width,
) -> bool:
    """CARRY_CHUNK_CANCEL may have rewritten the outer chunk's def
    to ``plain_chunk(base)`` before this rule ran. The borrow-sum
    tie ``y2 = Mod(Ite(g, base, base + 1), 2^w)`` recovers the same
    chunk relation: the cancelled and carry-selected forms are equal
    by that rule's lemma."""
    if g is None:
        return False
    lc = _match_low_chunk_shape(ctx.lookthrough(y_outer), ctx, width)
    if lc is None:
        return False
    base = _match_borrow_sum(y2, g, ctx, width)
    return base is not None and canonical_symbol(
        base.name
    ) == canonical_symbol(lc.name)


def _rewrite_neg_s64_double(
    expr: TacExpr, ctx: RewriteCtx
) -> TacExpr | None:
    shape = _match_gadget_shape(expr, ctx)
    if shape is None or shape[2].bits >= 256:
        return None
    y_outer, x_outer, width = shape
    x_lt = ctx.lookthrough(x_outer)
    inner = _match_neg_gadget(x_lt, ctx)
    if inner is not None and inner[2] is width:
        y2, x_inner, _w = inner
        y2_name = canonical_symbol(y2.name)
        if not _chunk_evidence(y_outer, x_outer, ctx, width):
            lc = _match_low_chunk_shape(
                ctx.lookthrough(y_outer), ctx, width
            )
            if lc is None or canonical_symbol(lc.name) != y2_name:
                return None
        if not _inner_edge_gate(x_inner, y2_name, ctx, width):
            return None
        return ApplyExpr(
            "Ite",
            (
                ApplyExpr("Le", (y2, width.half_const)),
                y2,
                ApplyExpr("Add", (y2, width.sign_ext_const)),
            ),
        )
    # Carry composition (the high-limb un-borrow): x' = n1 + carry
    # with n1 the inner gadget. The value is the sign extension of
    # z = (-y') mod 2^w, uniformly across both carry polarities --
    # the inner structure makes the outer edge arm land on exactly
    # z (per-branch case analysis in the module comment below; the
    # z3-gated lemma checks the whole domain).
    decomp = _match_carry_of_gadget(x_lt, ctx)
    if decomp is None or decomp[3] is not width:
        return None
    g, y2, x_inner, _w = decomp
    y2_name = canonical_symbol(y2.name)
    if not _inner_edge_gate(x_inner, y2_name, ctx, width):
        return None
    if not _chunk_evidence(y_outer, x_outer, ctx, width):
        if not _match_carry_chunk_emit(
            ctx.lookthrough(y_outer), ctx, y2_name, g, width
        ) and not _cancelled_carry_chunk_evidence(
            y_outer, y2, g, ctx, width
        ):
            return None
    # Borrow-sum composition: when y2's def is Mod(Ite(g, base,
    # base + 1), 2^w) over the SAME flag g as the carry select, the
    # outer chunk y' equals (-base) mod 2^w and the doubly-negated
    # sign extension lands on base directly. Emit plain
    # signext(base), skipping the negchunk intermediate -- whose
    # Eq(y', 0) guard the Eq-over-Ite distribution would unfold
    # before any downstream consumer could match it. Full-domain
    # z3 lemma in tests (base in [0, 2^w), shared flag).
    if g is not None:
        base = _match_borrow_sum(y2, g, ctx, width)
        if base is not None:
            return ApplyExpr(
                "Ite",
                (
                    ApplyExpr("Le", (base, width.half_const)),
                    base,
                    ApplyExpr("Add", (base, width.sign_ext_const)),
                ),
            )
    # signext((-y') mod 2^w), nested on y' directly so the Ite/Add
    # distribution rules leave it alone: y' == 0 -> 0; y' >= 2^(w-1)
    # -> z = 2^w - y' (the positive band, z <= 2^(w-1)); else the
    # negative band z + (2^256 - 2^w).
    sub = ApplyExpr("Sub", (width.full_const, y_outer))
    return ApplyExpr(
        "Ite",
        (
            ApplyExpr("Eq", (y_outer, ConstExpr("0x0"))),
            ConstExpr("0x0"),
            ApplyExpr(
                "Ite",
                (
                    ApplyExpr("Ge", (y_outer, width.half_const)),
                    sub,
                    ApplyExpr("Add", (sub, width.sign_ext_const)),
                ),
            ),
        ),
    )


NEG_S64_DOUBLE = Rule(
    name="NegS64Double",
    fn=_rewrite_neg_s64_double,
    description=(
        "neg_gadget(neg_gadget(L)) -> Ite(Le(L, 2^(w-1)), L, "
        "Add(L, 2^256 - 2^w)): the abs lowering's double negation "
        "is the w->256 sign extension of the chunk (w in {64, 128}), "
        "with the iw::MIN pattern unextended."
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


# FROM_S64_ZERO_TEST: the bare from_s<w> zero test, without the wrap
# round trip -- ``Eq(Ite(Lt(y, 2^(w-1)), y, IntSub(y, 2^w)), 0)``.
# from_s<w> maps y to y (then arm) or y - 2^w (else arm); the result
# is 0 iff y == 0 or y == 2^w, and the range gate y < 2^w excludes
# the latter. The no-overflow assumes of the i128 negation carry
# several of these deep inside their Ite trees.


def _rewrite_from_s64_zero_test(
    expr: TacExpr, ctx: RewriteCtx
) -> TacExpr | None:
    e = _eq_other_side(expr, 0)
    if e is None:
        return None
    match = _match_from_s(ctx.lookthrough(e), ctx)
    if match is None:
        return None
    y, width = match
    rng = infer_expr_range(y, ctx)
    if rng is None or rng[1] is None or rng[1] >= width.full or rng[0] < 0:
        return None
    return ApplyExpr("Eq", (y, ConstExpr("0x0")))


FROM_S64_ZERO_TEST = Rule(
    name="FromS64ZeroTest",
    fn=_rewrite_from_s64_zero_test,
    description=(
        "Eq(from_s<w>(y), 0) -> Eq(y, 0) when range proves y < 2^w "
        "(from_s<w> hits zero only at y == 0 or the excluded y == 2^w)."
    ),
)


# SIGN_EXT_SIGN_TEST / SIGN_EXT_CMP_LIFT: consumers of the
# NEG_S64_DOUBLE output shape (w in {64, 128}; the 64-bit instance
# shown)
#
#     signext(z) = Ite(Le(z, 2^63), z, Add(z, 2^256 - 2^64))
#
# with z ranged in [0, 2^64) (a chunk symbol, or the (-y') chunk Ite
# whose arms are 0 and Sub(2^64, y') under the y' != 0 guard).
#
# Sign test: the then arm is <= 2^(w-1) < 2^255; the else arm is
# >= 2^256 - 2^w + 2^(w-1) (no Add wrap given z < 2^w), so
# ``signext(z) <s 0  <=>  Gt(z, 2^(w-1))`` and the dual for ``0 <=s``.
#
# Unsigned compare against a constant c <= 2^256 - 2^w + 2^(w-1):
# the else arm exceeds c, so ``Lt(signext(z), c) <=> Le(z, 2^(w-1))
# && Lt(z, c)`` (bare ``Lt(z, c)`` when c <= 2^(w-1)), with the
# Le/Gt/Ge and Eq (c <= 2^(w-1) only) variants accordingly.


def _match_sign_ext(
    e: TacExpr, ctx: RewriteCtx
) -> tuple[str, TacExpr, _Width] | None:
    """Match either NEG_S64_DOUBLE emit form; the descriptor drives
    the consumer rewrites:

    - ``("sym", z, w)`` -- the plain form ``Ite(Le(z, 2^(w-1)), z,
      Add(z, 2^256 - 2^w))`` with the value equal to signext(z).
    - ``("negchunk", y, w)`` -- the carry form nested on the chunk:
      ``Ite(Eq(y, 0), 0, Ite(Ge(y, 2^(w-1)), 2^w - y,
      Add(2^w - y, 2^256 - 2^w)))`` with the value equal to
      signext((-y) mod 2^w).

    Both gated on the parameter's range within [0, 2^w), so the
    negative band has no Add wrap. Widths below 256 only (the
    offset degenerates at 256).
    """
    if not (isinstance(e, ApplyExpr) and e.op == "Ite" and len(e.args) == 3):
        return None
    cond, t, el = e.args
    cond_in = ctx.lookthrough(cond)
    # Plain form.
    if (
        isinstance(cond_in, ApplyExpr)
        and cond_in.op == "Le"
        and len(cond_in.args) == 2
        and eq_modulo_meta(t, cond_in.args[0])
        and isinstance(el, ApplyExpr)
        and el.op == "Add"
        and len(el.args) == 2
        and eq_modulo_meta(el.args[0], cond_in.args[0])
    ):
        width = _WIDTH_BY_HALF.get(const_to_int(cond_in.args[1]))
        if (
            width is not None
            and width.bits < 256
            and const_to_int(el.args[1]) == width.sign_ext_value
        ):
            z = cond_in.args[0]
            if _ranged_chunk(z, ctx, width):
                return "sym", z, width
        return None
    # Carry form.
    y = _eq_other_side(cond_in, 0)
    if (
        y is not None
        and const_to_int(t) == 0
        and isinstance(el, ApplyExpr)
        and el.op == "Ite"
        and len(el.args) == 3
    ):
        g2, pos, neg = el.args
        g2_in = ctx.lookthrough(g2)
        if not (
            isinstance(g2_in, ApplyExpr)
            and g2_in.op == "Ge"
            and len(g2_in.args) == 2
            and eq_modulo_meta(g2_in.args[0], y)
        ):
            return None
        width = _WIDTH_BY_HALF.get(const_to_int(g2_in.args[1]))
        if width is None or width.bits >= 256:
            return None
        sub_ok = (
            isinstance(pos, ApplyExpr)
            and pos.op == "Sub"
            and len(pos.args) == 2
            and const_to_int(pos.args[0]) == width.full
            and eq_modulo_meta(pos.args[1], y)
        )
        if (
            sub_ok
            and isinstance(neg, ApplyExpr)
            and neg.op == "Add"
            and len(neg.args) == 2
            and eq_modulo_meta(neg.args[0], pos)
            and const_to_int(neg.args[1]) == width.sign_ext_value
            and _ranged_chunk(y, ctx, width)
        ):
            return "negchunk", y, width
    return None


def _ranged_chunk(z: TacExpr, ctx: RewriteCtx, width: _Width) -> bool:
    """z in [0, 2^w): by interval inference, or structurally as a
    member of the chunk-expression emit family -- each arm of those
    Ites is in [0, 2^w) under its own guard (the carry arm
    ``Sub(1, y2)`` wraps for unguarded interval eval, but the
    ``Le(y2, 1)`` guard pins it to {0, 1})."""
    rng = infer_expr_range(z, ctx)
    if not (
        rng is None
        or rng[0] is None
        or rng[0] < 0
        or rng[1] is None
        or rng[1] >= width.full
    ):
        return True
    return _is_chunk_emit(ctx.lookthrough(z), ctx, width)


def _is_chunk_emit(e: TacExpr, ctx: RewriteCtx, width: _Width) -> bool:
    if _match_low_chunk_shape(e, ctx, width) is not None:
        return True
    if isinstance(e, ApplyExpr) and e.op == "Ite" and len(e.args) == 3:
        g, t, el = e.args
        g_in = ctx.lookthrough(g)
        # The carry shape Ite(Le(y2, 1), Sub(1, y2), Sub(2^w+1, y2)).
        if (
            isinstance(g_in, ApplyExpr)
            and g_in.op == "Le"
            and len(g_in.args) == 2
            and const_to_int(g_in.args[1]) == 1
        ):
            y2_name = _canon_sym(g_in.args[0])
            if y2_name is not None and _match_carry_chunk_shape(
                e, ctx, y2_name, width
            ):
                return True
        # A guard selecting between chunk emits.
        return _is_chunk_emit(t, ctx, width) and _is_chunk_emit(
            el, ctx, width
        )
    return False


def _rewrite_sign_ext_sign_test(
    expr: TacExpr, ctx: RewriteCtx
) -> TacExpr | None:
    if not (isinstance(expr, ApplyExpr) and len(expr.args) == 2):
        return None
    a, b = expr.args
    # Normalize all eight zero-threshold orientations to one of
    # "lt" (v <s 0), "le", "gt", "ge".
    if const_to_int(b) == 0:
        e = a
        rel = {"Slt": "lt", "Sle": "le", "Sgt": "gt", "Sge": "ge"}.get(
            expr.op
        )
    elif const_to_int(a) == 0:
        e = b
        rel = {"Slt": "gt", "Sle": "ge", "Sgt": "lt", "Sge": "le"}.get(
            expr.op
        )
    else:
        return None
    if rel is None:
        return None
    match = _match_sign_ext(ctx.lookthrough(e), ctx)
    if match is None:
        return None
    kind, arg, width = match
    half = width.half_const
    zero = ConstExpr("0x0")
    if kind == "sym":
        # v = signext(z): negative <=> z > 2^(w-1); zero <=> z == 0.
        if rel == "lt":
            return ApplyExpr("Gt", (arg, half))
        if rel == "ge":
            return ApplyExpr("Le", (arg, half))
        if rel == "gt":
            return ApplyExpr(
                "LAnd",
                (
                    ApplyExpr("Lt", (zero, arg)),
                    ApplyExpr("Le", (arg, half)),
                ),
            )
        return ApplyExpr(
            "LOr",
            (
                ApplyExpr("Eq", (arg, zero)),
                ApplyExpr("Gt", (arg, half)),
            ),
        )
    # negchunk: v = signext((-y) mod 2^w): negative <=>
    # 0 < y < 2^(w-1); zero <=> y == 0; positive <=> y >= 2^(w-1).
    if rel == "lt":
        return ApplyExpr(
            "LAnd",
            (
                ApplyExpr("Lt", (zero, arg)),
                ApplyExpr("Lt", (arg, half)),
            ),
        )
    if rel == "ge":
        return ApplyExpr(
            "LOr",
            (
                ApplyExpr("Eq", (arg, zero)),
                ApplyExpr("Ge", (arg, half)),
            ),
        )
    if rel == "gt":
        return ApplyExpr("Ge", (arg, half))
    return ApplyExpr("Lt", (arg, half))


_SIGN_EXT_CMP_FLIP = {"Lt": "Gt", "Le": "Ge", "Gt": "Lt", "Ge": "Le", "Eq": "Eq"}


def _rewrite_sign_ext_cmp_lift(
    expr: TacExpr, ctx: RewriteCtx
) -> TacExpr | None:
    if not (
        isinstance(expr, ApplyExpr)
        and expr.op in _SIGN_EXT_CMP_FLIP
        and len(expr.args) == 2
    ):
        return None
    a, b = expr.args
    op = expr.op
    e, c_expr = a, b
    c = const_to_int(c_expr)
    if c is None or isinstance(a, ConstExpr):
        c = const_to_int(a)
        e, c_expr = b, a
        op = _SIGN_EXT_CMP_FLIP[op]
    if c is None or c < 0:
        return None
    match = _match_sign_ext(ctx.lookthrough(e), ctx)
    if match is None:
        return None
    kind, arg, width = match
    if c > width.sign_ext_value + width.half:
        return None
    if kind == "sym":
        return _cmp_lift_sym(op, arg, c, c_expr, width)
    return _cmp_lift_negchunk(op, arg, c, c_expr, width)


def _cmp_lift_sym(
    op: str, z: TacExpr, c: int, c_expr: TacExpr, width: _Width
) -> TacExpr | None:
    le_cap = ApplyExpr("Le", (z, width.half_const))
    if op in ("Lt", "Le"):
        cmp = ApplyExpr(op, (z, c_expr))
        if c <= width.half:
            return cmp
        return ApplyExpr("LAnd", (le_cap, cmp))
    if op in ("Gt", "Ge"):
        # c <= 2^(w-1): the negative band (z > 2^(w-1)) already
        # exceeds c, and there z > c / z >= c holds too -- the bare
        # predicate covers both bands. c > 2^(w-1): only the
        # negative band.
        if c <= width.half:
            return ApplyExpr(op, (z, c_expr))
        return ApplyExpr("Gt", (z, width.half_const))
    if c <= width.half:
        return ApplyExpr("Eq", (z, c_expr))
    return None


def _cmp_lift_negchunk(
    op: str, y: TacExpr, c: int, c_expr: TacExpr, width: _Width
) -> TacExpr | None:
    """Value = signext((-y) mod 2^w): 0 at y == 0; 2^w - y (the
    positive band, <= 2^(w-1)) for y >= 2^(w-1); huge (negative
    band) for 0 < y < 2^(w-1). Comparisons against c become band
    predicates."""
    is_zero = ApplyExpr("Eq", (y, ConstExpr("0x0")))
    pos_band = ApplyExpr("Ge", (y, width.half_const))
    if op in ("Lt", "Le"):
        if c <= width.half:
            if op == "Lt" and c == 0:
                return None  # nothing is < 0
            # value <= c <=> y == 0, or positive band with
            # 2^w - y <= c i.e. y >= 2^w - c (>= 2^(w-1) implied).
            bound = width.full - c
            inner_op = "Ge" if op == "Le" else "Gt"
            return ApplyExpr(
                "LOr",
                (
                    is_zero,
                    ApplyExpr(
                        inner_op, (y, ConstExpr(f"0x{bound:x}"))
                    ),
                ),
            )
        # Mid band: every positive-band value (<= 2^(w-1)) passes,
        # the negative band fails.
        return ApplyExpr("LOr", (is_zero, pos_band))
    if op in ("Gt", "Ge"):
        if c <= width.half:
            # Negative band always passes; positive band needs
            # 2^w - y >= c i.e. y <= 2^w - c; y == 0 gives 0.
            bound = width.full - c
            inner_op = "Le" if op == "Ge" else "Lt"
            in_band = ApplyExpr(
                "LAnd",
                (
                    pos_band,
                    ApplyExpr(inner_op, (y, ConstExpr(f"0x{bound:x}"))),
                ),
            )
            neg_band = ApplyExpr(
                "LAnd",
                (
                    ApplyExpr("Lt", (ConstExpr("0x0"), y)),
                    ApplyExpr("Lt", (y, width.half_const)),
                ),
            )
            if c == 0:
                # value >= 0 is universal; value > 0 <=> y != 0.
                if op == "Ge":
                    return ConstExpr("true")
                return ApplyExpr("LNot", (is_zero,))
            return ApplyExpr("LOr", (neg_band, in_band))
        # Mid band: only the negative band exceeds c.
        return ApplyExpr(
            "LAnd",
            (
                ApplyExpr("Lt", (ConstExpr("0x0"), y)),
                ApplyExpr("Lt", (y, width.half_const)),
            ),
        )
    # Eq.
    if c == 0:
        return is_zero
    if c <= width.half:
        return ApplyExpr("Eq", (y, ConstExpr(f"0x{width.full - c:x}")))
    return None


SIGN_EXT_SIGN_TEST = Rule(
    name="SignExtSignTest",
    fn=_rewrite_sign_ext_sign_test,
    description=(
        "Slt(signext(z), 0) -> Gt(z, 2^(w-1)) (and the Sle/Sgt/Sge "
        "duals) over the NEG_S64_DOUBLE output shape, gated on "
        "z in [0, 2^w)."
    ),
)

SIGN_EXT_CMP_LIFT = Rule(
    name="SignExtCmpLift",
    fn=_rewrite_sign_ext_cmp_lift,
    description=(
        "Unsigned comparisons of signext(z) against constants below "
        "the negative band lift to predicates on z (Lt/Le/Gt/Ge/Eq)."
    ),
)


# MOD_DIV_PIN / CARRY_CHUNK_CANCEL: limb-fusion cancellations for
# the i128 (two-limb) negation/abs lowering, where L = Mod(X, 2^64)
# and H = Div(X, 2^64) algebra runs limb-wise and the gadget rules
# above lift WITHIN limbs but leave limb-shaped residue. Each rule
# is a closed-form linear lemma (z3-checked in tests):
#
# - Mod/Div pin: Eq(Mod(X, m), r) && Eq(Div(X, m), q) pins
#   X == q*m + r (Euclidean decomposition is a bijection) -- the
#   i128::MIN no-overflow guard ``!(L == 0 && H == 2^63)`` becomes
#   X != 2^127. The quotient also arrives R4-unfolded as the
#   aligned window a <= X < a + m.
#
# - Carry-chunk cancel: with y2 = Mod(C, 2^w) over the borrow sum
#   C = Ite(g, base, base + 1) (g <=> "no borrow"), the
#   carry-selected chunk Ite(g, plain_chunk(y2), carry_chunk(y2))
#   equals plain_chunk(base): the +1 borrow and the +1 un-borrow
#   annihilate, for base in [0, 2^w) including the C = 2^w edge.
#
# The third member of the family lives inside NEG_S64_DOUBLE: with
# the same borrow-sum tie, the doubly-negated sign extension lands
# on base directly (signext((-((-base) mod 2^w)) mod 2^w) ==
# signext(base)), and the composed emit skips the negchunk
# intermediate that the Eq-over-Ite distribution would otherwise
# unfold before any standalone consumer could match it.


def _match_low_chunk_any(
    e: TacExpr, ctx: RewriteCtx
) -> tuple[SymbolRef, _Width] | None:
    for width in _WIDTHS:
        y = _match_low_chunk_shape(e, ctx, width)
        if y is not None:
            return y, width
    return None


def _ranged_in_width(e: TacExpr, ctx: RewriteCtx, width: _Width) -> bool:
    rng = infer_expr_range(e, ctx)
    return not (
        rng is None
        or rng[0] is None
        or rng[0] < 0
        or rng[1] is None
        or rng[1] >= width.full
    )


def _match_borrow_sum(
    y2: SymbolRef, g: TacExpr, ctx: RewriteCtx, width: _Width
) -> SymbolRef | None:
    """``y2 = Mod(C, 2^w)`` with ``C = Ite(g', base, base + 1)``,
    ``g'`` the same no-borrow condition as ``g``; returns ``base``
    when range proves ``base`` in ``[0, 2^w)``."""
    y2_def = ctx.lookthrough(y2)
    if not (
        isinstance(y2_def, ApplyExpr)
        and y2_def.op in {"Mod", "IntMod"}
        and len(y2_def.args) == 2
        and const_to_int(y2_def.args[1]) == width.full
    ):
        return None
    c_def = ctx.lookthrough(y2_def.args[0])
    if not (
        isinstance(c_def, ApplyExpr)
        and c_def.op == "Ite"
        and len(c_def.args) == 3
    ):
        return None
    g2, no_borrow, borrow = c_def.args
    if not eq_modulo_meta(ctx.lookthrough(g2), ctx.lookthrough(g)):
        return None
    base_name = _canon_sym(no_borrow)
    if base_name is None:
        return None
    if not (
        isinstance(borrow, ApplyExpr)
        and borrow.op in {"Add", "IntAdd"}
        and len(borrow.args) == 2
    ):
        return None
    a, b = borrow.args
    if const_to_int(b) == 1 and _canon_sym(a) == base_name:
        pass
    elif const_to_int(a) == 1 and _canon_sym(b) == base_name:
        pass
    else:
        return None
    if not _ranged_in_width(no_borrow, ctx, width):
        return None
    assert isinstance(no_borrow, SymbolRef)
    return no_borrow


def _plain_chunk_emit(base: SymbolRef, width: _Width) -> TacExpr:
    return ApplyExpr(
        "Ite",
        (
            ApplyExpr("Eq", (base, ConstExpr("0x0"))),
            ConstExpr("0x0"),
            ApplyExpr("Sub", (width.full_const, base)),
        ),
    )


def _rewrite_carry_chunk_cancel(
    expr: TacExpr, ctx: RewriteCtx
) -> TacExpr | None:
    if not (
        isinstance(expr, ApplyExpr)
        and expr.op == "Ite"
        and len(expr.args) == 3
    ):
        return None
    g, t, el = expr.args
    plain = _match_low_chunk_any(t, ctx)
    if plain is None:
        return None
    y2, width = plain
    y2_name = canonical_symbol(y2.name)
    if not _match_carry_chunk_shape(el, ctx, y2_name, width):
        return None
    base = _match_borrow_sum(y2, g, ctx, width)
    if base is None:
        return None
    return _plain_chunk_emit(base, width)


CARRY_CHUNK_CANCEL = Rule(
    name="CarryChunkCancel",
    fn=_rewrite_carry_chunk_cancel,
    description=(
        "Ite(g, plain_chunk(y2), carry_chunk(y2)) with y2 = "
        "Mod(Ite(g, base, base + 1), 2^w) -> plain_chunk(base): the "
        "borrow into the sum and the carry-select un-borrow "
        "annihilate."
    ),
)


def _match_eq_const(expr: TacExpr) -> tuple[TacExpr, int] | None:
    """``Eq(e, c)`` with one side a constant (either orientation);
    returns ``(e, c)``."""
    if not (
        isinstance(expr, ApplyExpr)
        and expr.op == "Eq"
        and len(expr.args) == 2
    ):
        return None
    a, b = expr.args
    v = const_to_int(b)
    if v is not None and not isinstance(a, ConstExpr):
        return a, v
    v = const_to_int(a)
    if v is not None:
        return b, v
    return None


def _match_mod_residue(
    e: TacExpr, ctx: RewriteCtx
) -> tuple[str, int, int] | None:
    """``Eq(Mod(X, m), r)`` (either orientation); returns
    ``(canonical X, m, r)``."""
    eq = _match_eq_const(e)
    if eq is None:
        return None
    inner, r = eq
    inner = ctx.lookthrough(inner)
    if not (
        isinstance(inner, ApplyExpr)
        and inner.op in {"Mod", "IntMod"}
        and len(inner.args) == 2
    ):
        return None
    m = const_to_int(inner.args[1])
    x_name = _canon_sym(inner.args[0])
    if m is None or m <= 0 or x_name is None or r < 0 or r >= m:
        return None
    return x_name, m, r


def _match_const_window(
    e: TacExpr, ctx: RewriteCtx
) -> tuple[SymbolRef, int, int] | None:
    """``Ge(X, a) && Lt(X, b)`` (modulo conjunct order and compare
    orientation); returns ``(X, a, b)`` -- inclusive lower,
    exclusive upper."""
    if not (
        isinstance(e, ApplyExpr) and e.op == "LAnd" and len(e.args) == 2
    ):
        return None

    def lower(c: TacExpr) -> tuple[SymbolRef, int] | None:
        c = ctx.lookthrough(c)
        if not (isinstance(c, ApplyExpr) and len(c.args) == 2):
            return None
        a, b = c.args
        if c.op == "Ge" and isinstance(a, SymbolRef):
            v = const_to_int(b)
            return (a, v) if v is not None else None
        if c.op == "Le" and isinstance(b, SymbolRef):
            v = const_to_int(a)
            return (b, v) if v is not None else None
        return None

    def upper(c: TacExpr) -> tuple[SymbolRef, int] | None:
        c = ctx.lookthrough(c)
        if not (isinstance(c, ApplyExpr) and len(c.args) == 2):
            return None
        a, b = c.args
        if c.op == "Lt" and isinstance(a, SymbolRef):
            v = const_to_int(b)
            return (a, v) if v is not None else None
        if c.op == "Gt" and isinstance(b, SymbolRef):
            v = const_to_int(a)
            return (b, v) if v is not None else None
        return None

    c1, c2 = e.args
    for lo_c, hi_c in ((c1, c2), (c2, c1)):
        lo = lower(lo_c)
        hi = upper(hi_c)
        if lo is None or hi is None:
            continue
        x_lo, a = lo
        x_hi, b = hi
        if canonical_symbol(x_lo.name) != canonical_symbol(x_hi.name):
            continue
        return x_lo, a, b
    return None


def _match_div_quotient(
    e: TacExpr, ctx: RewriteCtx, m: int
) -> tuple[SymbolRef, int] | None:
    """Quotient evidence for modulus ``m``: ``Eq(Div(X, m), q)``
    directly, or the R4-unfolded window ``a <= X < a + m`` with
    ``m | a`` (then ``q = a / m``). Returns ``(X, q)``."""
    eq = _match_eq_const(e)
    if eq is not None:
        inner, q = eq
        inner = ctx.lookthrough(inner)
        if (
            isinstance(inner, ApplyExpr)
            and inner.op in {"Div", "IntDiv"}
            and len(inner.args) == 2
            and const_to_int(inner.args[1]) == m
            and isinstance(inner.args[0], SymbolRef)
            and q >= 0
        ):
            return inner.args[0], q
        return None
    win = _match_const_window(e, ctx)
    if win is None:
        return None
    x, a, b = win
    if b - a != m or a % m != 0 or a < 0:
        return None
    return x, a // m


def _rewrite_mod_div_pin(
    expr: TacExpr, ctx: RewriteCtx
) -> TacExpr | None:
    if not (
        isinstance(expr, ApplyExpr)
        and expr.op == "LAnd"
        and len(expr.args) == 2
    ):
        return None
    c1, c2 = expr.args
    for mod_c, div_c in ((c1, c2), (c2, c1)):
        mz = _match_mod_residue(ctx.lookthrough(mod_c), ctx)
        if mz is None:
            continue
        x_name, m, r = mz
        quot = _match_div_quotient(ctx.lookthrough(div_c), ctx, m)
        if quot is None:
            continue
        x, q = quot
        if canonical_symbol(x.name) != x_name:
            continue
        return ApplyExpr("Eq", (x, ConstExpr(f"0x{q * m + r:x}")))
    return None


MOD_DIV_PIN = Rule(
    name="ModDivPin",
    fn=_rewrite_mod_div_pin,
    description=(
        "Eq(Mod(X, m), r) && Eq(Div(X, m), q) -> Eq(X, q*m + r): a "
        "full Euclidean residue/quotient pair pins the value (the "
        "i128::MIN guard shape, L == 0 && H == 2^63 -> X == 2^127). "
        "The quotient side also matches its R4-unfolded window form "
        "a <= X < a + m with m | a."
    ),
)
