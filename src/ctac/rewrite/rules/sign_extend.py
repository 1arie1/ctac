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
