"""``IntMulDiv(A, B, K)`` -> ``Div(V, M*K)`` when the wider product
``V == A * M * B`` is already a static register in the program.

Motivating shape (the SBF-lowered u64 × u46 → u128 multiplication):

    R96 = narrow(IntMul(K_a, R30))          ; K_a a positive const
    R93 = narrow(IntMul(M, R90))             ; M = 2^14, positive const
    R99 = narrow(IntMul(R96, R93))           ; wide product
    R100 = Mod(R99, 2^64)                    ; low 64 chunk
    I102 = IntMulDiv(R96, R90, K)            ; "high" chunk, K = 2^50

The "muldiv-style" high chunk ``IntMulDiv(R96, R90, K)`` looks
unrelated to R99 syntactically, but numerically:

    IntMulDiv(R96, R90, K) = (R96 * R90) / K
    R99 = R96 * (M * R90) = M * (R96 * R90)        (narrows are identity)
    R99 / (M * K) = (R96 * R90) / K = IntMulDiv(R96, R90, K)

So I102 equals ``Div(R99, M*K)`` (= 2^64 in our case). Rewriting
the muldiv into that form puts the high chunk in the canonical
``Div(T, M*K)`` shape that ``CHUNK_MERGE`` consumes; the
``(I102 * 2^64 + R100) + R28`` recombination then collapses to
``R99 + R28``, eliminating the chunked encoding entirely.

Soundness: the rewrite is purely arithmetic. The preconditions
(narrows are identity) follow from V's bv-sort + the operand
ranges that the upstream lift / multiplication produced. rw-eq's
rule-2 CHK is ``Eq(IntMulDiv(A, B, K), Div(V, M*K))``; z3 closes
it from V's def + range bounds + the const-arith for M and K.

Gates:

1. ``K`` must be a positive constant.
2. There exists a static var ``V`` in the program with def
   ``narrow(IntMul(A_or_A_alias, W))``.
3. ``W`` (under SymRef lookthrough + narrow peeling) is
   ``IntMul(M_const, B_or_B_alias)`` for a positive const M.
4. ``A_or_A_alias`` matches A, ``B_or_B_alias`` matches B,
   compared via ``eq_modulo_meta`` (so DSA version suffixes don't
   defeat the match).

The result divisor is the constant ``M * K``. We emit it as a
bv-style ConstExpr so the rewritten ``Div`` plugs into the
existing chunk-merge pattern (which expects ``Div(T, K_bv)``).
"""

from __future__ import annotations

from ctac.ast.nodes import ApplyExpr, ConstExpr, SymbolRef, TacExpr
from ctac.rewrite.context import RewriteCtx, _is_safe_narrow_apply
from ctac.rewrite.framework import Rule
from ctac.rewrite.rules.common import const_to_int, eq_modulo_meta


def _bv_const(value: int) -> ConstExpr:
    return ConstExpr(f"{hex(value)}")


def _match_int_mul_with_const(
    expr: TacExpr, ctx: RewriteCtx, other: TacExpr
) -> int | None:
    """If ``expr`` is ``IntMul(M_const, other)`` or
    ``IntMul(other, M_const)`` after lookthrough + narrow-peel,
    return ``M_const``."""
    e = ctx.lookthrough(expr)
    if not (isinstance(e, ApplyExpr) and e.op == "IntMul" and len(e.args) == 2):
        return None
    wa, wb = e.args
    wa_v = const_to_int(wa)
    wb_v = const_to_int(wb)
    if wa_v is not None and eq_modulo_meta(wb, other):
        return wa_v if wa_v > 0 else None
    if wb_v is not None and eq_modulo_meta(wa, other):
        return wb_v if wb_v > 0 else None
    return None


def _rewrite_muldiv_to_full_product_div(
    expr: TacExpr, ctx: RewriteCtx
) -> TacExpr | None:
    """``IntMulDiv(A, B, K)`` -> ``Div(V, M*K)`` when V = narrow(IntMul(A, W))
    is a static def and W ≡ M * B."""
    if not (
        isinstance(expr, ApplyExpr)
        and expr.op == "IntMulDiv"
        and len(expr.args) == 3
    ):
        return None
    a_expr, b_expr, k_expr = expr.args
    k_v = const_to_int(k_expr)
    if k_v is None or k_v <= 0:
        return None

    for v_name, v_def in ctx.static_defs.items():
        if not _is_safe_narrow_apply(v_def):
            continue
        assert isinstance(v_def, ApplyExpr)
        # The narrow's inner is often an int-typed intermediate
        # SymRef (``narrow(I98)`` with ``I98 = IntMul(...)``). Use
        # lookthrough to resolve through the chain.
        inner = ctx.lookthrough(v_def.args[1])
        if not (
            isinstance(inner, ApplyExpr)
            and inner.op == "IntMul"
            and len(inner.args) == 2
        ):
            continue
        a_side, w_side = inner.args
        # Find which operand of the IntMul is A.
        if eq_modulo_meta(a_side, a_expr):
            w_candidate = w_side
        elif eq_modulo_meta(w_side, a_expr):
            w_candidate = a_side
        else:
            continue
        m = _match_int_mul_with_const(w_candidate, ctx, b_expr)
        if m is None:
            continue
        return ApplyExpr(
            "Div", (SymbolRef(v_name), _bv_const(m * k_v))
        )
    return None


MULDIV_TO_FULL_PRODUCT_DIV = Rule(
    name="MulDivToFullProductDiv",
    fn=_rewrite_muldiv_to_full_product_div,
    description=(
        "IntMulDiv(A, B, K) -> Div(V, M*K) when V = narrow(IntMul(A, W)) "
        "is a static def with W ≡ M*B (M a positive const). Recognizes "
        "the high-chunk of a u64×u46→u128 product as the canonical "
        "Div(V, 2^N) form so chunk-merge can collapse the "
        "(I102 * 2^64 + R100) recombination back to V."
    ),
)

__all__ = ["MULDIV_TO_FULL_PRODUCT_DIV"]
