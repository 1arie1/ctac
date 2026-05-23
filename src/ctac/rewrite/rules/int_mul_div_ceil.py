"""Recognize ``IntCeilDiv(narrow(IntMul(A, B)), W)`` and lift it to
``IntMulDivCeil(A, B, W)``.

After CeilDivKnuth lifts the post-u128 ``(V + W - 1) / W`` chain to
``IntCeilDiv(V, W)``, the typical residue is::

    I70 = IntMul(A, B)            ; int-domain product
    R71 = narrow(I70)             ; bv256 narrow; no-op when A*B fits
    I94 = IntCeilDiv(R71, W)

The result ``I94`` equals ``ceil((A*B) / W)`` for ``A, B >= 0,
W >= 1``, provided ``narrow(A*B) == A*B`` (the product fits bv256).

Rewrite (at the ``IntCeilDiv(R71, W)`` host)::

    I94 = IntMulDivCeil(A, B, W)

The two intermediates (I70, R71) become dead via DCE if no other
consumer references them. Folding to the concept lets the SMT
layer's ``int_mul_div_ceil_axiom`` reason directly about the
``ceil(A*B/W)`` value without the narrow detour, mirroring the
``IntCeilDiv`` over `IntDiv + Add + Sub` chain collapse.

Soundness:

  * ``W`` is positive (range ``[1, ...]``) — otherwise the floor-ceil
    identity doesn't hold.
  * ``IntMul(A, B)`` is provably ``<= 2^256-1`` — so the narrow is
    identity in int domain and ``ceil(narrow(A*B)/W) == ceil(A*B/W)``.

rw-eq's per-cmd CHK on the rewritten host verifies the equivalence
under the program's actual assume context.
"""

from __future__ import annotations

from ctac.ast.nodes import (
    ApplyExpr,
    AssignExpCmd,
    SymbolRef,
    TacExpr,
)
from ctac.rewrite.context import RewriteCtx, _is_safe_narrow_apply
from ctac.rewrite.framework import Rule
from ctac.rewrite.range_infer import infer_expr_range
from ctac.rewrite.rules.common import MUL_OPS

_BV256_MAX = (1 << 256) - 1


def _canonical_expr(expr: TacExpr) -> TacExpr:
    from ctac.analysis.symbols import canonical_symbol

    if isinstance(expr, SymbolRef):
        return SymbolRef(canonical_symbol(expr.name))
    if isinstance(expr, ApplyExpr):
        return ApplyExpr(expr.op, tuple(_canonical_expr(a) for a in expr.args))
    return expr


def _peel_narrow(expr: TacExpr) -> TacExpr:
    if _is_safe_narrow_apply(expr):
        assert isinstance(expr, ApplyExpr)
        return expr.args[1]
    return expr


def _rewrite_int_mul_div_ceil(
    expr: TacExpr, ctx: RewriteCtx
) -> TacExpr | None:
    # Fire only at the top-level RHS of an AssignExpCmd.
    host = ctx.current_cmd()
    if not (ctx.at_cmd_top() and isinstance(host, AssignExpCmd)):
        return None
    if not (
        isinstance(expr, ApplyExpr)
        and expr.op == "IntCeilDiv"
        and len(expr.args) == 2
    ):
        return None
    r_ref, w_ref = expr.args

    # R must look through to ``narrow(IntMul(A, B))`` (or any equivalent
    # narrow-wrapped Mul). Lookthrough peels SymRef -> def; ``_peel_narrow``
    # strips the safe_math_narrow Apply.
    mul_inner = _peel_narrow(ctx.lookthrough(r_ref))
    if not (
        isinstance(mul_inner, ApplyExpr)
        and mul_inner.op in MUL_OPS
        and len(mul_inner.args) == 2
    ):
        return None
    a_ref, b_ref = mul_inner.args

    # W must be positive.
    w_range = infer_expr_range(w_ref, ctx)
    if w_range is None or w_range[0] is None or w_range[0] < 1:
        return None

    # The product A*B must fit bv256 (narrow is a no-op).
    prod_range = infer_expr_range(mul_inner, ctx)
    if (
        prod_range is None
        or prod_range[0] is None
        or prod_range[0] < 0
        or prod_range[1] is None
        or prod_range[1] > _BV256_MAX
    ):
        return None

    return ApplyExpr("IntMulDivCeil", (a_ref, b_ref, w_ref))


INT_MUL_DIV_CEIL = Rule(
    name="IntMulDivCeil",
    fn=_rewrite_int_mul_div_ceil,
    description=(
        "IntCeilDiv(narrow(IntMul(A, B)), W) -> IntMulDivCeil(A, B, W) "
        "under W >= 1 and A*B fits bv256 (narrow no-op). Folds the "
        "narrow-wrapped product + ceil-div chain to the IntMulDivCeil "
        "concept."
    ),
)

__all__ = ["INT_MUL_DIV_CEIL"]
