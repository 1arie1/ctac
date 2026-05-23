"""Recognize the post-u128-lift Knuth ceil-div idiom and lift it to
``IntCeilDiv(V, W)``.

After the u128 lift family (carry-add, decrement, chunk-merge)
reduces the SBF chunked ceil-multiplication to the bare three-line
form::

    H0 = narrow(IntAdd(V, W))       ; bv256 (V + W); narrow is no-op
                                    ; when V + W fits bv256
    H2 = IntSub(H0_ref, 1)
    I  = IntDiv(H2_ref, W_ref)      ; floor((V + W - 1) / W)

the result ``I`` is the textbook ceil-div identity
``floor((V + W - 1) / W) == ceil(V / W)`` (for ``V >= 0, W >= 1``).

Rewrite (fires at the ``IntDiv(H2, W)`` host)::

    I = IntCeilDiv(V, W)

The three intermediates (H0, H2, possibly the chained SymRefs)
become dead via DCE once no live cmd references them.

Soundness: write ``V = qW + r`` with ``0 <= r < W``. Then
``V + W - 1 = (q + 1)W + (r - 1)``.

  * ``r == 0``: ``V + W - 1 = qW + (W - 1)``; floor = ``q``,
    and ``ceil(V/W) = q``. Equal.
  * ``r >= 1``: ``V + W - 1 = (q + 1)W + (r - 1)`` with
    ``0 <= r - 1 < W``; floor = ``q + 1``, and
    ``ceil(V/W) = q + 1``. Equal.

Preconditions:

  * ``W`` is positive (range ``[1, ...]``) — otherwise the
    floor-ceil identity doesn't hold.
  * ``narrow(IntAdd(V, W))`` is provably no-wrap (interval
    inference shows ``V + W <= 2^256 - 1``) — otherwise H0 is
    not the int sum and the identity fails.

rw-eq's per-cmd CHK on the rewritten ``I``'s def verifies the
equivalence under the program's actual assume context.
"""

from __future__ import annotations

from ctac.ast.nodes import (
    ApplyExpr,
    AssignExpCmd,
    ConstExpr,
    SymbolRef,
    TacExpr,
)
from ctac.rewrite.context import RewriteCtx, _is_safe_narrow_apply
from ctac.rewrite.framework import Rule
from ctac.rewrite.range_infer import infer_expr_range
from ctac.rewrite.rules.common import DIV_OPS, const_to_int

_BV256_MAX = (1 << 256) - 1


def _canonical_expr(expr: TacExpr) -> TacExpr:
    from ctac.analysis.symbols import canonical_symbol

    if isinstance(expr, SymbolRef):
        return SymbolRef(canonical_symbol(expr.name))
    if isinstance(expr, ApplyExpr):
        return ApplyExpr(expr.op, tuple(_canonical_expr(a) for a in expr.args))
    return expr


def _eq_modulo_meta(a: TacExpr, b: TacExpr) -> bool:
    return _canonical_expr(a) == _canonical_expr(b)


def _const_eq(expr: TacExpr, value: int) -> bool:
    return isinstance(expr, ConstExpr) and const_to_int(expr) == value


def _peel_narrow(expr: TacExpr) -> TacExpr:
    if _is_safe_narrow_apply(expr):
        assert isinstance(expr, ApplyExpr)
        return expr.args[1]
    return expr


def _rewrite_ceil_div_knuth(
    expr: TacExpr, ctx: RewriteCtx
) -> TacExpr | None:
    # Fire only at the top-level RHS of an AssignExpCmd.
    host = ctx.current_cmd()
    if not (ctx.at_cmd_top() and isinstance(host, AssignExpCmd)):
        return None
    if not (
        isinstance(expr, ApplyExpr)
        and expr.op in DIV_OPS
        and len(expr.args) == 2
    ):
        return None
    h2_ref, w_ref = expr.args

    # h2_ref -> IntSub(H0, 1)
    h2_def = ctx.lookthrough(h2_ref)
    if not (
        isinstance(h2_def, ApplyExpr)
        and h2_def.op == "IntSub"
        and len(h2_def.args) == 2
    ):
        return None
    h0_ref, one = h2_def.args
    if not _const_eq(one, 1):
        return None

    # H0 -> narrow(IntAdd(V, W)) (commutative). Peel narrow.
    h0_inner = _peel_narrow(ctx.lookthrough(h0_ref))
    if not (
        isinstance(h0_inner, ApplyExpr)
        and h0_inner.op == "IntAdd"
        and len(h0_inner.args) == 2
    ):
        return None
    add_l, add_r = h0_inner.args
    if _eq_modulo_meta(add_r, w_ref):
        v_ref = add_l
    elif _eq_modulo_meta(add_l, w_ref):
        v_ref = add_r
    else:
        return None

    # W must be positive (range [1, ...]).
    w_range = infer_expr_range(w_ref, ctx)
    if w_range is None or w_range[0] is None or w_range[0] < 1:
        return None

    # V + W must fit bv256 (narrow is no-op). Use a synthetic IntAdd
    # to query range inference; the rule's structural match guarantees
    # the actual H0 def is the same IntAdd.
    sum_range = infer_expr_range(h0_inner, ctx)
    if (
        sum_range is None
        or sum_range[0] is None
        or sum_range[0] < 0
        or sum_range[1] is None
        or sum_range[1] > _BV256_MAX
    ):
        return None

    return ApplyExpr("IntCeilDiv", (v_ref, w_ref))


CEIL_DIV_KNUTH = Rule(
    name="CeilDivKnuth",
    fn=_rewrite_ceil_div_knuth,
    description=(
        "IntDiv(IntSub(narrow(IntAdd(V, W)), 1), W) -> IntCeilDiv(V, W) "
        "under W >= 1 and narrow-no-wrap. Lifts the post-u128 "
        "(V + W - 1) / W idiom to the IntCeilDiv concept."
    ),
)

__all__ = ["CEIL_DIV_KNUTH"]
