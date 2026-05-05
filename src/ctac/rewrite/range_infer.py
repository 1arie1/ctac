"""Best-effort integer interval inference over TAC expressions.

The per-op transfer functions live in
``ctac.analysis.abs_int.expr_eval`` and are shared with the abs_int
``IntervalDomain``. This module's contribution is the *symbol-level
lookup* the shared evaluator calls back into:

- the unique static def's RHS (or, for DSA-dynamic vars, the convex
  hull over every def's RHS);
- dominating range-assume facts (``ctx.range``);
- declared sort default (``ctx.symbol_sort``).

Plus the ``Sub``/``IntSub`` relational refinement (``ctx.diff_bounds``)
and the Ite-recursion cap (``ctx.ite_max_depth``) which are passed
through to the shared evaluator.

Wrap-detection callers (``ADD_BV_TO_INT`` and friends) need the
*unwrapped* (pre-bv-clamp) interval to decide whether wrap occurred.
They use :func:`infer_unwrapped_op` directly, which evaluates operands
through the shared evaluator and applies the binop in the unbounded
Int domain. Every other caller gets the bv-domain-safe interval from
:func:`infer_expr_range` by default.
"""

from __future__ import annotations

from ctac.analysis.abs_int import interval_ops as iv
from ctac.analysis.abs_int.expr_eval import (
    _sort_width,
    eval_expr_iv,
    unwrapped_int_op,
)
from ctac.analysis.abs_int.interval_ops import Interval
from ctac.ast.nodes import TacExpr
from ctac.rewrite.context import RewriteCtx


def infer_expr_range(
    expr: TacExpr, ctx: RewriteCtx, *, ite_depth: int = 0
) -> tuple[int, int] | None:
    """Returns ``(lo, hi)`` only when both bounds are concrete, else
    ``None``."""
    return iv.to_pair_strict(_infer_iv(expr, ctx, ite_depth=ite_depth))


def _infer_iv(
    expr: TacExpr, ctx: RewriteCtx, *, ite_depth: int = 0
) -> Interval:
    """Evaluate ``expr`` to an interval, delegating per-op math to the
    shared evaluator and feeding it the rewriter's symbol-level
    lookup."""
    return eval_expr_iv(
        expr,
        lookup=lambda name: _infer_symbol(name, ctx, ite_depth=ite_depth),
        sort_of=ctx.symbol_sort,
        diff_bounds=ctx.diff_bounds,
        ite_max_depth=ctx.ite_max_depth,
        _ite_depth=ite_depth,
    )


def infer_unwrapped_op(
    op: str, args: list[TacExpr], ctx: RewriteCtx, *, ite_depth: int = 0
) -> tuple[int, int] | None:
    """Pre-clamp interval for a bv binop, used by wrap-detection rules.

    ``infer_expr_range(Add(a, b))`` returns the bv-clamped interval
    (the value the bv op actually produces under wrap-mod-2^256).
    Wrap-detection rules need the *unwrapped* sum to decide whether the
    bv result equals the int result (i.e., whether wrap occurred). This
    helper evaluates ``a`` and ``b`` through the shared evaluator
    (operand sub-expressions stay bv-clamped) but applies the binop
    in the Int domain, returning the unwrapped result as a tuple.
    """
    interval = unwrapped_int_op(
        op,
        args,
        lookup=lambda name: _infer_symbol(name, ctx, ite_depth=ite_depth),
        sort_of=ctx.symbol_sort,
        diff_bounds=ctx.diff_bounds,
        ite_max_depth=ctx.ite_max_depth,
    )
    return iv.to_pair_strict(interval)


def _infer_symbol(name: str, ctx: RewriteCtx, *, ite_depth: int) -> Interval:
    # Intersect bounds from every source: the def-set's RHS range, the
    # dominating assume facts, and the declared sort. Each source
    # narrows; meet across all of them is sound.
    #
    # Def-set: for DSA-static vars this is a single RHS (the unique
    # def). For DSA-dynamic vars it's the convex-hull join over every
    # def's RHS — sound because at any use the value reaches from one
    # of the defs, so the result is bounded by their union. If any def
    # is non-:class:`AssignExpCmd` (havoc) or otherwise un-walkable, the
    # def-set is treated as TOP.
    interval = iv.TOP
    rhs_set = ctx.def_rhs_expressions(name)
    if rhs_set is not None:
        joined: Interval | None = None
        for rhs in rhs_set:
            v = _infer_iv(rhs, ctx, ite_depth=ite_depth)
            joined = v if joined is None else iv.join(joined, v)
        if joined is not None:
            interval = iv.meet(interval, joined)
    interval = iv.meet(interval, iv.from_pair(ctx.range(name)))
    width = _sort_width(ctx.symbol_sort(name))
    if width is not None:
        # Bv-typed symbols are non-negative by construction; the
        # bv-width interval ``[0, 2^width-1]`` provides the lower
        # bound. The previous "if hi is known and >= 0, assume lo=0"
        # fallback for sort-less symbols was unsound for signed ints
        # (``IntSub`` results, ``unwrap_twos_complement`` outputs) and
        # has been removed. Callers who need a non-negative lower bound
        # for an int-typed symbol must derive it explicitly (e.g. via
        # a dominating ``Ge(X, 0)`` assume).
        interval = iv.meet(interval, iv.bv_width_iv(width))
    return interval
