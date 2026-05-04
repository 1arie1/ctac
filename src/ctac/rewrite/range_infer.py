"""Best-effort integer interval inference over TAC expressions.

Coverage:
    - constants
    - symbols with a dominating range-assume
    - symbols declared with a bv-k sort (default ``[0, 2^k - 1]``,
      used when no range-assume dominates)
    - ``Apply(safe_math_narrow_bvN:bif, E)`` where ``E``'s range fits
    - ``IntMul``/``Mul``/``IntAdd``/``Add`` of non-negative bounded args
    - ``Div``/``IntDiv`` by a positive constant (floor-div scaling)
    - ``Mod``/``IntMod`` by a positive constant (always ``[0, K - 1]``,
      identity when the dividend is provably in ``[0, K)``)
    - ``Sub``/``IntSub`` with relational refinement (``ctx.diff_bounds``)
    - ``Ite(c, t, e)`` (union of branch ranges, capped at
      ``ctx.ite_max_depth`` to avoid blowup on deep chains)
    - symbols whose static definition is one of the above

The per-op interval arithmetic lives in
``ctac.analysis.abs_int.interval_ops`` so the abs_int interval domain
shares the same math.
"""

from __future__ import annotations

from ctac.analysis.abs_int import interval_ops as iv
from ctac.analysis.abs_int.interval_ops import Interval
from ctac.ast.nodes import ApplyExpr, ConstExpr, SymbolRef, TacExpr
from ctac.rewrite.context import RewriteCtx
from ctac.rewrite.rules.common import const_to_int

_NARROW_WIDTHS = {
    "safe_math_narrow_bv64": 64,
    "safe_math_narrow_bv128": 128,
    "safe_math_narrow_bv256": 256,
}

_BV_SORT_PREFIX = "bv"

# Note on bv256 semantics: TAC ``Add`` / ``Sub`` / ``Mul`` are wrap-mod-2^256
# but the unwrapped range computed here is the *upper bound on the
# pre-wrap result*. Callers that need a wrapped (in-domain) value (e.g.
# ``RangeFold``) apply ``iv.bv_clamp`` themselves; callers reasoning about
# whether wrap occurs (e.g. ``ADD_BV_TO_INT``) need the unwrapped form
# directly.


def _narrow_width(fn_name: str) -> int | None:
    core = fn_name[:-4] if fn_name.endswith(":bif") else fn_name
    for prefix, width in _NARROW_WIDTHS.items():
        if core.startswith(prefix):
            return width
    return None


def _sort_width(sort: str | None) -> int | None:
    if sort is None or not sort.startswith(_BV_SORT_PREFIX):
        return None
    rest = sort[len(_BV_SORT_PREFIX):]
    if not rest.isdigit():
        return None
    return int(rest)


def infer_expr_range(
    expr: TacExpr, ctx: RewriteCtx, *, ite_depth: int = 0
) -> tuple[int, int] | None:
    """Returns ``(lo, hi)`` only when both bounds are concrete, else
    ``None``."""
    return iv.to_pair_strict(_infer_iv(expr, ctx, ite_depth=ite_depth))


def _infer_iv(
    expr: TacExpr, ctx: RewriteCtx, *, ite_depth: int = 0
) -> Interval:
    if isinstance(expr, ConstExpr):
        c = const_to_int(expr)
        if c is None:
            return iv.TOP
        return iv.point(c)
    if isinstance(expr, SymbolRef):
        return _infer_symbol(expr.name, ctx, ite_depth=ite_depth)
    if isinstance(expr, ApplyExpr):
        return _infer_apply(expr, ctx, ite_depth=ite_depth)
    return iv.TOP


def _infer_symbol(name: str, ctx: RewriteCtx, *, ite_depth: int) -> Interval:
    # Intersect bounds from every source: the unique static def, the
    # dominating assume facts, and the declared sort. Each source
    # narrows; meet across all of them is sound.
    interval = iv.TOP
    d = ctx.definition(name)
    if d is not None:
        interval = iv.meet(interval, _infer_iv(d, ctx, ite_depth=ite_depth))
    interval = iv.meet(interval, iv.from_pair(ctx.range(name)))
    width = _sort_width(ctx.symbol_sort(name))
    if width is not None:
        interval = iv.meet(interval, iv.bv_width_iv(width))
    # Unsigned-by-convention fallback: if an upper bound exists but no
    # source produced a lower bound, assume lo=0. TAC values in this
    # pipeline are non-negative integers (bv values always, int values
    # almost always), so an upper-only assume like ``Le(R, K)`` with
    # K >= 0 is effectively a ``[0, K]`` range. Applied here so every
    # symbol lookup matches the historical tuple-API behavior.
    if interval.lo is None and interval.hi is not None and interval.hi >= 0:
        interval = Interval(0, interval.hi)
    return interval


def _infer_apply(
    expr: ApplyExpr, ctx: RewriteCtx, *, ite_depth: int
) -> Interval:
    if expr.op == "Apply" and expr.args and isinstance(expr.args[0], SymbolRef):
        width = _narrow_width(expr.args[0].name)
        if width is not None and len(expr.args) == 2:
            inner = _infer_iv(expr.args[1], ctx, ite_depth=ite_depth)
            clamped = iv.narrow_clamp(inner, width)
            if clamped is not None:
                return clamped
        return iv.TOP
    if expr.op in {"Mul", "IntMul"} and len(expr.args) == 2:
        a = _infer_iv(expr.args[0], ctx, ite_depth=ite_depth)
        b = _infer_iv(expr.args[1], ctx, ite_depth=ite_depth)
        result = iv.mul_nonneg(a, b)
        return result if result is not None else iv.TOP
    if expr.op in {"Add", "IntAdd"} and len(expr.args) == 2:
        a = _infer_iv(expr.args[0], ctx, ite_depth=ite_depth)
        b = _infer_iv(expr.args[1], ctx, ite_depth=ite_depth)
        return iv.add(a, b)
    if expr.op in {"Div", "IntDiv"} and len(expr.args) == 2:
        # Only positive-constant divisors are bounded; non-constant
        # divisors could approach zero and blow the bound up.
        k = const_to_int(expr.args[1]) if isinstance(expr.args[1], ConstExpr) else None
        if k is not None and k > 0:
            a = _infer_iv(expr.args[0], ctx, ite_depth=ite_depth)
            result = iv.floor_div_by_pos_const(a, k)
            if result is not None:
                return result
        return iv.TOP
    if expr.op == "IntCeilDiv" and len(expr.args) == 2:
        # The IntCeilDiv axiom leaves the value totally free outside
        # ``b > 0``, so any bound for negative ``a`` or non-positive ``b``
        # would be unsound.
        a = _infer_iv(expr.args[0], ctx, ite_depth=ite_depth)
        b = _infer_iv(expr.args[1], ctx, ite_depth=ite_depth)
        result = iv.ceil_div_nonneg(a, b)
        return result if result is not None else iv.TOP
    if expr.op in {"Mod", "IntMod"} and len(expr.args) == 2:
        k = const_to_int(expr.args[1]) if isinstance(expr.args[1], ConstExpr) else None
        if k is not None and k > 0:
            a = _infer_iv(expr.args[0], ctx, ite_depth=ite_depth)
            result = iv.mod_by_pos_const(a, k)
            if result is not None:
                return result
        return iv.TOP
    if expr.op in {"Sub", "IntSub"} and len(expr.args) == 2:
        a = _infer_iv(expr.args[0], ctx, ite_depth=ite_depth)
        b = _infer_iv(expr.args[1], ctx, ite_depth=ite_depth)
        result = iv.sub(a, b)
        # Refine via relational assumes on the two operands. Only
        # symbol-vs-symbol relations are tracked today, so this step
        # applies only when both operands are plain symbol references.
        if isinstance(expr.args[0], SymbolRef) and isinstance(expr.args[1], SymbolRef):
            diff = ctx.diff_bounds(expr.args[0].name, expr.args[1].name)
            if diff is not None:
                result = iv.meet(result, iv.from_pair(diff))
        return result
    if expr.op == "Ite" and len(expr.args) == 3:
        if ite_depth >= ctx.ite_max_depth:
            return iv.TOP
        next_depth = ite_depth + 1
        a = _infer_iv(expr.args[1], ctx, ite_depth=next_depth)
        b = _infer_iv(expr.args[2], ctx, ite_depth=next_depth)
        return iv.join(a, b)
    return iv.TOP
