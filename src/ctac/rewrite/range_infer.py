"""Best-effort integer interval inference over TAC expressions.

Minimal coverage for MVP rewrite rules (notably R1):
    - constants
    - symbols with a dominating range-assume
    - symbols declared with a bv-k sort (default bound ``[0, 2^k - 1]``),
      used as a fallback when no range-assume dominates
    - ``Apply(safe_math_narrow_bvN:bif, E)`` where ``E``'s range fits in ``bvN``
    - ``IntMul``/``Mul``/``IntAdd``/``Add`` of non-negative bounded arguments
    - ``Div``/``IntDiv`` by a positive constant (bounds scale by floor-div)
    - ``Ite(c, t, e)``: union of branch ranges, capped at ``ctx.ite_max_depth``
      nested levels to avoid exponential blowup on deep Ite chains
    - symbols whose static definition is one of the above
"""

from __future__ import annotations

from ctac.ast.nodes import ApplyExpr, ConstExpr, SymbolRef, TacExpr
from ctac.rewrite.context import RewriteCtx
from ctac.rewrite.rules.common import const_to_int

_NARROW_WIDTHS = {
    "safe_math_narrow_bv64": 64,
    "safe_math_narrow_bv128": 128,
    "safe_math_narrow_bv256": 256,
}

_BV_SORT_PREFIX = "bv"


def _narrow_width(fn_name: str) -> int | None:
    core = fn_name[:-4] if fn_name.endswith(":bif") else fn_name
    for prefix, width in _NARROW_WIDTHS.items():
        if core.startswith(prefix):
            return width
    return None


def _sort_width(sort: str | None) -> int | None:
    # Parse ``"bv256"`` / ``"bv64"`` / ... into the width in bits.
    if sort is None or not sort.startswith(_BV_SORT_PREFIX):
        return None
    rest = sort[len(_BV_SORT_PREFIX):]
    if not rest.isdigit():
        return None
    return int(rest)


def infer_expr_range(
    expr: TacExpr, ctx: RewriteCtx, *, ite_depth: int = 0
) -> tuple[int, int] | None:
    if isinstance(expr, ConstExpr):
        c = const_to_int(expr)
        if c is None:
            return None
        return (c, c)
    if isinstance(expr, SymbolRef):
        r = ctx.range(expr.name)
        if r is not None:
            lo, hi = r
            if hi is not None and lo is None and hi >= 0:
                # Havoc'd bv vars default to lo=0; callers treat ints similarly.
                lo = 0
            if lo is not None and hi is not None:
                return (lo, hi)
        d = ctx.definition(expr.name)
        if d is not None:
            return infer_expr_range(d, ctx, ite_depth=ite_depth)
        # Fallback: symbols declared as ``bvk`` are in ``[0, 2^k - 1]`` by
        # sort. Applies only when no tighter bound came from an assume or
        # a static definition.
        width = _sort_width(ctx.symbol_sort(expr.name))
        if width is not None:
            return (0, (1 << width) - 1)
        return None
    if isinstance(expr, ApplyExpr):
        return _infer_apply(expr, ctx, ite_depth=ite_depth)
    return None


def _infer_apply(
    expr: ApplyExpr, ctx: RewriteCtx, *, ite_depth: int
) -> tuple[int, int] | None:
    if expr.op == "Apply" and expr.args and isinstance(expr.args[0], SymbolRef):
        width = _narrow_width(expr.args[0].name)
        if width is not None and len(expr.args) == 2:
            inner = infer_expr_range(expr.args[1], ctx, ite_depth=ite_depth)
            if inner is not None and inner[0] >= 0 and inner[1] < (1 << width):
                return inner
        return None
    if expr.op in {"Mul", "IntMul"} and len(expr.args) == 2:
        a = infer_expr_range(expr.args[0], ctx, ite_depth=ite_depth)
        b = infer_expr_range(expr.args[1], ctx, ite_depth=ite_depth)
        if a and b and a[0] >= 0 and b[0] >= 0:
            return (a[0] * b[0], a[1] * b[1])
    if expr.op in {"Add", "IntAdd"} and len(expr.args) == 2:
        a = infer_expr_range(expr.args[0], ctx, ite_depth=ite_depth)
        b = infer_expr_range(expr.args[1], ctx, ite_depth=ite_depth)
        if a and b:
            return (a[0] + b[0], a[1] + b[1])
    if expr.op in {"Div", "IntDiv"} and len(expr.args) == 2:
        # floor(a / K) for positive constant K scales the numerator's range
        # by K. Unlike Mul/Add above we don't bound non-constant divisors —
        # the denominator could approach 0 and blow the upper bound up.
        k = const_to_int(expr.args[1]) if isinstance(expr.args[1], ConstExpr) else None
        if k is not None and k > 0:
            a = infer_expr_range(expr.args[0], ctx, ite_depth=ite_depth)
            if a and a[0] >= 0:
                return (a[0] // k, a[1] // k)
    if expr.op == "Ite" and len(expr.args) == 3:
        if ite_depth >= ctx.ite_max_depth:
            return None
        next_depth = ite_depth + 1
        a = infer_expr_range(expr.args[1], ctx, ite_depth=next_depth)
        b = infer_expr_range(expr.args[2], ctx, ite_depth=next_depth)
        if a and b:
            return (min(a[0], b[0]), max(a[1], b[1]))
    return None
