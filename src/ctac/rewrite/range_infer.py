"""Best-effort integer interval inference over TAC expressions.

Minimal coverage for MVP rewrite rules (notably R1):
    - constants
    - symbols with a dominating range-assume
    - symbols declared with a bv-k sort (default bound ``[0, 2^k - 1]``),
      used as a fallback when no range-assume dominates
    - ``Apply(safe_math_narrow_bvN:bif, E)`` where ``E``'s range fits in ``bvN``
    - ``IntMul``/``Mul``/``IntAdd``/``Add`` of non-negative bounded arguments
    - ``Div``/``IntDiv`` by a positive constant (bounds scale by floor-div)
    - ``Mod``/``IntMod`` by a positive constant (always in ``[0, K - 1]``)
    - ``Sub``/``IntSub``: interval arithmetic on the operand ranges,
      refined by any relational assumes on the two operands
      (``ctx.diff_bounds``)
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
        # Intersect bounds from every source that has something to say:
        # the unique static definition's inferred range, dominating
        # assume-facts, and the declared sort. Each source narrows the
        # box; taking the tightest lo / hi across all of them is always
        # sound. This lets a one-sided assume (e.g. `Ge(X, 1)` giving
        # `lo=1, hi=None`) combine with the sort's upper bound
        # (`hi = 2^256 - 1`) to yield a usable interval.
        lo: int | None = None
        hi: int | None = None

        def _tighten(r: tuple[int | None, int | None] | None) -> None:
            nonlocal lo, hi
            if r is None:
                return
            r_lo, r_hi = r
            if r_lo is not None:
                lo = r_lo if lo is None else max(lo, r_lo)
            if r_hi is not None:
                hi = r_hi if hi is None else min(hi, r_hi)

        d = ctx.definition(expr.name)
        if d is not None:
            _tighten(infer_expr_range(d, ctx, ite_depth=ite_depth))
        _tighten(ctx.range(expr.name))
        width = _sort_width(ctx.symbol_sort(expr.name))
        if width is not None:
            _tighten((0, (1 << width) - 1))

        # Unsigned-by-convention fallback: if an upper bound exists but
        # no source produced a lower bound, assume lo=0. TAC values in
        # this pipeline are non-negative integers (bv values always,
        # int values almost always), so an upper-only assume like
        # `Le(R, K)` with K >= 0 is effectively a `[0, K]` range.
        if lo is None and hi is not None and hi >= 0:
            lo = 0

        if lo is not None and hi is not None:
            return (lo, hi)
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
    if expr.op == "IntCeilDiv" and len(expr.args) == 2:
        # ceil(a / b) for non-negative numerator and positive divisor:
        # bounded by the per-corner ceiling values. lo = ceil(a_lo/b_hi),
        # hi = ceil(a_hi/b_lo). For ``a_lo == 0`` the lo is 0. Don't try
        # to bound when ``a`` could be negative or ``b`` could be
        # zero/negative — the IntCeilDiv axiom leaves the value totally
        # free outside ``b > 0``, so any bound would be unsound.
        a = infer_expr_range(expr.args[0], ctx, ite_depth=ite_depth)
        b = infer_expr_range(expr.args[1], ctx, ite_depth=ite_depth)
        if a is not None and b is not None and a[0] >= 0 and b[0] > 0:
            a_lo, a_hi = a
            b_lo, b_hi = b
            lo = (a_lo + b_hi - 1) // b_hi if a_lo > 0 else 0
            hi = (a_hi + b_lo - 1) // b_lo
            return (lo, hi)
    if expr.op in {"Mod", "IntMod"} and len(expr.args) == 2:
        # `a mod K` for positive constant K is always in [0, K-1]. If
        # the dividend's range is already contained in [0, K), the mod
        # is an identity and we can return the dividend's own range —
        # this lets RANGE_FOLD and sibling rules see the tighter value.
        k = const_to_int(expr.args[1]) if isinstance(expr.args[1], ConstExpr) else None
        if k is not None and k > 0:
            a = infer_expr_range(expr.args[0], ctx, ite_depth=ite_depth)
            if a is not None:
                a_lo, a_hi = a
                if a_lo >= 0 and a_hi < k:
                    return (a_lo, a_hi)
            return (0, k - 1)
    if expr.op in {"Sub", "IntSub"} and len(expr.args) == 2:
        a = infer_expr_range(expr.args[0], ctx, ite_depth=ite_depth)
        b = infer_expr_range(expr.args[1], ctx, ite_depth=ite_depth)
        if a is None or b is None:
            return None
        lo = a[0] - b[1]
        hi = a[1] - b[0]
        # Refine via relational assumes on the two operands. Only
        # symbol-vs-symbol relations are tracked today, so this step
        # applies only when both operands are plain symbol references.
        if isinstance(expr.args[0], SymbolRef) and isinstance(expr.args[1], SymbolRef):
            diff = ctx.diff_bounds(expr.args[0].name, expr.args[1].name)
            if diff is not None:
                d_lo, d_hi = diff
                if d_lo is not None:
                    lo = max(lo, d_lo)
                if d_hi is not None:
                    hi = min(hi, d_hi)
        return (lo, hi)
    if expr.op == "Ite" and len(expr.args) == 3:
        if ite_depth >= ctx.ite_max_depth:
            return None
        next_depth = ite_depth + 1
        a = infer_expr_range(expr.args[1], ctx, ite_depth=next_depth)
        b = infer_expr_range(expr.args[2], ctx, ite_depth=next_depth)
        if a and b:
            return (min(a[0], b[0]), max(a[1], b[1]))
    return None
