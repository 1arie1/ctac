"""Shared TacExpr → Interval evaluator.

Used by both:

- ``ctac.analysis.abs_int.domains.interval.IntervalDomain``
  (transfer function on per-block dataflow state).
- ``ctac.rewrite.range_infer`` (best-effort range query for rule
  predicates).

Both callers plug in their own ``SymbolRef`` lookup; everything else
(constants, arithmetic, narrow, Ite, etc.) is shared. The key
invariant: bv-domain ops (``Add`` / ``Sub`` / ``Mul`` / ``Div`` /
``Mod``) get ``bv_clamp`` applied; Int-domain ops (``IntAdd`` / ...)
return the unwrapped interval. ``result_width`` is the width hint
when the surrounding context is a bv assignment; ``None`` means use
operand-sort inference.

The contract: callers asking ``eval_expr_iv(Add(...))`` get a
bv-domain-safe interval. Callers that need the un-wrapped pre-clamp
result (rare; e.g. wrap-detection rules) call
:func:`unwrapped_int_op` directly.
"""

from __future__ import annotations

from collections.abc import Callable

from ctac.analysis.abs_int import interval_ops as iv
from ctac.analysis.abs_int.interval_ops import Interval
from ctac.ast.nodes import ApplyExpr, ConstExpr, SymbolRef, TacExpr
from ctac.ast.range_constraints import const_expr_to_int as const_to_int

LookupFn = Callable[[str], Interval]
SortFn = Callable[[str], "str | None"]
DiffBoundsFn = Callable[[str, str], "tuple[int | None, int | None] | None"]


_BV_SORT_PREFIX = "bv"
_NARROW_WIDTHS = {
    "safe_math_narrow_bv64": 64,
    "safe_math_narrow_bv128": 128,
    "safe_math_narrow_bv256": 256,
}
# ``Apply(wrap_twos_complement_<W>:bif, X)`` is the bv-W image of a
# signed int X: ``X`` for non-negative ``X``, ``X + 2^W`` for negative
# ``X``. Only the 256-bit form exists in the current TAC frontend.
_WRAP_WIDTHS = {
    "wrap_twos_complement_256": 256,
}

_REL_OPS = frozenset(
    {"Eq", "Ne", "Lt", "Le", "Gt", "Ge", "Slt", "Sle", "Sgt", "Sge"}
)
_BOOL_BIN_OPS = frozenset({"LAnd", "LOr"})
_BOOL_UN_OPS = frozenset({"LNot"})


def _sort_width(sort: "str | None") -> "int | None":
    if sort is None or not sort.startswith(_BV_SORT_PREFIX):
        return None
    rest = sort[len(_BV_SORT_PREFIX):]
    if not rest.isdigit():
        return None
    return int(rest)


def _narrow_width(fn_name: str) -> "int | None":
    core = fn_name[:-4] if fn_name.endswith(":bif") else fn_name
    for prefix, width in _NARROW_WIDTHS.items():
        if core.startswith(prefix):
            return width
    return None


def _match_signed_wrap(
    expr: TacExpr, expected_width: int
) -> "TacExpr | None":
    """If ``expr`` is ``Apply(wrap_twos_complement_<expected_width>:bif, X)``,
    return ``X`` (the underlying signed-int operand). Otherwise ``None``."""
    if not (
        isinstance(expr, ApplyExpr)
        and expr.op == "Apply"
        and len(expr.args) == 2
        and isinstance(expr.args[0], SymbolRef)
    ):
        return None
    callee = expr.args[0].name
    core = callee[:-4] if callee.endswith(":bif") else callee
    width = _WRAP_WIDTHS.get(core)
    if width is None or width != expected_width:
        return None
    return expr.args[1]


def _infer_bv_width_from_operand_sorts(
    args: "list[TacExpr]", sort_of: SortFn
) -> "int | None":
    """Width fallback for raw bv ops without a surrounding
    ``result_width``: walk the operand subtrees, collecting bv-N sorts
    from every reachable ``SymbolRef``. If they agree on a single N,
    return N. Otherwise return ``None`` (and the bv op falls back to
    TOP). The walk is needed for nested expressions like
    ``Add(Add(R_bv256, C1), C2)`` where no top-level operand is a
    SymbolRef but the nested ``R_bv256`` pins the width."""
    widths: set[int] = set()

    def visit(e: TacExpr) -> None:
        if isinstance(e, SymbolRef):
            w = _sort_width(sort_of(e.name))
            if w is not None:
                widths.add(w)
            return
        if isinstance(e, ApplyExpr):
            for sub in e.args:
                visit(sub)

    for a in args:
        visit(a)
    if len(widths) == 1:
        return next(iter(widths))
    return None


def eval_expr_iv(
    expr: TacExpr,
    *,
    lookup: LookupFn,
    sort_of: SortFn,
    result_width: "int | None" = None,
    diff_bounds: "DiffBoundsFn | None" = None,
    ite_max_depth: "int | None" = None,
    _ite_depth: int = 0,
) -> Interval:
    """Compute the interval of ``expr``. Caller-supplied ``lookup``
    handles ``SymbolRef`` resolution; ``sort_of`` provides declared
    sort for operand-width inference. ``result_width`` flows through
    nested ops as the surrounding bv-width hint. ``diff_bounds``, if
    provided, refines ``Sub`` / ``IntSub`` of two ``SymbolRef``s by
    relational facts (rewriter-only feature).

    ``ite_max_depth`` caps Ite-recursion (rewriter-side; the abs_int
    domain leaves it ``None`` since the dataflow framework already
    bounds work via fixed-point iteration)."""
    if isinstance(expr, ConstExpr):
        c = const_to_int(expr)
        return iv.point(c) if c is not None else iv.TOP
    if isinstance(expr, SymbolRef):
        return lookup(expr.name)
    if isinstance(expr, ApplyExpr):
        return _eval_apply(
            expr,
            lookup=lookup,
            sort_of=sort_of,
            result_width=result_width,
            diff_bounds=diff_bounds,
            ite_max_depth=ite_max_depth,
            ite_depth=_ite_depth,
        )
    return iv.TOP


def _eval_apply(
    expr: ApplyExpr,
    *,
    lookup: LookupFn,
    sort_of: SortFn,
    result_width: "int | None",
    diff_bounds: "DiffBoundsFn | None",
    ite_max_depth: "int | None",
    ite_depth: int,
) -> Interval:
    op = expr.op
    args = list(expr.args)

    def recurse(e: TacExpr, *, rw: "int | None" = result_width) -> Interval:
        return eval_expr_iv(
            e,
            lookup=lookup,
            sort_of=sort_of,
            result_width=rw,
            diff_bounds=diff_bounds,
            ite_max_depth=ite_max_depth,
            _ite_depth=ite_depth,
        )

    # ``Apply(callee, ...)``: only ``safe_math_narrow_bvN`` has interval
    # semantics here (identity on the inner expression, with width clamp).
    # The inner is int-typed, so reset ``result_width`` to None.
    if op == "Apply" and args and isinstance(args[0], SymbolRef):
        width = _narrow_width(args[0].name)
        if width is not None and len(args) == 2:
            inner = recurse(args[1], rw=None)
            clamped = iv.narrow_clamp(inner, width)
            return clamped if clamped is not None else iv.TOP
        return iv.TOP

    # Int-domain (unbounded) arithmetic — interval math is sound
    # directly. ``result_width`` flows through to operands so a bv op
    # nested inside (e.g. ``Mod`` inside an ``IntMul``) can still
    # compute its modular result.
    if op == "IntAdd" and len(args) == 2:
        return iv.add(recurse(args[0]), recurse(args[1]))
    if op == "IntSub" and len(args) == 2:
        result = iv.sub(recurse(args[0]), recurse(args[1]))
        if (
            diff_bounds is not None
            and isinstance(args[0], SymbolRef)
            and isinstance(args[1], SymbolRef)
        ):
            d = diff_bounds(args[0].name, args[1].name)
            if d is not None:
                result = iv.meet(result, iv.from_pair(d))
        return result
    if op == "IntMul" and len(args) == 2:
        result = iv.mul_nonneg(recurse(args[0]), recurse(args[1]))
        return result if result is not None else iv.TOP
    if op == "IntDiv" and len(args) == 2:
        k = const_to_int(args[1]) if isinstance(args[1], ConstExpr) else None
        if k is not None and k > 0:
            a = recurse(args[0])
            result = iv.floor_div_by_pos_const(a, k)
            if result is not None:
                return result
        return iv.TOP
    if op == "IntCeilDiv" and len(args) == 2:
        a = recurse(args[0])
        b = recurse(args[1])
        result = iv.ceil_div_nonneg(a, b)
        return result if result is not None else iv.TOP
    if op == "IntMod" and len(args) == 2:
        k = const_to_int(args[1]) if isinstance(args[1], ConstExpr) else None
        if k is not None and k > 0:
            a = recurse(args[0])
            result = iv.mod_by_pos_const(a, k)
            if result is not None:
                return result
        return iv.TOP

    # Bv ``Div`` / ``Mod`` by a positive constant — result is already
    # bounded ([0, k-1] for Mod; floor(a/k) for Div). No surrounding
    # bv-width hint required: the mod / div primitive returns a sound
    # int-domain interval and any subsequent bv-clamp is identity for
    # k <= 2^width (the dominant case in TAC). For non-positive /
    # symbolic divisors we don't try a width-bounded fallback (Div by
    # zero is encoder-dependent; conservative TOP keeps callers honest).
    if op in {"Div", "Mod"} and len(args) == 2:
        k = const_to_int(args[1]) if isinstance(args[1], ConstExpr) else None
        if k is not None and k > 0:
            a = recurse(args[0])
            if op == "Div":
                result = iv.floor_div_by_pos_const(a, k)
            else:
                result = iv.mod_by_pos_const(a, k)
            if result is not None:
                return result
        return iv.TOP

    # Special case for bv ``Add(Y, wrap(X))``: bv ``Add`` of a
    # bv-domain ``Y`` and the bv image of a signed int ``X`` equals
    # the signed sum ``Y + X`` (mod ``2^width``). When the un-wrapped
    # signed sum already fits in ``[0, 2^width-1]``, the modular
    # result equals ``Y + X`` precisely — including the case where
    # ``X`` is negative (the bv ``Add`` cancels the ``+2^width``
    # correction baked into ``wrap``). Without this pattern, ``X``'s
    # signed range filters into a TOP through ``wrap``'s non-convex
    # image, throwing away the carry-cancellation insight.
    #
    # Width comes from the ``wrap`` callee itself (``wrap_<W>``), so
    # this pattern fires even when the surrounding context lacks a
    # bv-width hint and the other operand is a constant whose sort
    # provides nothing.
    if op == "Add" and len(args) == 2:
        for i, j in ((0, 1), (1, 0)):
            for wrap_width in _WRAP_WIDTHS.values():
                inner_x = _match_signed_wrap(args[j], wrap_width)
                if inner_x is None:
                    continue
                y_iv = recurse(args[i], rw=wrap_width)
                # ``inner_x`` is int-typed; reset width context.
                x_iv = eval_expr_iv(
                    inner_x,
                    lookup=lookup,
                    sort_of=sort_of,
                    result_width=None,
                    diff_bounds=diff_bounds,
                    ite_max_depth=ite_max_depth,
                    _ite_depth=ite_depth,
                )
                if (
                    y_iv.lo is not None and y_iv.hi is not None
                    and x_iv.lo is not None and x_iv.hi is not None
                ):
                    lo = y_iv.lo + x_iv.lo
                    hi = y_iv.hi + x_iv.hi
                    if 0 <= lo and hi <= (1 << wrap_width) - 1:
                        return Interval(lo, hi)
                # Either side unbounded, or the signed sum spans the
                # wrap boundary — fall through to general bv-binop.
                break

    # Raw bv ops — modular interval semantics. Width comes from the
    # surrounding context first, then from operand SymbolRef sorts when
    # they agree (e.g. ``Add(R_bv256, R_bv256)`` is bv256-modular even
    # when the assignment's lhs sort is missing). Without either signal,
    # return TOP.
    if op in {"Add", "Sub", "Mul"} and len(args) == 2:
        width = result_width
        if width is None:
            width = _infer_bv_width_from_operand_sorts(args, sort_of)
        if width is None:
            return iv.TOP
        a = recurse(args[0], rw=width)
        b = recurse(args[1], rw=width)
        if op == "Sub" and diff_bounds is not None and isinstance(
            args[0], SymbolRef
        ) and isinstance(args[1], SymbolRef):
            unwrapped = iv.sub(a, b)
            d = diff_bounds(args[0].name, args[1].name)
            if d is not None:
                unwrapped = iv.meet(unwrapped, iv.from_pair(d))
            return iv.bv_clamp(unwrapped, width)
        return _eval_bv_binop(op, a, b, width)

    if op == "Ite" and len(args) == 3:
        if ite_max_depth is not None and ite_depth >= ite_max_depth:
            return iv.TOP
        next_depth = ite_depth + 1
        return iv.join(
            eval_expr_iv(
                args[1],
                lookup=lookup,
                sort_of=sort_of,
                result_width=result_width,
                diff_bounds=diff_bounds,
                ite_max_depth=ite_max_depth,
                _ite_depth=next_depth,
            ),
            eval_expr_iv(
                args[2],
                lookup=lookup,
                sort_of=sort_of,
                result_width=result_width,
                diff_bounds=diff_bounds,
                ite_max_depth=ite_max_depth,
                _ite_depth=next_depth,
            ),
        )

    if op in _REL_OPS and len(args) == 2:
        return iv.bool_iv()
    if op in _BOOL_BIN_OPS and len(args) == 2:
        return iv.bool_iv()
    if op in _BOOL_UN_OPS and len(args) == 1:
        return iv.bool_iv()
    return iv.TOP


def _eval_bv_binop(
    op: str, a: Interval, b: Interval, width: int
) -> Interval:
    """Modular bv binop on operand intervals ``a``, ``b`` at width
    ``width``. Compute the un-wrapped int-domain result; if it fits
    in ``[0, 2^width - 1]`` the bv op didn't wrap and the precise
    interval is sound; otherwise return the full bv range
    (overapproximation across the wrap)."""
    if op == "Add":
        return iv.bv_clamp(iv.add(a, b), width)
    if op == "Sub":
        return iv.bv_clamp(iv.sub(a, b), width)
    if op == "Mul":
        unwrapped = iv.mul_nonneg(a, b)
        if unwrapped is None:
            return iv.bv_width_iv(width)
        return iv.bv_clamp(unwrapped, width)
    if op == "Div":
        # Bv unsigned div by positive const: floor(a/k) <= a, so never
        # grows beyond the dividend's bv range. Symbolic / zero
        # divisors fall through to the bv range.
        k: "int | None" = None
        if b.lo is not None and b.lo == b.hi and b.lo > 0:
            k = b.lo
        if k is not None:
            result = iv.floor_div_by_pos_const(a, k)
            if result is not None:
                return iv.bv_clamp(result, width)
        return iv.bv_width_iv(width)
    if op == "Mod":
        # Bv unsigned mod by positive const: result < k <= 2^width, so
        # the result always fits.
        k = None
        if b.lo is not None and b.lo == b.hi and b.lo > 0:
            k = b.lo
        if k is not None:
            result = iv.mod_by_pos_const(a, k)
            if result is not None:
                return iv.bv_clamp(result, width)
        return iv.bv_width_iv(width)
    return iv.bv_width_iv(width)


def unwrapped_int_op(
    op: str,
    args: "list[TacExpr]",
    *,
    lookup: LookupFn,
    sort_of: SortFn,
    diff_bounds: "DiffBoundsFn | None" = None,
    ite_max_depth: "int | None" = None,
) -> Interval:
    """Compute the interval of ``op(args)`` in the *unbounded Int*
    domain — without bv wrap clamping.

    For wrap-detection callers (e.g. ``ADD_BV_TO_INT``) which need to
    decide whether a bv op overflows the bv domain. Operands are
    evaluated with the same shared evaluator (so they're bv-clamped
    where appropriate), but the binop itself stays in Int.
    """
    a = eval_expr_iv(
        args[0], lookup=lookup, sort_of=sort_of,
        diff_bounds=diff_bounds, ite_max_depth=ite_max_depth,
    )
    if len(args) >= 2:
        b = eval_expr_iv(
            args[1], lookup=lookup, sort_of=sort_of,
            diff_bounds=diff_bounds, ite_max_depth=ite_max_depth,
        )
    if op in {"Add", "IntAdd"}:
        return iv.add(a, b)
    if op in {"Sub", "IntSub"}:
        result = iv.sub(a, b)
        if (
            diff_bounds is not None
            and isinstance(args[0], SymbolRef)
            and isinstance(args[1], SymbolRef)
        ):
            d = diff_bounds(args[0].name, args[1].name)
            if d is not None:
                result = iv.meet(result, iv.from_pair(d))
        return result
    if op in {"Mul", "IntMul"}:
        result = iv.mul_nonneg(a, b)
        return result if result is not None else iv.TOP
    return iv.TOP
