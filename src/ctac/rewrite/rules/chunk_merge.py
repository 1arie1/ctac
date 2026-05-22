"""Two cooperating rules that recombine the chunk extracts of a
narrowed Euclidean split back into the original wide value.

When a fresh u128 / u192 / ... bv-register ``T`` has been split via
``hi = Div(T, K); lo = Mod(T, K)`` (the standard chunk extraction
the u128-add / u128-decrement passes emit), the SBF frontend
typically reconstructs ``T`` later as
``ShiftLeft(hi, log2(K)) + lo`` inside a wider int expression. The
rules here collapse that reconstruction:

(1) ``SHIFT_LEFT_TO_INT_MUL``:
    ``ShiftLeft(X, K_count) -> IntMul(X, 2^K_count)`` when range
    inference proves ``X * 2^K_count < 2^256`` (so the bv shift has
    the same value as the int mul). Conversion from a bv shift into
    an int multiplication exposes the multiplicative structure to
    subsequent rules — most importantly to ``CHUNK_MERGE`` below.

(2) ``CHUNK_MERGE``:
    ``narrow(IntAdd(IntMul(Div(T, K), K), Mod(T, K))) -> T`` when
    ``T`` is a SymbolRef and ``K`` is a constant. This is the
    Euclidean-division identity ``(T // K) * K + (T mod K) = T``
    wrapped by the narrow that the surrounding int → bv lift
    inserts. The rule also accepts the symmetric IntAdd ordering
    and looks through SymRef aliases on the ``hi`` and ``lo``
    sub-expressions (since they're typically named via
    ``R_hi = Div(T, K); R_lo = Mod(T, K)``).

Together they turn the post-decrement reconstruction
``narrow(IntAdd(ShiftLeft(R_hi, 64), R_lo))`` (where R_hi and R_lo
are the chunks of ``H1 = Sub(H0, 1)``) back into ``H1`` directly —
exactly the lift / op / split / merge pipeline the user described
as the goal of the u128 work.

Soundness:

(1) ``ShiftLeft(X, K) = X * 2^K (mod 2^256)``. When the strict
    upper bound ``X * 2^K < 2^256`` holds, ``mod 2^256`` is
    identity, so the values are equal. ``infer_expr_range`` checks
    the bound.

(2) Standard Euclidean-division identity for non-negative
    arguments. ``Div`` and ``Mod`` on bv are unsigned, hence
    non-negative. ``narrow`` on the result coerces back to bv;
    safe since ``T`` is already bv-domain.
"""

from __future__ import annotations

from ctac.analysis.symbols import canonical_symbol
from ctac.ast.nodes import ApplyExpr, ConstExpr, SymbolRef, TacExpr
from ctac.rewrite.context import RewriteCtx, _is_safe_narrow_apply
from ctac.rewrite.framework import Rule
from ctac.rewrite.range_infer import infer_expr_range
from ctac.rewrite.rules.common import const_to_int

_BV256_MAX = (1 << 256) - 1


def _int_const(value: int) -> ConstExpr:
    return ConstExpr(f"{hex(value)}(int)")


def _rewrite_shift_left_to_int_mul(
    expr: TacExpr, ctx: RewriteCtx
) -> TacExpr | None:
    """``ShiftLeft(X, K)`` -> ``IntMul(X, 2^K)`` when no bv-wrap occurs.

    Range gate: ``infer_expr_range`` on the candidate ``IntMul``
    expression must show ``hi <= 2^256-1`` and ``lo >= 0``. The
    candidate is constructed before the gate so the inference walks
    the IntMul shape with ``mul_nonneg`` semantics.
    """
    if not (
        isinstance(expr, ApplyExpr)
        and expr.op == "ShiftLeft"
        and len(expr.args) == 2
    ):
        return None
    x, k_expr = expr.args
    k = const_to_int(k_expr)
    if k is None or k <= 0 or k >= 256:
        return None
    candidate = ApplyExpr("IntMul", (x, _int_const(1 << k)))
    rng = infer_expr_range(candidate, ctx)
    if rng is None or rng[0] is None or rng[1] is None:
        return None
    if rng[0] < 0 or rng[1] > _BV256_MAX:
        return None
    return candidate


SHIFT_LEFT_TO_INT_MUL = Rule(
    name="ShiftLeftToIntMul",
    fn=_rewrite_shift_left_to_int_mul,
    description=(
        "ShiftLeft(X, K) -> IntMul(X, 2^K) when range inference proves "
        "X * 2^K fits in bv256 (no wrap). Exposes the multiplicative "
        "structure for downstream chunk-merge."
    ),
)


def _match_int_mul_with_const_k(
    expr: TacExpr, ctx: RewriteCtx
) -> tuple[TacExpr, int] | None:
    """If ``expr`` is ``IntMul(X, K_const)`` or ``IntMul(K_const, X)``,
    return ``(X, K_const_value)``. Lookthrough on the input."""
    e = ctx.lookthrough(expr)
    if not (isinstance(e, ApplyExpr) and e.op == "IntMul" and len(e.args) == 2):
        return None
    a, b = e.args
    a_v = const_to_int(a)
    b_v = const_to_int(b)
    if b_v is not None:
        return a, b_v
    if a_v is not None:
        return b, a_v
    return None


def _match_div_with_k(
    expr: TacExpr, want_k: int, ctx: RewriteCtx
) -> SymbolRef | None:
    """If ``expr`` (or its lookthrough) is ``Div(T, K)`` with T a
    SymbolRef and K matching ``want_k``, return T."""
    e = ctx.lookthrough(expr)
    if not (isinstance(e, ApplyExpr) and e.op == "Div" and len(e.args) == 2):
        return None
    t, k = e.args
    if const_to_int(k) != want_k:
        return None
    return t if isinstance(t, SymbolRef) else None


def _match_mod_with_k(
    expr: TacExpr, want_k: int, ctx: RewriteCtx
) -> SymbolRef | None:
    """If ``expr`` (or its lookthrough) is ``Mod(T, K)`` with T a
    SymbolRef and K matching ``want_k``, return T."""
    e = ctx.lookthrough(expr)
    if not (isinstance(e, ApplyExpr) and e.op == "Mod" and len(e.args) == 2):
        return None
    t, k = e.args
    if const_to_int(k) != want_k:
        return None
    return t if isinstance(t, SymbolRef) else None


def _flatten_int_add(expr: TacExpr) -> list[TacExpr]:
    """Flatten a binary-IntAdd tree into a list of additive terms.
    Non-IntAdd inputs return ``[expr]``."""
    if not (
        isinstance(expr, ApplyExpr) and expr.op == "IntAdd" and len(expr.args) == 2
    ):
        return [expr]
    return _flatten_int_add(expr.args[0]) + _flatten_int_add(expr.args[1])


def _rewrite_chunk_merge(
    expr: TacExpr, ctx: RewriteCtx
) -> TacExpr | None:
    """``narrow(IntAdd(IntMul(Div(T, K), K), Mod(T, K) + ...rest))`` ->
    ``narrow(T + ...rest)`` (and the 2-term special case
    ``narrow(IntMul(Div(T, K), K) + Mod(T, K))`` -> ``T``).

    Flattens the IntAdd tree, searches for a ``IntMul(Div(T, K), K)``
    term paired with a ``Mod(T, K)`` term (same T, same K). Replaces
    both with ``T`` and rebuilds the narrow over the remaining sum.
    Looks through SymbolRef aliases on the ``Div(T, K)`` and
    ``Mod(T, K)`` sub-expressions.
    """
    if not _is_safe_narrow_apply(expr):
        return None
    assert isinstance(expr, ApplyExpr)
    narrow_fn = expr.args[0]
    inner = expr.args[1]
    terms = _flatten_int_add(inner)
    if len(terms) < 2:
        return None
    for i, t_i in enumerate(terms):
        mul_match = _match_int_mul_with_const_k(t_i, ctx)
        if mul_match is None:
            continue
        div_expr, k_value = mul_match
        t_from_div = _match_div_with_k(div_expr, k_value, ctx)
        if t_from_div is None:
            continue
        for j, t_j in enumerate(terms):
            if i == j:
                continue
            t_from_mod = _match_mod_with_k(t_j, k_value, ctx)
            if t_from_mod is None:
                continue
            if canonical_symbol(t_from_div.name) != canonical_symbol(
                t_from_mod.name
            ):
                continue
            # Combine the pair into ``T``; rebuild the narrow.
            remaining = [
                terms[k] for k in range(len(terms)) if k != i and k != j
            ]
            if not remaining:
                # Pure 2-term Euclidean identity — drop the narrow.
                return t_from_div
            new_sum: TacExpr = t_from_div
            for r in remaining:
                new_sum = ApplyExpr("IntAdd", (new_sum, r))
            return ApplyExpr("Apply", (narrow_fn, new_sum))
    return None


CHUNK_MERGE = Rule(
    name="ChunkMerge",
    fn=_rewrite_chunk_merge,
    description=(
        "narrow(IntAdd(IntMul(Div(T, K), K), Mod(T, K))) -> T. "
        "The Euclidean-division identity wrapped by the int->bv "
        "narrow. Looks through SymRef aliases on the chunks."
    ),
)


__all__ = ["CHUNK_MERGE", "SHIFT_LEFT_TO_INT_MUL"]
