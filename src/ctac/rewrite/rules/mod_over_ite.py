"""``Mod(Ite(c, T, E), K)`` -> ``Ite(c, Mod(T, K), Mod(E, K))``
distribution, when **both** arms' Mod simplifies under the
path-refined range of each branch.

Pattern (motivating shape from the u128 decrement chain):

    R117 = Ite(TB, IntSub(R, 1), 0xff..f256-1)        ; bv256 bv-const else arm
    R119 = Mod(R117, 2^64)

where ``TB`` is the carry-flag SymRef pointing to ``Ge(R, 1)``.

Without path refinement, ``IntSub(R, 1)`` has range ``[-1, R_hi-1]``
because R is unrefined u64. With ``TB = Ge(R, 1)`` available in the
then-arm, ``R``'s lower bound refines to 1 and the IntSub fits in
``[0, R_hi-1] ⊆ [0, 2^64-1]`` — so Mod by 2^64 is identity. The
else-arm ``Mod(2^256-1, 2^64)`` is a const-const fold to ``2^64-1``.

Both arms simplify; distribution is profitable:

    R119 = Ite(TB, IntSub(R, 1), 0xff..f64-1)

Without the path refinement the rule wouldn't fire — that's the
exact case the user said was the goal.

Soundness: standard distribution of ``Mod`` over ``Ite``
(``Mod(Ite(c, T, E), K) = Ite(c, Mod(T, K), Mod(E, K))``) is
semantically valid for any K. Per-arm simplification uses only
sound facts: const-const fold (always), range-fits identity
(when interval inference proves the arm is in ``[0, K-1]`` under
the branch condition), and ``Mod`` idempotence
(``Mod(Mod(X, K), K) = Mod(X, K)``).

Cost gate: rule only fires when **both** arms reduce. Otherwise
the distribution duplicates the Mod into both arms without
shrinking, which is gratuitous.

Path refinement is conservative: only ``Cmp(SymRef, Const)`` shapes
(and their negation for the else-arm) are extracted from the
condition; nested LAnd is decomposed. Anything else falls back to
the unrefined range.
"""

from __future__ import annotations

from ctac.analysis.abs_int import interval_ops as iv
from ctac.analysis.abs_int.interval_ops import Interval
from ctac.analysis.symbols import canonical_symbol
from ctac.ast.nodes import ApplyExpr, ConstExpr, SymbolRef, TacExpr
from ctac.rewrite.context import RewriteCtx
from ctac.rewrite.framework import Rule
from ctac.rewrite.range_infer import infer_expr_range
from ctac.rewrite.rules.common import const_to_int, reformat_const

_NEG_CMP = {"Ge": "Lt", "Gt": "Le", "Le": "Gt", "Lt": "Ge", "Eq": "Ne", "Ne": "Eq"}


def _is_ite(e: TacExpr) -> bool:
    return isinstance(e, ApplyExpr) and e.op == "Ite" and len(e.args) == 3


def _negate_cmp(cmp: ApplyExpr) -> ApplyExpr | None:
    """Turn ``Ge(X, K)`` into ``Lt(X, K)`` etc. for else-arm refinement."""
    if cmp.op not in _NEG_CMP or len(cmp.args) != 2:
        return None
    return ApplyExpr(_NEG_CMP[cmp.op], cmp.args)


def _refinement_from_cmp(cmp: ApplyExpr) -> tuple[str, Interval] | None:
    """A single ``Cmp(SymRef, Const)`` (or symmetric) produces a
    refinement interval for the symbol. Returns ``(canon_name, iv)``
    or ``None`` if the shape isn't recognized."""
    if cmp.op not in {"Ge", "Gt", "Le", "Lt", "Eq", "Ne"} or len(cmp.args) != 2:
        return None
    a, b = cmp.args
    # Identify (sym, const) — either order.
    if isinstance(a, SymbolRef) and isinstance(b, ConstExpr):
        sym, const, flip = a, b, False
    elif isinstance(b, SymbolRef) and isinstance(a, ConstExpr):
        sym, const, flip = b, a, True
    else:
        return None
    k = const_to_int(const)
    if k is None:
        return None
    op = cmp.op
    if flip:
        # ``Cmp(K, X)`` is ``Cmp_flip(X, K)``: Ge↔Le, Gt↔Lt; Eq/Ne unchanged.
        op = {"Ge": "Le", "Gt": "Lt", "Le": "Ge", "Lt": "Gt"}.get(op, op)
    if op == "Ge":
        refined = Interval(k, None)
    elif op == "Gt":
        refined = Interval(k + 1, None)
    elif op == "Le":
        refined = Interval(None, k)
    elif op == "Lt":
        refined = Interval(None, k - 1)
    elif op == "Eq":
        refined = Interval(k, k)
    else:  # Ne — no interval refinement (split would be required)
        return None
    return canonical_symbol(sym.name), refined


def _collect_refinements(
    cond: TacExpr,
    branch_true: bool,
    ctx: RewriteCtx,
    out: dict[str, Interval],
) -> None:
    """Walk ``cond`` (with SymRef lookthrough) and merge every
    ``Cmp(SymRef, Const)`` it contributes into ``out`` via interval
    meet. ``LAnd`` decomposes naturally when ``branch_true`` is True;
    the negation for ``branch_true`` False expands DeMorgan-style as
    far as the limited shapes recognize.
    """
    # Look through SymRef alias to actual cond expr.
    if isinstance(cond, SymbolRef):
        d = ctx.definition(cond.name)
        if d is not None:
            cond = d
    if not isinstance(cond, ApplyExpr):
        return
    if branch_true:
        if cond.op == "LAnd" and len(cond.args) == 2:
            _collect_refinements(cond.args[0], True, ctx, out)
            _collect_refinements(cond.args[1], True, ctx, out)
            return
        if cond.op == "LNot" and len(cond.args) == 1:
            _collect_refinements(cond.args[0], False, ctx, out)
            return
        ref = _refinement_from_cmp(cond)
    else:
        # branch_true is False: we want refinements under cond=False.
        # DeMorgan: !(LAnd(a, b)) = LOr(!a, !b); LOr is unhandled
        # (refinement would need disjunction of intervals, which we
        # over-approximate). Skip LAnd for else-branch.
        if cond.op == "LNot" and len(cond.args) == 1:
            _collect_refinements(cond.args[0], True, ctx, out)
            return
        negated = _negate_cmp(cond)
        if negated is None:
            return
        ref = _refinement_from_cmp(negated)
    if ref is None:
        return
    name, refined = ref
    if name in out:
        out[name] = iv.meet(out[name], refined)
    else:
        out[name] = refined


def _eval_with_refinements(
    expr: TacExpr,
    refinements: dict[str, Interval],
    ctx: RewriteCtx,
) -> Interval:
    """Compute ``expr``'s interval using ``ctx`` as the base and
    ``refinements`` as per-symbol overrides (meet-combined).

    Covers the small set of int-op shapes that appear inside Ite arms
    in chunked u128 chains: SymRef, ConstExpr, ``IntAdd``,
    ``IntSub``. Anything else falls back to the unrefined
    ``infer_expr_range``."""
    if isinstance(expr, ConstExpr):
        v = const_to_int(expr)
        if v is None:
            return iv.TOP
        return Interval(v, v)
    if isinstance(expr, SymbolRef):
        natural = infer_expr_range(expr, ctx)
        natural_iv = iv.from_pair(natural) if natural is not None else iv.TOP
        canon = canonical_symbol(expr.name)
        if canon in refinements:
            return iv.meet(natural_iv, refinements[canon])
        return natural_iv
    if isinstance(expr, ApplyExpr):
        if expr.op == "IntAdd" and len(expr.args) == 2:
            return iv.add(
                _eval_with_refinements(expr.args[0], refinements, ctx),
                _eval_with_refinements(expr.args[1], refinements, ctx),
            )
        if expr.op == "IntSub" and len(expr.args) == 2:
            return iv.sub(
                _eval_with_refinements(expr.args[0], refinements, ctx),
                _eval_with_refinements(expr.args[1], refinements, ctx),
            )
    # Fallback: unrefined.
    r = infer_expr_range(expr, ctx)
    return iv.from_pair(r) if r is not None else iv.TOP


def _simplify_mod_arm(
    x: TacExpr,
    k_expr: ConstExpr,
    kv: int,
    refinements: dict[str, Interval],
    ctx: RewriteCtx,
) -> TacExpr | None:
    """Try to simplify ``Mod(x, kv)`` under ``refinements``.
    Returns the simplified expression or ``None`` if no simplification
    is provably sound.

    Three cases handled:
      (1) ``x`` is a literal const  -> ``Mod`` is const-const fold.
      (2) ``x``'s refined range fits in ``[0, kv-1]`` -> identity.
      (3) ``x`` is already ``Mod(_, kv)`` -> idempotent.
    """
    # (1) Const fold.
    xv = const_to_int(x)
    if xv is not None and isinstance(x, ConstExpr):
        return reformat_const(x, xv % kv)
    # (2) Range-fits identity.
    rng = _eval_with_refinements(x, refinements, ctx)
    if rng.lo is not None and rng.hi is not None and rng.lo >= 0 and rng.hi <= kv - 1:
        return x
    # (3) Mod idempotence.
    if isinstance(x, ApplyExpr) and x.op == "Mod" and len(x.args) == 2:
        inner_kv = const_to_int(x.args[1])
        if inner_kv == kv:
            return x
    return None


def _rewrite_mod_over_ite(expr: TacExpr, ctx: RewriteCtx) -> TacExpr | None:
    """``Mod(Ite(c, T, E), K)`` -> ``Ite(c, Mod(T, K), Mod(E, K))``
    when both ``Mod`` arms simplify under path-refined ranges.

    Fires only on top-level ``Mod`` of an ``Ite`` whose divisor is a
    positive constant. The arm-simplification gate is strict: both
    arms must reduce (const-fold, range-identity, or Mod-idempotent)
    or the rule abstains, since otherwise distribution duplicates
    ``Mod`` into both arms without shrinking either.
    """
    if not (isinstance(expr, ApplyExpr) and expr.op == "Mod" and len(expr.args) == 2):
        return None
    inner, k_expr = expr.args
    if not isinstance(k_expr, ConstExpr):
        return None
    # The Ite can arrive directly as the Mod operand or through a
    # SymbolRef alias (the common case — chunked u128 chains name the
    # Ite via a register like R117). Lookthrough exposes the Ite at
    # the cost of duplicating its structure into the Mod site, but
    # the cost gate further down ensures the duplication shrinks via
    # per-arm simplification.
    inner_lt = ctx.lookthrough(inner)
    if not _is_ite(inner_lt):
        return None
    assert isinstance(inner_lt, ApplyExpr)
    cond, then_arm, else_arm = inner_lt.args
    kv = const_to_int(k_expr)
    if kv is None or kv <= 0:
        return None
    then_refinements: dict[str, Interval] = {}
    _collect_refinements(cond, True, ctx, then_refinements)
    else_refinements: dict[str, Interval] = {}
    _collect_refinements(cond, False, ctx, else_refinements)
    new_then = _simplify_mod_arm(then_arm, k_expr, kv, then_refinements, ctx)
    if new_then is None:
        return None
    new_else = _simplify_mod_arm(else_arm, k_expr, kv, else_refinements, ctx)
    if new_else is None:
        return None
    return ApplyExpr("Ite", (cond, new_then, new_else))


MOD_OVER_ITE = Rule(
    name="ModOverIte",
    fn=_rewrite_mod_over_ite,
    description=(
        "Mod(Ite(c, T, E), K) -> Ite(c, Mod(T, K), Mod(E, K)) when "
        "both arms' Mod simplifies under path-refined ranges "
        "(const fold, range-fits identity, or Mod idempotent)."
    ),
)

__all__ = ["MOD_OVER_ITE"]
