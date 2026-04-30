"""Strengthening normalization for store-equalities.

Rewrites ``Eq(Store(M, k1, v1), Store(M, k2, v2))`` — both sides over the
same syntactic base map ``M`` — into ``LAnd(Eq(k1, k2), Eq(v1, v2))``,
dropping any conjuncts that fold to a trivial reflexive equality. With one
trivial conjunct this collapses to the surviving one; with both, to ``true``.

Soundness caveat
----------------

The original equality is denotationally
``(k1==k2 ∧ v1==v2) ∨ (k1!=k2 ∧ v1==M[k1] ∧ v2==M[k2])`` — the second
disjunct covers "writes coincide because the values were already there".
Replacing the disjunction with just the first conjunct is a *strengthening*:
in an ``assume`` context it admits fewer paths, so it can mask real bugs. We
use it from the rw-eq pipeline, where the equality encodes the rwriter
writing the same cells the same way (a structural / syntactic claim) rather
than producing denotationally-equal maps via different write traces; rw-eq's
contract excludes the "coincidentally equal" case by design.

Don't add this rule to general-purpose pipelines without auditing whether
the host context tolerates the strengthening.
"""

from __future__ import annotations

from ctac.ast.nodes import ApplyExpr, ConstExpr, SymbolRef, TacExpr
from ctac.rewrite.context import RewriteCtx
from ctac.rewrite.framework import Rule

_TRUE = ConstExpr("true")


def _is_store(expr: TacExpr) -> bool:
    return (
        isinstance(expr, ApplyExpr)
        and expr.op == "Store"
        and len(expr.args) == 3
    )


def _same_base_map(a: TacExpr, b: TacExpr) -> bool:
    # Restricted to syntactic SymbolRef equality on both sides — that is
    # what rw-eq emits in practice and keeps the rewrite obviously safe to
    # apply (no aliasing reasoning required).
    return isinstance(a, SymbolRef) and isinstance(b, SymbolRef) and a.name == b.name


def normalize_store_eq(expr: TacExpr) -> TacExpr | None:
    """Top-level rewrite for ``Eq(Store(M, k1, v1), Store(M, k2, v2))``.

    Returns the strengthened conjunction (with trivial conjuncts dropped)
    when both sides are ``Store``\\ s over a syntactically identical base
    map, otherwise ``None``.
    """
    if not (isinstance(expr, ApplyExpr) and expr.op == "Eq" and len(expr.args) == 2):
        return None
    left, right = expr.args
    if not (_is_store(left) and _is_store(right)):
        return None
    assert isinstance(left, ApplyExpr) and isinstance(right, ApplyExpr)
    base_l, k_l, v_l = left.args
    base_r, k_r, v_r = right.args
    if not _same_base_map(base_l, base_r):
        return None
    conjuncts: list[TacExpr] = []
    if k_l != k_r:
        conjuncts.append(ApplyExpr("Eq", (k_l, k_r)))
    if v_l != v_r:
        conjuncts.append(ApplyExpr("Eq", (v_l, v_r)))
    if not conjuncts:
        return _TRUE
    if len(conjuncts) == 1:
        return conjuncts[0]
    return ApplyExpr("LAnd", tuple(conjuncts))


def _rewrite_store_eq(expr: TacExpr, _ctx: RewriteCtx) -> TacExpr | None:
    return normalize_store_eq(expr)


STORE_EQ_NORM = Rule(
    name="StoreEqNorm",
    fn=_rewrite_store_eq,
    description=(
        "Eq(Store(M, k1, v1), Store(M, k2, v2)) with shared base M -> "
        "LAnd(Eq(k1, k2), Eq(v1, v2)) (trivial conjuncts dropped). "
        "Strengthening — sound only where coincidental map equality is "
        "excluded by contract (e.g. rw-eq inputs)."
    ),
)
