"""SELECT_OVER_STORE: fold Select through Store/Ite chains.

For ``Select(M, k)`` where ``M`` is a SymbolRef to a bytemap, walk
``M``'s static def. Three terminating shapes resolve cleanly:

1. **Store-key hit.** Def is ``Store(M_old, k', v)`` and ``k' ≡ k``
   syntactically -> the Select equals ``v``.
2. **Constant-disjoint peel.** Def is ``Store(M_old, k', v)`` where
   both ``k`` and ``k'`` are ``ConstExpr`` and unequal -> the Store
   doesn't affect this read; recurse on ``Select(M_old, k)``.
3. **Ite-shared-root collapse.** Def is ``Ite(c, M_t, M_f)`` and both
   arms recursively resolve to the *same* TacExpr -> return that
   single expression. The cache (see below) makes the shared-root
   case cheap to detect.

A symbolic-key Store with no syntactic equality and no constant-vs-
constant inequality bails (no fire). Same for an Ite whose arms
disagree after recursive resolution. The rule only fires when the
walk produces a single clean output (a value, a peeled
``Select(M_leaf, k)``, or a fully-collapsed Ite shared by both arms).

Memoization
-----------

Per-iteration cache attached lazily to ``ctx`` keyed on
``(canonical_symbol(M), canonical(k))``. The cache makes
Ite-of-bytemaps with shared roots cheap: when both arms recurse into
the same root with the same index, the second arm hits the cache.
Implicitly reset across rewriter iterations because ``RewriteCtx`` is
recreated per iteration. Cache values include ``None`` (bailed) so we
don't retry unresolvable queries.

Soundness
---------

Each step is the standard array ``select``/``store`` axiom or
``select(ite(c, M_t, M_f), k) = ite(c, select(M_t, k), select(M_f, k))``
distribution. The conservative key-comparison (syntactic eq, or
constant-vs-constant neq, or bail) means the rule never produces
output that depends on equality of two symbolic terms.

Placement
---------

Registered in ``simplify_pipeline`` (catches input-level forms) and in
the late cascade cleanup phase in ``commands_rw.py`` (catches
post-CSE shapes where parallel-arm M-chains have unified into shared-
root Ites). The rule produces compound RHSes so it cannot co-locate
with CSE; both registration sites are CSE-snapshot-safe (CSE doesn't
run alongside).
"""

from __future__ import annotations

from ctac.analysis.symbols import canonical_symbol
from ctac.ast.nodes import ApplyExpr, ConstExpr, SymbolRef, TacExpr
from ctac.rewrite.context import RewriteCtx
from ctac.rewrite.framework import Rule


_BYTEMAP_SORTS = frozenset({"bytemap", "ghostmap"})


def _canonical_expr(expr: TacExpr) -> TacExpr:
    """Strip DSA suffixes recursively. Used as cache-key normalizer
    so ``R0`` and ``R0:5`` hash to the same key."""
    if isinstance(expr, SymbolRef):
        return SymbolRef(canonical_symbol(expr.name))
    if isinstance(expr, ApplyExpr):
        return ApplyExpr(expr.op, tuple(_canonical_expr(a) for a in expr.args))
    return expr


def _const_value(expr: TacExpr) -> str | None:
    """Return the literal text of ``expr`` if it's a ``ConstExpr``,
    else ``None``. Used for constant-vs-constant inequality checks."""
    if isinstance(expr, ConstExpr):
        return expr.value
    return None


def _key_relation(a: TacExpr, b: TacExpr) -> str:
    """Compare two TAC keys. Returns ``"eq"`` if syntactically equal
    (after canonicalization), ``"neq"`` if both are constants and
    unequal, ``"unknown"`` otherwise.

    Constant comparison uses literal text after normalization — TAC
    parses 0x4 and 4(int) as different ConstExprs even though they're
    semantically equal; we use the canonical form ``ConstExpr.value``
    text directly. False negatives are sound (we just don't fire);
    false positives would be unsound but are precluded by syntactic
    equality on the same constructor."""
    a_canon = _canonical_expr(a)
    b_canon = _canonical_expr(b)
    if a_canon == b_canon:
        return "eq"
    a_v = _const_value(a)
    b_v = _const_value(b)
    if a_v is not None and b_v is not None and a_v != b_v:
        return "neq"
    return "unknown"


def _is_bytemap_symbol(name: str, ctx: RewriteCtx) -> bool:
    canon = canonical_symbol(name)
    return ctx.symbol_sorts.get(canon) in _BYTEMAP_SORTS


def _resolve_select(
    map_sym: SymbolRef, idx_expr: TacExpr, ctx: RewriteCtx, cache: dict
) -> TacExpr | None:
    """Top-level resolution entry: handle a SymbolRef map by looking
    up its static def, then dispatching to ``_resolve_in_def``. Cache
    the result (including ``None`` for bailed queries)."""
    canon = canonical_symbol(map_sym.name)
    cache_key = (canon, _canonical_expr(idx_expr))
    if cache_key in cache:
        return cache[cache_key]

    # Belt-and-braces: the rule's caller already checks the outer
    # SymbolRef is a bytemap, but recursion through aliases lands here
    # too — re-check.
    if not _is_bytemap_symbol(map_sym.name, ctx):
        cache[cache_key] = None
        return None

    def_rhs = ctx.definition(canon)
    if def_rhs is None:
        # Leaf: havoc-defined, dynamic-multi-def, or no static def.
        # The Select stays rooted here.
        result: TacExpr | None = ApplyExpr(
            "Select", (SymbolRef(canon), idx_expr)
        )
        cache[cache_key] = result
        return result

    result = _resolve_in_def(def_rhs, idx_expr, ctx, cache)
    cache[cache_key] = result
    return result


def _resolve_in_def(
    def_rhs: TacExpr, idx_expr: TacExpr, ctx: RewriteCtx, cache: dict
) -> TacExpr | None:
    """Resolve ``Select(<def_rhs>, idx_expr)`` where ``def_rhs`` is a
    Store, Ite, or SymbolRef sub-tree. Returns the resolved expr or
    ``None`` if the walk can't make clean progress."""
    if isinstance(def_rhs, SymbolRef):
        # Alias to another bytemap symbol — recurse via the cached
        # symbol-level entry point.
        if not _is_bytemap_symbol(def_rhs.name, ctx):
            return None
        return _resolve_select(def_rhs, idx_expr, ctx, cache)

    if isinstance(def_rhs, ApplyExpr):
        if def_rhs.op == "Store" and len(def_rhs.args) == 3:
            m_old, k_store, v = def_rhs.args
            rel = _key_relation(k_store, idx_expr)
            if rel == "eq":
                return v
            if rel == "neq":
                return _resolve_in_def(m_old, idx_expr, ctx, cache)
            return None  # symbolic / mixed shape: bail

        if def_rhs.op == "Ite" and len(def_rhs.args) == 3:
            _cond, m_t, m_f = def_rhs.args
            t_r = _resolve_in_def(m_t, idx_expr, ctx, cache)
            if t_r is None:
                return None
            e_r = _resolve_in_def(m_f, idx_expr, ctx, cache)
            if e_r is None:
                return None
            # Only fire on Ite when both arms agree post-resolution —
            # otherwise we'd inflate one Select into Ite-of-two-Selects.
            if t_r == e_r:
                return t_r
            return None

    return None


def _rewrite_select_over_store(expr: TacExpr, ctx: RewriteCtx) -> TacExpr | None:
    if not (
        isinstance(expr, ApplyExpr)
        and expr.op == "Select"
        and len(expr.args) == 2
    ):
        return None
    mem, idx = expr.args
    if not isinstance(mem, SymbolRef):
        return None
    if not _is_bytemap_symbol(mem.name, ctx):
        return None

    cache = getattr(ctx, "_sos_cache", None)
    if cache is None:
        cache = {}
        ctx._sos_cache = cache  # type: ignore[attr-defined]

    result = _resolve_select(mem, idx, ctx, cache)
    if result is None:
        return None
    # Avoid spurious "fire" when resolution returns the same expression
    # (e.g. leaf bytemap whose canonicalized form already matches the
    # input). Compare canonical forms — input may carry DSA suffixes.
    if _canonical_expr(result) == _canonical_expr(expr):
        return None
    return result


SELECT_OVER_STORE = Rule(
    name="SelectOverStore",
    fn=_rewrite_select_over_store,
    description=(
        "Fold Select(M, k) through M's def chain when the result "
        "resolves cleanly: Store-key hit yields the stored value; "
        "constant-disjoint Store peels; Ite-of-bytemaps where both "
        "arms agree collapses to the single arm."
    ),
)
