"""HAVOC_EQUATE_SUBST: substitute a 'dummy' havoc'd variable with
its equality partner from an assume.

Pattern:

    R = havoc                # def
    assume R <= 0x800000     # constraint(s) on R
    ...
    assume X == R            # equality with another symbol
    # R has no other uses

Substituting R -> X everywhere makes R dead (DCE removes the havoc
def) and turns the equality assume into ``assume Eq(X, X)``, which
the companion ``EQ_REFLEXIVE`` rule folds to ``true``; UCE then
removes the no-op assume. Net result: the dummy R is gone, its
constraints attach directly to X.

Conditions for substitution
---------------------------

R is substitutable to X when **all** of:

1. R is DSA-static.
2. R is havoc-defined (no AssignExpCmd RHS).
3. Every use of R is inside an ``AssumeExpCmd`` (no `AssignExpCmd`
   RHS uses, no JumpiCmd condition).
4. R has no weak (annotation) uses — annotations would otherwise
   silently drift after the substitution.
5. Some R-using assume has shape ``Eq(R, X)`` or ``Eq(X, R)`` at
   top-level or inside a top-level ``LAnd`` conjunct, with X a
   ``SymbolRef`` distinct from R.
6. R and X share the same declared sort.

When multiple equalities exist (R == X1 and R == X2), the first
found in walk order wins; the remaining equality becomes
``Eq(X1, X2)`` after substitution — a regular constraint, not a
mistake.

Memoization
-----------

Per-iteration cache attached lazily to ``ctx`` keyed on R's
canonical name. Implicitly reset across rewriter iterations
(``RewriteCtx`` is rebuilt per iter). Cache values include
``None`` for "not substitutable" so we don't re-resolve.

Soundness
---------

R is havoc'd (any value) and constrained `R == X`. Replacing every
R use with X yields the same set of feasible assignments to all
other variables. The havoc def becomes dead; the equality assume
becomes a tautology. No other variables' constraints change.
"""

from __future__ import annotations

from ctac.analysis.symbols import canonical_symbol
from ctac.ast.nodes import ApplyExpr, AssumeExpCmd, SymbolRef, TacExpr
from ctac.rewrite.context import RewriteCtx
from ctac.rewrite.framework import Rule


def _find_eq_partner(expr: TacExpr, R_name: str) -> str | None:
    """Walk top-level + LAnd conjuncts for ``Eq(R, X)`` / ``Eq(X, R)``.

    Returns the partner symbol's full name (with DSA suffix) if found.
    Caller canonicalizes."""
    if not isinstance(expr, ApplyExpr):
        return None
    if expr.op == "Eq" and len(expr.args) == 2:
        a, b = expr.args
        if isinstance(a, SymbolRef) and canonical_symbol(a.name) == R_name and isinstance(b, SymbolRef):
            return b.name
        if isinstance(b, SymbolRef) and canonical_symbol(b.name) == R_name and isinstance(a, SymbolRef):
            return a.name
        return None
    if expr.op == "LAnd":
        for arg in expr.args:
            x = _find_eq_partner(arg, R_name)
            if x is not None:
                return x
    return None


def _is_dummy_havoc(canon: str, ctx: RewriteCtx) -> bool:
    """``canon`` is a "dummy" havoc: static, havoc-defined, with all
    uses inside assumes and no weak (annotation) uses. Used both as
    the gate for R itself and as a cycle-prevention check on R's
    candidate partner X — substituting R -> X when X is also a dummy
    creates an `R <-> X` infinite swap in the rule application loop
    (and is semantically pointless: the dummies just rename each
    other). The substitution should always head toward a real,
    computationally-used variable."""
    if not ctx.is_static(canon):
        return False
    if canon in ctx.static_defs:  # has an AssignExpCmd RHS -> non-dummy
        return False
    uses = ctx.du.uses_by_symbol.get(canon, ())
    if not uses:
        return False
    if any(u.cmd_kind != "AssumeExpCmd" for u in uses):
        return False
    if ctx.du.weak_uses_by_symbol.get(canon, ()):
        return False
    return True


def _x_def_reaches_use(
    x_def_block: str, x_def_cmd_idx: int, use_block: str, use_cmd_idx: int, ctx: RewriteCtx
) -> bool:
    """X's definition reaches a use position iff its def-block
    dominates the use-block (with same-block ordering as a special
    case — def's cmd_index must precede the use's). Required so the
    substitution ``R -> X`` doesn't introduce use-before-def: every
    R use must be reachable from X's def."""
    if x_def_block == use_block:
        return x_def_cmd_idx < use_cmd_idx
    return x_def_block in ctx.dominators.get(use_block, frozenset())


def _resolve_partner(canon_R: str, ctx: RewriteCtx) -> str | None:
    """Decide whether R can be substituted, and if so, return the
    canonical name of its replacement. ``None`` = not substitutable."""
    if not _is_dummy_havoc(canon_R, ctx):
        return None
    by_id = ctx.program.block_by_id()
    R_sort = ctx.symbol_sorts.get(canon_R)
    R_uses = ctx.du.uses_by_symbol.get(canon_R, ())
    for use in R_uses:
        block = by_id.get(use.block_id)
        if block is None:
            continue
        cmd = block.commands[use.cmd_index]
        if not isinstance(cmd, AssumeExpCmd):
            continue
        x_name = _find_eq_partner(cmd.condition, canon_R)
        if x_name is None:
            continue
        x_canon = canonical_symbol(x_name)
        if x_canon == canon_R:
            continue
        if ctx.symbol_sorts.get(x_canon) != R_sort:
            continue
        if _is_dummy_havoc(x_canon, ctx):
            # Both R and X are dummies that mutually equate. Skip;
            # would create an `R <-> X` swap loop in the rule
            # application.
            continue
        # X must be statically reachable: a single def whose position
        # reaches every R-use. Multi-def (DSA-dynamic) X would need
        # the unique-common-successor argument from
        # ``cse-dynamic-free-var-coverage``; we keep this rule simple
        # and bail.
        x_defs = ctx.du.definitions_by_symbol.get(x_canon, ())
        if len(x_defs) != 1:
            continue
        x_def = x_defs[0]
        if not all(
            _x_def_reaches_use(x_def.block_id, x_def.cmd_index, u.block_id, u.cmd_index, ctx)
            for u in R_uses
        ):
            # Substituting R -> X would put X out-of-scope at some
            # R-use site (use-before-def). Skip this candidate.
            continue
        return x_canon
    return None


def _rewrite_havoc_equate(expr: TacExpr, ctx: RewriteCtx) -> TacExpr | None:
    if not isinstance(expr, SymbolRef):
        return None
    canon_R = canonical_symbol(expr.name)
    cache = getattr(ctx, "_he_subst_cache", None)
    if cache is None:
        cache = {}
        ctx._he_subst_cache = cache  # type: ignore[attr-defined]
    if canon_R not in cache:
        cache[canon_R] = _resolve_partner(canon_R, ctx)
    x_canon = cache[canon_R]
    if x_canon is None:
        return None
    # Avoid spurious "fire" when the input SymbolRef is already the
    # partner (e.g., the substituted form survives a re-walk).
    if canonical_symbol(expr.name) == x_canon and expr.name == x_canon:
        return None
    return SymbolRef(x_canon)


HAVOC_EQUATE_SUBST = Rule(
    name="HavocEquateSubst",
    fn=_rewrite_havoc_equate,
    description=(
        "Substitute a static havoc'd R with its equality partner X "
        "when R is used only inside assumes and one of those assumes "
        "has shape Eq(R, X). The havoc def then drops via DCE."
    ),
)
