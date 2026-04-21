"""CSE: fold structurally-equal static ``AssignExpCmd`` RHSes into aliases.

For every ``AssignExpCmd X rhs`` whose LHS is DSA-static, if some earlier
``AssignExpCmd Y rhs'`` exists with ``Y`` also static and ``rhs'``
structurally equal to ``rhs`` (modulo DSA meta-suffixes on SymbolRefs),
rewrite to ``AssignExpCmd X Y`` — a pure alias. CP then propagates ``X``
to ``Y`` at uses, and DCE removes the alias.

**Scope:** we fire only when the RHS is a compound expression. Plain
``SymbolRef`` RHS (aliases) are CP's job; ``ConstExpr`` RHS has no
benefit from folding (constants are already canonical).

**Soundness:** DSA-static defs have unique, dominating definitions. If
two static defs have the same RHS, they compute the same value — the
alias preserves semantics.

**Placement:** runs both in ``simplify_pipeline`` (picks up duplicates
the input already has) and alongside ``ITE_PURIFY`` in the post-DCE
phase (picks up duplicates that ITE_PURIFY itself just created by
naming identical Ite conditions twice).
"""

from __future__ import annotations

from ctac.analysis.symbols import canonical_symbol
from ctac.ast.nodes import ApplyExpr, AssignExpCmd, ConstExpr, SymbolRef, TacExpr
from ctac.rewrite.context import RewriteCtx
from ctac.rewrite.framework import Rule


def _canonical(expr: TacExpr) -> TacExpr:
    """Strip DSA meta-suffixes (``:N``) from ``SymbolRef`` names recursively.

    Two RHS trees are considered equal under CSE if their canonical forms
    compare equal — so ``Lt(R0, X)`` matches ``Lt(R0:3, X)``.
    """
    if isinstance(expr, SymbolRef):
        return SymbolRef(canonical_symbol(expr.name))
    if isinstance(expr, ApplyExpr):
        return ApplyExpr(expr.op, tuple(_canonical(a) for a in expr.args))
    return expr


def _build_rhs_index(ctx: RewriteCtx) -> dict[TacExpr, str]:
    """Map canonicalized static ``AssignExpCmd`` RHS -> first LHS in program order."""
    index: dict[TacExpr, str] = {}
    for block in ctx.program.blocks:
        for cmd in block.commands:
            if not isinstance(cmd, AssignExpCmd):
                continue
            # Skip plain aliases (CP's job) and trivial constants.
            if isinstance(cmd.rhs, (SymbolRef, ConstExpr)):
                continue
            lhs = canonical_symbol(cmd.lhs)
            if lhs not in ctx.static_symbols:
                continue
            index.setdefault(_canonical(cmd.rhs), lhs)
    return index


def _rewrite_cse(expr: TacExpr, ctx: RewriteCtx) -> TacExpr | None:
    host = ctx.current_cmd()
    if not (ctx.at_cmd_top() and isinstance(host, AssignExpCmd)):
        return None
    # Skip if the RHS is already trivial (alias / const).
    if isinstance(expr, (SymbolRef, ConstExpr)):
        return None
    if not ctx.is_static(host.lhs):
        return None
    # Cache the RHS index on the ctx (built lazily; one build per iteration).
    index = getattr(ctx, "_cse_rhs_index", None)
    if index is None:
        index = _build_rhs_index(ctx)
        ctx._cse_rhs_index = index  # type: ignore[attr-defined]
    first_lhs = index.get(_canonical(expr))
    if first_lhs is None:
        return None
    if first_lhs == canonical_symbol(host.lhs):
        return None  # this IS the canonical first definition
    return SymbolRef(first_lhs)


CSE = Rule(
    name="CSE",
    fn=_rewrite_cse,
    description="Fold duplicate static AssignExpCmd X=rhs into an alias of the first such LHS.",
)
