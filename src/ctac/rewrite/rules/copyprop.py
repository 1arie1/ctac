"""Narrow copy propagation.

CP: when a static ``SymbolRef`` X refers to another ``SymbolRef`` Y (i.e. X's
unique definition is ``AssignExpCmd X Y``), rewrite X to Y at its use sites.
Runs alongside the other rules so R1-induced aliases (``R35 = R34``) have
their uses rewired and the now-dead originals become DCE-removable.
"""

from __future__ import annotations

from ctac.ast.nodes import SymbolRef, TacExpr
from ctac.rewrite.context import RewriteCtx
from ctac.rewrite.framework import Rule


def _rewrite_cp(expr: TacExpr, ctx: RewriteCtx) -> TacExpr | None:
    if not isinstance(expr, SymbolRef):
        return None
    d = ctx.definition(expr.name)
    if isinstance(d, SymbolRef):
        return d
    return None


CP_ALIAS = Rule(
    name="CP",
    fn=_rewrite_cp,
    description="Copy propagation: replace SymbolRef X with Y when X's unique definition is Y.",
)
