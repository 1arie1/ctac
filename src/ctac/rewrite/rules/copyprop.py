"""Narrow copy / constant propagation.

CP: when a static ``SymbolRef`` X has a unique ``AssignExpCmd`` definition
whose RHS is itself a ``SymbolRef`` Y or a ``ConstExpr`` c, rewrite X to Y
or c at its use sites. Runs alongside the other simplification rules so
R1-induced aliases (``R35 = R34``) and constant defs (``R2063 =
0x300000538`` produced by CFG-edit specialize, by chain recognition, by
RangeFold's compound-only folding, etc.) flow through to use sites and
the now-dead originals become DCE-removable.

Soundness:
* SymRef -> SymRef: replacing X by Y is safe because Y dominates X's
  unique def (Y was its RHS), and X's def dominates every use of X.
* SymRef -> ConstExpr: strictly safer in the dominance dimension —
  constants are universally available.

Snapshot-safety: this rule mutates RHSes of expressions it touches, so
must run in a phase that does not also contain CSE (whose RHS index
is taken once per iteration). The driver pipeline already isolates
CSE in its own phase; CP_ALIAS lives in ``simplify_pipeline``.
"""

from __future__ import annotations

from ctac.ast.nodes import ConstExpr, SymbolRef, TacExpr
from ctac.rewrite.context import RewriteCtx
from ctac.rewrite.framework import Rule


def _rewrite_cp(expr: TacExpr, ctx: RewriteCtx) -> TacExpr | None:
    if not isinstance(expr, SymbolRef):
        return None
    d = ctx.definition(expr.name)
    if isinstance(d, (SymbolRef, ConstExpr)):
        return d
    return None


CP_ALIAS = Rule(
    name="CP",
    fn=_rewrite_cp,
    description=(
        "Copy / constant propagation: replace SymbolRef X with its "
        "unique definition's RHS when that RHS is a SymbolRef or a "
        "ConstExpr."
    ),
)
