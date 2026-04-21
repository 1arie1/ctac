"""ITE_PURIFY: name non-trivial Ite conditions as fresh bool variables.

For every ``Ite(cond, then, else)`` whose ``cond`` is neither a
:class:`SymbolRef` nor a :class:`ConstExpr`, emit

    AssignExpCmd TB<N> <cond>
    ... Ite(SymbolRef("TB<N>"), then, else) ...

The aim is to give solvers named boolean handles they can case-split on
without having to interpret compound condition expressions each time.
Downstream SMT emission is free to inline these definitions if that's
cheaper for its solver.

**Ordering:** this rule is intentionally *not* part of
``simplify_pipeline``. It runs as a final phase after DCE so that the
existing Ite rules (IteBool / IteSame / EqIte / BoolAbsorb / DeMorgan)
get first crack at any Ite they can collapse — otherwise we would name
conditions that are about to be eliminated.
"""

from __future__ import annotations

from ctac.ast.nodes import ApplyExpr, ConstExpr, SymbolRef, TacExpr
from ctac.rewrite.context import RewriteCtx
from ctac.rewrite.framework import Rule


def _rewrite_ite_purify(expr: TacExpr, ctx: RewriteCtx) -> TacExpr | None:
    if not (isinstance(expr, ApplyExpr) and expr.op == "Ite" and len(expr.args) == 3):
        return None
    cond, then_branch, else_branch = expr.args
    # Already a named bool (SymbolRef) or a trivial literal — nothing to do.
    if isinstance(cond, (SymbolRef, ConstExpr)):
        return None
    tb = ctx.emit_fresh_assign(prefix="TB", rhs=cond, sort="bool")
    return ApplyExpr("Ite", (tb, then_branch, else_branch))


ITE_PURIFY = Rule(
    name="ITE_PURIFY",
    fn=_rewrite_ite_purify,
    description="Name each non-trivial Ite condition as a fresh bool var TB<N>.",
)
