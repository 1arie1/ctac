"""PURIFY_ASSERT: name non-trivial assertion predicates as fresh bool vars.

For every ``AssertCmd`` whose ``predicate`` is neither a :class:`SymbolRef`
nor a :class:`ConstExpr`, emit

    AssignExpCmd TA<N> <predicate>
    AssertCmd TA<N>

so downstream consumers (SMT encoders, the ``ctac ua`` assert-merging
strategies) see every assertion as a named boolean handle. Only fires at
the host command's top-level expression — nested expressions inside the
predicate are handled by the other purification rules (notably
``ITE_PURIFY``).
"""

from __future__ import annotations

from ctac.ast.nodes import AssertCmd, ConstExpr, SymbolRef, TacExpr
from ctac.rewrite.context import RewriteCtx
from ctac.rewrite.framework import Rule


def _rewrite_purify_assert(expr: TacExpr, ctx: RewriteCtx) -> TacExpr | None:
    if not ctx.at_cmd_top():
        return None
    if not isinstance(ctx.current_cmd(), AssertCmd):
        return None
    if isinstance(expr, (SymbolRef, ConstExpr)):
        return None
    return ctx.emit_fresh_assign(prefix="TA", rhs=expr, sort="bool")


PURIFY_ASSERT = Rule(
    name="PURIFY_ASSERT",
    fn=_rewrite_purify_assert,
    description="Name each non-trivial AssertCmd predicate as a fresh bool var TA<N>.",
)
