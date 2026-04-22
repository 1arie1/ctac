"""PURIFY_ASSUME: name non-trivial assume conditions as fresh bool vars.

Parallel to :mod:`ctac.rewrite.rules.purify_assert` but for
``AssumeExpCmd``. For every ``AssumeExpCmd`` whose ``condition`` is
neither a :class:`SymbolRef` nor a :class:`ConstExpr`, emit

    AssignExpCmd TA<N> <condition>
    AssumeExpCmd TA<N>

Shares the ``TA`` prefix with ``PURIFY_ASSERT``: both are named boolean
temporaries for assertion-shaped predicates, and a single counter keeps
the naming stable across the phase.

Default off in ``ctac rw``; ``ctac ua`` keeps its own opt-in.
"""

from __future__ import annotations

from ctac.ast.nodes import AssumeExpCmd, ConstExpr, SymbolRef, TacExpr
from ctac.rewrite.context import RewriteCtx
from ctac.rewrite.framework import Rule


def _rewrite_purify_assume(expr: TacExpr, ctx: RewriteCtx) -> TacExpr | None:
    if not ctx.at_cmd_top():
        return None
    if not isinstance(ctx.current_cmd(), AssumeExpCmd):
        return None
    if isinstance(expr, (SymbolRef, ConstExpr)):
        return None
    return ctx.emit_fresh_assign(prefix="TA", rhs=expr, sort="bool")


PURIFY_ASSUME = Rule(
    name="PURIFY_ASSUME",
    fn=_rewrite_purify_assume,
    description="Name each non-trivial AssumeExpCmd condition as a fresh bool var TA<N>.",
)
