"""CSE: fold structurally-equal static ``AssignExpCmd`` RHSes into aliases.

For every ``AssignExpCmd X rhs`` whose LHS is DSA-static, find any other
static def ``Y rhs'`` with ``rhs'`` canonically equal to ``rhs``. The
rewrite splits two ways depending on whether Y's def-block dominates X's:

1. **Y dominates X** — emit a plain alias ``X := Y``. CP then propagates
   ``X → Y`` at uses; DCE removes the alias. Smallest diff, easiest to
   eyeball.

2. **Y does not dominate X** — hoist ``TCSE<n> := rhs`` into the entry
   block (which dominates everything), record it in the index so
   subsequent non-dominating uses share the same TCSE, and emit
   ``X := TCSE<n>``. The original ``Y := rhs`` is left untouched —
   it's the orig program's own def, sound in its own scope. The hoist
   is skipped (rule declines) when any free variable of ``rhs`` isn't
   entry-defined: hoisting a computation whose inputs aren't visible
   at the entry block would read undefined values.

**Scope:** fires only when the RHS is a compound expression. Plain
``SymbolRef`` RHS (aliases) are CP's job; ``ConstExpr`` RHS has no
benefit from folding (constants are already canonical).

**Soundness:** Aliases preserve semantics only when the alias source's
def dominates the use; "static" alone (one def site) doesn't imply
that — a symbol can have a single def in block B and a use on a path
that doesn't visit B before the use (e.g. B is a successor of the
use site). Without the dominance split, the rule was unsound on a
real target where a parallel assignment block read a static defined
in a downstream block (rw-eq counterexample:
``B854:0 = Eq(R135, 0)`` got CSE'd to ``B854:0 = B796`` where
``B796 = Eq(R135, 0)`` lived in a successor of the use site; on paths
not yet through B796's def, the read was undefined).

**Naming:** Hoisted defs use the ``TCSE`` prefix so a reader scanning
the rewriter's output can quickly tell which assignments CSE
introduced versus the orig's.

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


def _iter_free_symbols(expr: TacExpr):
    """Yield canonical symbol names referenced in ``expr``. Mirrors
    sea_vc's ``_iter_expr_symbols``: skip ``ApplyExpr``'s args[0] when
    the op is ``Apply`` (that's a function tag, not a program variable)."""
    if isinstance(expr, SymbolRef):
        yield canonical_symbol(expr.name)
        return
    if isinstance(expr, ApplyExpr):
        start_idx = 1 if expr.op == "Apply" and expr.args else 0
        for arg in expr.args[start_idx:]:
            yield from _iter_free_symbols(arg)


def _build_rhs_index(
    ctx: RewriteCtx,
) -> dict[TacExpr, tuple[str, str, TacExpr]]:
    """Map canonicalized static ``AssignExpCmd`` RHS -> (first lhs in
    program order, that def's block id, the original RHS expression).
    The block id drives the dominance split; the original RHS is needed
    to materialize a hoisted ``TCSE<n> := rhs`` in the non-dominating
    case."""
    index: dict[TacExpr, tuple[str, str, TacExpr]] = {}
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
            index.setdefault(_canonical(cmd.rhs), (lhs, block.id, cmd.rhs))
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
    canon = _canonical(expr)
    hit = index.get(canon)
    if hit is None:
        return None
    first_lhs, first_block, first_rhs = hit
    if first_lhs == canonical_symbol(host.lhs):
        return None  # this IS the canonical first definition
    cur_block = ctx._cur_block
    if cur_block is None:
        return None

    # Fast path: the natural alias source dominates the current host.
    # Plain alias, smallest diff. Self-block trivially dominates because
    # ``setdefault`` keeps the FIRST seen RHS in source order, and the
    # walker visits commands in order.
    if first_block == cur_block or first_block in ctx.dominators.get(
        cur_block, frozenset()
    ):
        return SymbolRef(first_lhs)

    # Slow path: alias source is in a non-dominating block. Hoist
    # ``TCSE<n> := first_rhs`` into the entry block — the entry block
    # dominates everywhere, so the hoisted def is visible at every
    # use. Skip when any free variable of ``first_rhs`` isn't
    # entry-defined: we can't hoist a computation whose inputs aren't
    # visible at the entry block insertion point.
    if not all(ctx.is_entry_defined(v) for v in _iter_free_symbols(first_rhs)):
        return None

    # Cache hoisted aliases per RHS so multiple non-dominating uses of
    # the same canonical RHS share one TCSE<n>. The cache is keyed by
    # canonical(rhs); the hoisted assignment becomes the new "natural"
    # source for this canonical RHS within this iteration.
    hoisted = getattr(ctx, "_cse_hoisted", None)
    if hoisted is None:
        hoisted = {}
        ctx._cse_hoisted = hoisted  # type: ignore[attr-defined]
    tx_name = hoisted.get(canon)
    if tx_name is None:
        sort = ctx.symbol_sort(first_lhs)
        if sort is None:
            # No sort info — can't safely emit a fresh assign. Decline
            # rather than guess; CSE will retry next iteration once
            # symbol_sorts is populated, or stay un-rewritten.
            return None
        tx = ctx.emit_fresh_assign(
            prefix="TCSE", rhs=first_rhs, sort=sort, placement="entry"
        )
        tx_name = tx.name
        hoisted[canon] = tx_name
    return SymbolRef(tx_name)


CSE = Rule(
    name="CSE",
    fn=_rewrite_cse,
    description="Fold duplicate static AssignExpCmd X=rhs into an alias of the first such LHS.",
)
