"""CSE: fold structurally-equal static ``AssignExpCmd`` RHSes into aliases.

For every ``AssignExpCmd X rhs`` whose LHS is DSA-static, find any other
static def ``Y rhs'`` with ``rhs'`` canonically equal to ``rhs``. The
rewrite splits two ways depending on whether Y's def-block dominates X's:

1. **Y dominates X** — emit a plain alias ``X := Y``. CP then propagates
   ``X → Y`` at uses; DCE removes the alias. Smallest diff, easiest to
   eyeball.

2. **Y does not dominate X** — hoist ``TCSE<n> := rhs`` into the
   *deepest common dominator* of every use site of ``rhs`` (the
   block where TCSE is visible to every CSE-replaceable site).
   Record the TCSE so subsequent non-dominating uses share it, and
   emit ``X := TCSE<n>`` at the original use site. The original
   ``Y := rhs`` is left untouched. The hoist is skipped (rule
   declines) when any free variable of ``rhs`` has a definition that
   doesn't dominate the chosen target block: hoisting a computation
   whose inputs aren't visible there would read undefined values.

   Note: when the deepest common dominator is the entry block
   (because uses live on disjoint branches of an early fork), this
   degenerates to the entry-block hoist that earlier versions
   always performed. The common-dominator generalization simply
   accepts more cases without forcing entry placement.

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

**Placement:** runs in its own dedicated phases, never alongside
rules that mutate registered RHSes. The CLI driver runs CSE early
(after chain recognition, to catch input-level duplicates before
simplification reshapes their structure) and late (after ITE_PURIFY
etc., to fold the structurally-equal ``T<N>`` defs those rules
emit). Isolation is load-bearing: CSE's RHS index is built once per
iteration; if a rule alongside it (CP, range fold, bit-op canon,
...) rewrites a registered RHS mid-iter, canon equivalence shifts
under the snapshot. With CSE alone in its phase, the snapshot is a
real invariant.
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
) -> dict[TacExpr, tuple[str, str, TacExpr, frozenset[str]]]:
    """Map canonicalized static ``AssignExpCmd`` RHS -> (canonical lhs,
    that def's block id, the original RHS expression, set of block
    ids where the canonical RHS appears as a static def).

    Canonical-first-def selection is **dominance-preferring**: when
    multiple static defs share a canonical RHS, we keep the one whose
    block dominates as many of the others as possible. Concretely, as
    we walk in file order, a later def replaces the existing first
    iff its block strictly dominates the existing first's block. This
    is the right choice because the fast path returns
    ``SymbolRef(first_lhs)`` — for that to be in scope at any other
    use site, ``first_block`` must dominate the use, and the
    deepest-up dominator covers the most uses.

    Without dominance preference (file-order ``setdefault``), a
    hoisted ``TCSE`` placed in an upstream block can fail to absorb
    its file-order-earlier-but-CFG-later sibling: the upstream
    ``TCSE`` would be the dominating def we want to alias to, but the
    downstream original keeps the canonical seat and stays
    un-aliased. That stalls multi-iteration CSE cascades through
    Store chains hoisted on dynamic bases (the motivating case:
    request_elevation_group/base.rw.tac).

    The first three drive the dominance split / TCSE construction;
    the use-block set lets the slow path compute the deepest common
    dominator instead of forcing the hoist into entry."""
    first: dict[TacExpr, tuple[str, str, TacExpr]] = {}
    use_blocks: dict[TacExpr, set[str]] = {}
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
            canon = _canonical(cmd.rhs)
            existing = first.get(canon)
            if existing is None:
                first[canon] = (lhs, block.id, cmd.rhs)
            else:
                ex_block = existing[1]
                if block.id != ex_block and block.id in ctx.dominators.get(
                    ex_block, frozenset()
                ):
                    first[canon] = (lhs, block.id, cmd.rhs)
            use_blocks.setdefault(canon, set()).add(block.id)
    return {k: (*first[k], frozenset(use_blocks[k])) for k in first}


def _deepest_common_strict_dominator(
    use_blocks: "frozenset[str] | set[str]", ctx: RewriteCtx
) -> str | None:
    """Return the deepest block that *strictly* dominates every block
    in ``use_blocks``. A block does not strictly dominate itself, so
    the result is never in ``use_blocks``.

    The strictness matters for hoisting: if the result were a use
    block X, the def would land at end of X (just before X's
    terminator), but uses earlier in X would read the symbol before
    its def — use-before-def. Restricting to strict dominators
    guarantees the def's block is positionally above every use.

    Returns ``None`` if no strict common dominator exists (e.g. when
    ``use_blocks == {entry}`` since entry has no strict dominators)."""
    if not use_blocks:
        return None
    common: set[str] | None = None
    for b in use_blocks:
        # Strip the block itself from its dominator set to get proper
        # dominators (those that are above ``b`` in the dom tree).
        proper = ctx.dominators.get(b, frozenset()) - {b}
        if common is None:
            common = set(proper)
        else:
            common &= proper
    if not common:
        return None
    # Domination is a tree; the intersection is a chain. The deepest
    # element has the largest dominator set (deeper = more ancestors).
    return max(common, key=lambda c: len(ctx.dominators.get(c, frozenset())))


def _effective_def_block_for_dominance(
    var_name: str, ctx: RewriteCtx
) -> str | None:
    """Return the block whose dominance over a target captures
    "every entry→target path passes through some def of ``var_name``".

    * Single def → that def's block. Single-def coverage is just
      single-block dominance, so the existing per-def check is
      already correct.

    * Multi-def (DSA-dynamic by ``analyze_dsa``'s definition: every
      def in a different block, all those blocks sharing the same
      single successor) → the unique common successor ``J`` of the
      def-blocks. Under that invariant, ``J`` postdominates the def
      set: every entry→target path that crosses ``J`` necessarily
      passes through one of the def blocks. So ``J`` dominating
      ``target`` ⇔ the def-set collectively covers every path to
      ``target`` — which is the actual safety condition for the
      hoist.

    * Multi-def with no unique common successor → ``None`` (decline).
      That shape isn't DSA-valid; we can't certify coverage from
      one-step lookahead.
    """
    canonical = canonical_symbol(var_name)
    defs = ctx.du.definitions_by_symbol.get(canonical, ())
    if not defs:
        return None
    if len(defs) == 1:
        return defs[0].block_id
    common: set[str] | None = None
    for ds in defs:
        succs = set(ctx.successors_of(ds.block_id))
        common = succs if common is None else common & succs
    if not common or len(common) != 1:
        return None
    (j,) = common
    return j


def _all_defs_dominate(
    var_name: str, target_block: str, ctx: RewriteCtx
) -> bool:
    """True iff some def-coverage of ``var_name`` lies on every path
    to ``target_block`` — see ``_effective_def_block_for_dominance``
    for the static (single-def) and DSA-dynamic (multi-def) cases.

    Required for hoisting a TCSE into ``target_block`` whose RHS
    references ``var_name``: without coverage, the hoisted def would
    read a variable not yet defined on some path to ``target_block``.
    """
    eff = _effective_def_block_for_dominance(var_name, ctx)
    if eff is None:
        return False
    return eff in ctx.dominators.get(target_block, frozenset())


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
    first_lhs, first_block, first_rhs, use_blocks = hit
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
    # ``TCSE<n> := first_rhs`` to the *deepest STRICT common dominator*
    # of all use sites — a block that dominates every use site and is
    # not itself a use site. Strictness matters: the def lands at the
    # end of the chosen block (just before its terminator), and if
    # the chosen block were one of the use sites, uses earlier in
    # that block would read the TCSE before its def — use-before-def.
    #
    # Constraints on the target:
    # - must strictly dominate every use site (visibility +
    #   positional ordering);
    # - every free var of ``first_rhs`` must be defined in the
    #   target itself or in a block dominating the target (so the
    #   TCSE's RHS is well-formed under def-use).
    # The use-block set is computed once per iteration from program state at
    # iter start. ``cur_block`` may not be in it because its RHS only became
    # canonically equal to ``first_rhs`` after subexpression rewrites (e.g.
    # CP propagated B217 -> TCSE21 earlier in this same iteration). Include
    # ``cur_block`` explicitly so the strict-common-dominator computation
    # accounts for the use site we're actually rewriting.
    effective_uses = set(use_blocks) | {cur_block}
    target_block = _deepest_common_strict_dominator(effective_uses, ctx)
    if target_block is None:
        return None
    if not all(
        _all_defs_dominate(v, target_block, ctx)
        for v in _iter_free_symbols(first_rhs)
    ):
        return None

    # Cache hoisted aliases per RHS so multiple non-dominating uses of
    # the same canonical RHS share one TCSE<n>. The cache is keyed by
    # canonical(rhs); the value carries (tx_name, def_block) so a later
    # cur_block in the same iteration that wasn't part of the cache's
    # target computation can be checked against the existing def block.
    hoisted = getattr(ctx, "_cse_hoisted", None)
    if hoisted is None:
        hoisted = {}
        ctx._cse_hoisted = hoisted  # type: ignore[attr-defined]
    cached = hoisted.get(canon)
    if cached is not None:
        tx_name, cached_def_block = cached
        # The TCSE was emitted earlier this iteration at ``cached_def_block``.
        # Reuse only if that block strictly dominates this cur_block; else
        # decline rather than introduce use-before-def.
        if cached_def_block not in (
            ctx.dominators.get(cur_block, frozenset()) - {cur_block}
        ):
            return None
        return SymbolRef(tx_name)
    sort = ctx.symbol_sort(first_lhs)
    if sort is None:
        # No sort info — can't safely emit a fresh assign. Decline
        # rather than guess; CSE will retry next iteration once
        # symbol_sorts is populated, or stay un-rewritten.
        return None
    tx = ctx.emit_fresh_assign(
        prefix="TCSE",
        rhs=first_rhs,
        sort=sort,
        placement="block_end",
        block_id=target_block,
    )
    hoisted[canon] = (tx.name, target_block)
    return SymbolRef(tx.name)


CSE = Rule(
    name="CSE",
    fn=_rewrite_cse,
    description="Fold duplicate static AssignExpCmd X=rhs into an alias of the first such LHS.",
)
