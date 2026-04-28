"""ITE_PURIFY: name non-trivial Ite conditions as fresh bool variables.

For every ``Ite(cond, then, else)`` whose ``cond`` is neither a
:class:`SymbolRef` nor a :class:`ConstExpr`, emit

    AssignExpCmd TB<N> <cond>
    ... Ite(SymbolRef("TB<N>"), then, else) ...

The aim is to give solvers named boolean handles they can case-split on
without having to interpret compound condition expressions each time.
Downstream SMT emission is free to inline these definitions if that's
cheaper for its solver.

**Placement:** the TB-def must dominate the use **and** sit in the
DSA-static prefix of its host block (sea_vc requires
``(static)*(dynamic)*terminator`` per block). We insert TB just
before the current Ite use site (``placement="current"``), which is
sound and shape-valid as long as no DSA-dynamic def already precedes
the use in the same block. When such a dynamic def exists, the TB
(static, single-def) would land between two dynamics and break the
shape; in that case we **skip** the rewrite for this Ite rather than
silently producing a TAC the encoder rejects. (Hoisting to entry is
not generally safe either: cond's operands may not all be visible at
entry, and uses inside the entry block would violate use-before-def.)

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
    # Skip if a DSA-dynamic def already precedes the current cmd in
    # this block: inserting a static TB-def at ``current`` would land
    # between two dynamics and violate ``(static)*(dynamic)*term``.
    cur_block = ctx._cur_block
    cur_cmd = ctx._cur_cmd
    if cur_block is not None and cur_cmd is not None:
        for dyn in ctx.dsa.dynamic_assignments:
            if dyn.block_id == cur_block and dyn.cmd_index < cur_cmd:
                ctx.warnings.append(
                    f"ITE_PURIFY: skipped Ite at {cur_block}:{cur_cmd} "
                    f"— DSA-dynamic def at {dyn.block_id}:{dyn.cmd_index} "
                    "precedes the use; inserting a TB-def at current "
                    "would violate (static)*(dynamic)*term shape"
                )
                return None
    tb = ctx.emit_fresh_assign(prefix="TB", rhs=cond, sort="bool")
    return ApplyExpr("Ite", (tb, then_branch, else_branch))


ITE_PURIFY = Rule(
    name="ITE_PURIFY",
    fn=_rewrite_ite_purify,
    description="Name each non-trivial Ite condition as a fresh bool var TB<N>.",
)
