"""HAVOC_EQUATE_FOLD: drop a 'dummy' havoc + its constraints by
moving them onto its equality partner at the equality's position.

Sister to ``HAVOC_EQUATE_SUBST``. Where SUBST rewrites every
R-reference to X (which only works when X's def reaches every
R-use, including ones earlier in cmd order), FOLD instead **drops
R entirely** and rewrites the equality assume's condition to a
conjunction of the constraints originally on R, with R -> X
substituted. Useful when X is defined *later* than R and forward
substitution would create use-before-def — the SBF frontend's
"pre-allocate slot R, then later equate to actual nondet result X"
shape.

Pattern:

    block A:
      R = havoc                  # def
      assume Le(R, c)            # constraint(s) on R
      ...
      X = nondet_call_result     # X defined later, in same block
      ...
      assume Eq(R, X)            # equality

becomes:

    block A:
      X = nondet_call_result     # X stays
      assume Le(X, c)            # was Eq(R, X); now the moved constraint
      # R = havoc dropped, Le(R, c) dropped, Eq(R, X) replaced

Soundness gate
--------------

The rule fires only when **R's def, R's other-use assumes (the
constraints), and the host equality assume are ALL in the same
block**. Single-block confines the rewrite to one linear path: the
constraints were asserted on every flow that reached the Eq, so
moving them to the Eq's position re-asserts the same fact at the
same point of every relevant trace. Sibling-block configurations
(e.g. R def in A; constraint in B; Eq in C with C reachable from
both B and a non-B sibling) would over-constrain X on the non-B
path and are explicitly skipped.

Conditions
----------

1. The host cmd is an ``AssumeExpCmd`` whose **top-level** condition
   is ``Eq(R, X)`` or ``Eq(X, R)``. Not inside an ``LAnd``.
2. R is a "dummy havoc" (existing ``_is_dummy_havoc`` from
   ``havoc_equate_subst``): static, havoc-defined, all uses in
   assumes, no weak (annotation) refs.
3. X is **not** a dummy (avoids R<->X cycles via the same logic
   as SUBST).
4. R and X share the same declared sort.
5. R has at least one constraint assume **other than** the host
   equality. Otherwise there's nothing to move; let UCE / DCE
   handle the empty case.
6. R's havoc def + each constraint assume is in the **same block**
   as the host equality assume.

Effect
------

* Build new condition = ``LAnd`` of all constraint assume
  conditions, each with R -> X substituted.
* Skip R's havoc def cmd.
* Skip each constraint assume's cmd.
* Return the new condition (replaces the host Eq's condition
  in-place).

Subsequent passes:

* DCE removes R's havoc def from the program (already marked skip).
* The other R-using assumes are also dropped via the skip set.
* If any of the original constraints was already true on X
  independently, ``RANGE_FOLD`` / ``EQ_REFLEXIVE`` may further
  simplify the new ``LAnd``.
"""

from __future__ import annotations

from ctac.analysis.symbols import canonical_symbol
from ctac.ast.nodes import ApplyExpr, AssumeExpCmd, SymbolRef, TacExpr
from ctac.rewrite.context import RewriteCtx
from ctac.rewrite.framework import Rule
from ctac.rewrite.rules.havoc_equate_subst import _is_dummy_havoc


def _subst_canon(expr: TacExpr, old_canon: str, new_canon: str) -> TacExpr:
    """Replace every ``SymbolRef`` whose canonical name equals
    ``old_canon`` with ``SymbolRef(new_canon)``. Recurses through
    ``ApplyExpr``. Preserves all other node types unchanged."""
    if isinstance(expr, SymbolRef):
        if canonical_symbol(expr.name) == old_canon:
            return SymbolRef(new_canon)
        return expr
    if isinstance(expr, ApplyExpr):
        new_args = tuple(_subst_canon(a, old_canon, new_canon) for a in expr.args)
        if all(a is b for a, b in zip(new_args, expr.args)):
            return expr
        return ApplyExpr(expr.op, new_args)
    return expr


def _try_fold(
    canon_R: str, canon_X: str, host_block: str, host_cmd_idx: int, ctx: RewriteCtx
) -> TacExpr | None:
    """Attempt the fold for one direction (R, X). Returns the new
    Eq-replacement condition on success, or ``None`` if any gate
    fails."""
    if canon_R == canon_X:
        return None
    if not _is_dummy_havoc(canon_R, ctx):
        return None
    if _is_dummy_havoc(canon_X, ctx):
        return None
    if ctx.symbol_sorts.get(canon_X) != ctx.symbol_sorts.get(canon_R):
        return None

    # R's havoc def must be in the same block as the host Eq.
    r_defs = ctx.du.definitions_by_symbol.get(canon_R, ())
    if len(r_defs) != 1 or r_defs[0].block_id != host_block:
        return None

    # Every R-using cmd OTHER than the host Eq must be in the same
    # block as the host. Collect their conditions for moving.
    by_id = ctx.program.block_by_id()
    constraint_conds: list[TacExpr] = []
    constraint_positions: list[tuple[str, int]] = []
    for use in ctx.du.uses_by_symbol.get(canon_R, ()):
        if use.block_id == host_block and use.cmd_index == host_cmd_idx:
            continue  # the host equality itself
        if use.block_id != host_block:
            return None  # cross-block constraint — bail (path conditional)
        block = by_id.get(use.block_id)
        if block is None:
            return None
        cmd = block.commands[use.cmd_index]
        if not isinstance(cmd, AssumeExpCmd):
            # _is_dummy_havoc already guaranteed all uses are
            # AssumeExpCmd, but defensive belt-and-braces.
            return None
        moved = _subst_canon(cmd.condition, canon_R, canon_X)
        constraint_conds.append(moved)
        constraint_positions.append((use.block_id, use.cmd_index))

    if not constraint_conds:
        # No constraints to move — bail (per spec).
        return None

    # Build new condition: LAnd-conjunction of all moved constraints.
    new_cond: TacExpr = constraint_conds[0]
    for c in constraint_conds[1:]:
        new_cond = ApplyExpr("LAnd", (new_cond, c))

    # Drop R's havoc def + each constraint assume.
    for d in r_defs:
        ctx.skip_cmd_at(d.block_id, d.cmd_index)
    for pos in constraint_positions:
        ctx.skip_cmd_at(*pos)

    return new_cond


def _rewrite_havoc_equate_fold(expr: TacExpr, ctx: RewriteCtx) -> TacExpr | None:
    # Only fire at top-level Eq(_, _) inside an AssumeExpCmd condition.
    host = ctx.current_cmd()
    if not (ctx.at_cmd_top() and isinstance(host, AssumeExpCmd)):
        return None
    if not (isinstance(expr, ApplyExpr) and expr.op == "Eq" and len(expr.args) == 2):
        return None
    a, b = expr.args
    if not (isinstance(a, SymbolRef) and isinstance(b, SymbolRef)):
        return None
    if ctx._cur_block is None or ctx._cur_cmd is None:
        return None
    cur_block = ctx._cur_block
    cur_cmd = ctx._cur_cmd

    canon_a = canonical_symbol(a.name)
    canon_b = canonical_symbol(b.name)
    # Try R=a/X=b first; then swap. The first successful fold wins.
    result = _try_fold(canon_a, canon_b, cur_block, cur_cmd, ctx)
    if result is not None:
        return result
    return _try_fold(canon_b, canon_a, cur_block, cur_cmd, ctx)


HAVOC_EQUATE_FOLD = Rule(
    name="HavocEquateFold",
    fn=_rewrite_havoc_equate_fold,
    description=(
        "Drop a static havoc'd dummy R whose only uses are constraint "
        "assumes + an Eq(R, X) all in the same block: rewrite the Eq "
        "to LAnd of R's constraints (substituted to X), drop R's "
        "havoc def + the original constraint assumes."
    ),
)
