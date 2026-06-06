"""Materialize bounds across an ``Eq(R, X)`` from a havoc'd R onto X.

Pattern (the SBF frontend's "pre-allocate slot R, later equate to actual
nondet result X" shape):

    R = havoc                # static AssignHavocCmd
    assume Le(R, K)          # constraint(s) on R
    ...
    X = <expr>               # X defined later, in same block
    assume Eq(R, X)          # equality

This pass walks the program and, for each such triple, inserts the
substituted constraint as a new RHS-only assume immediately AFTER the
equality:

    assume Eq(R, X)
    assume Le(X, K)          # ← materialized

Why this shape (not the more aggressive ``HAVOC_EQUATE_FOLD`` that
drops R and its constraints): rw-eq, the soundness gate, walks LHS
and RHS in source order and pairs cmds per position. Dropping LHS
cmds and replacing them with a single moved cmd on the RHS forces
rw-eq's walker to emit an lhs-only-assume CHK that can't discharge
without the dropped cmds back in scope — a known walker limitation
analogous to rule 6 (rehavoc). Adding a *new* RHS-only assume,
in contrast, lands on rw-eq's rule 4 (rhs-only-assume) which emits
a CHK = ``Le(X, K)`` at the materialization position; ``Eq(R, X)``
is already an assume in scope at that point, so the CHK trivially
discharges via ``R == X ∧ Le(R, K) ⇒ Le(X, K)``. Both LHS and RHS
contain every original cmd, just the RHS has one more.

Pass placement: runs ONCE, before the simplify pipeline, so the
materialized assume is visible to range inference and downstream
rewrites. Idempotent: skipped per-Eq if the substituted assume
already exists in the same block.

Gates
-----

For each ``AssumeExpCmd Eq(R, X)`` (top-level, both args
``SymbolRef``):

1. R is DSA-static and havoc-defined (single ``AssignHavocCmd R``).
2. R has at least one other use that is an ``AssumeExpCmd``
   constraining R (i.e. a different assume than the host Eq).
3. X is a SymbolRef distinct from R.
4. R and X share declared sort.

For each candidate constraint assume on R (other than the host Eq),
substitute R -> X in the condition and insert the result after the
host Eq — unless an identical assume already follows the host.
"""

from __future__ import annotations

from dataclasses import dataclass, replace

from ctac.analysis.symbols import canonical_symbol
from ctac.ast.nodes import (
    ApplyExpr,
    AssignHavocCmd,
    AssumeExpCmd,
    SymbolRef,
    TacCmd,
    TacExpr,
)
from ctac.ir.models import TacBlock, TacProgram
from ctac.rewrite.unparse import canonicalize_cmd


@dataclass(frozen=True)
class MaterializeEquateBoundsResult:
    """Outcome of :func:`materialize_havoc_equate_bounds`."""

    program: TacProgram
    hits: int


def _subst_symbol(expr: TacExpr, old_canon: str, new_name: str) -> TacExpr:
    """Replace every ``SymbolRef`` whose canonical name equals
    ``old_canon`` with ``SymbolRef(new_name)``."""
    if isinstance(expr, SymbolRef):
        if canonical_symbol(expr.name) == old_canon:
            return SymbolRef(new_name)
        return expr
    if isinstance(expr, ApplyExpr):
        new_args = tuple(_subst_symbol(a, old_canon, new_name) for a in expr.args)
        if all(a is b for a, b in zip(new_args, expr.args)):
            return expr
        return ApplyExpr(expr.op, new_args)
    return expr


def _is_top_level_eq_of_symrefs(
    cond: TacExpr,
) -> tuple[str, str] | None:
    """Return the canonical names of (R, X) if cond is ``Eq(R, X)``
    with both args ``SymbolRef``; else None."""
    if not (
        isinstance(cond, ApplyExpr)
        and cond.op == "Eq"
        and len(cond.args) == 2
    ):
        return None
    a, b = cond.args
    if not (isinstance(a, SymbolRef) and isinstance(b, SymbolRef)):
        return None
    return canonical_symbol(a.name), canonical_symbol(b.name)


def materialize_havoc_equate_bounds(
    program: TacProgram,
    *,
    symbol_sorts: dict[str, str] | None = None,
) -> MaterializeEquateBoundsResult:
    """Walk the program once and, for each ``assume Eq(R, X)`` where R
    is a havoc'd symbol with bound assumes, insert the substituted
    bound onto X right after the equality.

    Pure structural transform: no rule iteration, no fixed point. The
    intent is to make implicit knowledge explicit so the rewrite
    simplify pipeline (and the downstream encoder) can use it.
    """
    symbol_sorts = symbol_sorts or {}

    # Build (canonical name) -> AssignHavocCmd position. A symbol with
    # any non-havoc def is excluded; we only materialize from pure
    # havoc'd sources.
    havoc_def_by_sym: dict[str, tuple[str, int]] = {}
    any_other_def_by_sym: set[str] = set()
    for block in program.blocks:
        for idx, cmd in enumerate(block.commands):
            if isinstance(cmd, AssignHavocCmd):
                canon = canonical_symbol(cmd.lhs)
                if canon in havoc_def_by_sym or canon in any_other_def_by_sym:
                    any_other_def_by_sym.add(canon)
                else:
                    havoc_def_by_sym[canon] = (block.id, idx)
            elif hasattr(cmd, "lhs") and isinstance(cmd.lhs, str):
                # AssignExpCmd (or anything else with an lhs attribute).
                canon = canonical_symbol(cmd.lhs)
                any_other_def_by_sym.add(canon)
                havoc_def_by_sym.pop(canon, None)
    pure_havocs = {
        canon: pos
        for canon, pos in havoc_def_by_sym.items()
        if canon not in any_other_def_by_sym
    }
    if not pure_havocs:
        return MaterializeEquateBoundsResult(program=program, hits=0)

    # For each pure-havoc symbol, collect AssumeExpCmd commands that
    # constrain it, keyed with their position. Constraint = any
    # AssumeExpCmd whose condition references the symbol but is NOT
    # itself a top-level ``Eq(R, X)``. Position matters: a constraint
    # assume is path-conditional, so it may only be materialized at an
    # Eq site it already dominates trivially — same block, earlier
    # index. Materializing a downstream constraint upstream prunes
    # executions that never reach the source assume (masking
    # counterexamples) and may reference symbols with no def yet.
    constraints_by_sym: dict[str, list[tuple[str, int, TacExpr]]] = {}
    for block in program.blocks:
        for cidx, cmd in enumerate(block.commands):
            if not isinstance(cmd, AssumeExpCmd):
                continue
            if _is_top_level_eq_of_symrefs(cmd.condition) is not None:
                continue
            for canon in _referenced_symbols(cmd.condition):
                if canon in pure_havocs:
                    constraints_by_sym.setdefault(canon, []).append(
                        (block.id, cidx, cmd.condition)
                    )

    if not constraints_by_sym:
        return MaterializeEquateBoundsResult(program=program, hits=0)

    # Pass 2: find each top-level Eq(R, X) assume and queue
    # materialized assumes (one per R-constraint) at the equality's
    # position+1, deduping against existing AssumeExpCmds in the
    # surrounding block.
    insertions: dict[tuple[str, int], list[TacCmd]] = {}
    hits = 0
    for block in program.blocks:
        existing_assume_conds = {
            cmd.condition
            for cmd in block.commands
            if isinstance(cmd, AssumeExpCmd)
        }
        for idx, cmd in enumerate(block.commands):
            if not isinstance(cmd, AssumeExpCmd):
                continue
            eq_pair = _is_top_level_eq_of_symrefs(cmd.condition)
            if eq_pair is None:
                continue
            r_canon, x_canon = eq_pair
            # Try both orientations: (R, X) and (X, R).
            for src_canon, tgt_canon in ((r_canon, x_canon), (x_canon, r_canon)):
                if src_canon == tgt_canon:
                    continue
                if src_canon not in pure_havocs:
                    continue
                if symbol_sorts.get(src_canon) != symbol_sorts.get(tgt_canon):
                    continue
                for src_block_id, src_idx, src_cond in constraints_by_sym.get(
                    src_canon, ()
                ):
                    if src_block_id != block.id or src_idx >= idx:
                        continue
                    materialized = _subst_symbol(src_cond, src_canon, tgt_canon)
                    if materialized in existing_assume_conds:
                        continue
                    insertions.setdefault((block.id, idx), []).append(
                        canonicalize_cmd(
                            AssumeExpCmd(raw="", condition=materialized)
                        )
                    )
                    existing_assume_conds.add(materialized)
                    hits += 1

    if not insertions:
        return MaterializeEquateBoundsResult(program=program, hits=0)

    new_blocks: list[TacBlock] = []
    for block in program.blocks:
        new_cmds: list[TacCmd] = []
        for idx, cmd in enumerate(block.commands):
            new_cmds.append(cmd)
            for q in insertions.get((block.id, idx), ()):
                new_cmds.append(q)
        new_blocks.append(replace(block, commands=new_cmds))
    return MaterializeEquateBoundsResult(
        program=TacProgram(blocks=new_blocks), hits=hits
    )


def _referenced_symbols(expr: TacExpr) -> set[str]:
    """Canonical names of every ``SymbolRef`` in ``expr``."""
    out: set[str] = set()
    stack: list[TacExpr] = [expr]
    while stack:
        e = stack.pop()
        if isinstance(e, SymbolRef):
            out.add(canonical_symbol(e.name))
        elif isinstance(e, ApplyExpr):
            stack.extend(e.args)
    return out


__all__ = [
    "MaterializeEquateBoundsResult",
    "materialize_havoc_equate_bounds",
]
