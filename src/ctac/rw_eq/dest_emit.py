"""DEST / IN_DEST emission helpers for the stuttering-simulation walker.

Given a :class:`SimDecomposition`, these helpers produce the typed TAC
fragments the walker splices into matched-block emit positions:

- ``emit_dest_write(A, ...)`` — one ``DEST_A := <expr>`` assignment
  emitted just before A's terminator, where A is a divergence point.
  ``<expr>`` is ``id_of[succ_R(A)]`` for a JumpCmd or
  ``ite(COND_R, id_of[then_R], id_of[else_R])`` for a JumpiCmd.
- ``emit_in_dest_ite(B, ...)`` — at sync point B's entry, the RC-gated
  ITE chain over LHS predecessors plus the ``IN_DEST_B == id_of[B]``
  CHK.

The "exactly one ``ReachabilityCertora<pred>`` is true" invariant from
sea_vc's CFG encoding is the contract these helpers rely on; the
ITE chain shorts on the final predecessor without a defensive
``BAD_VAL`` fallback. See ``ctac-research/journal/2026-05/2026-05-24-rw-eq-stuttering-simulation-theory-and-per-a-witness.md``
for the rationale.
"""

from __future__ import annotations

from typing import Literal

from ctac.ast.nodes import (
    ApplyExpr,
    AssertCmd,
    AssignExpCmd,
    ConstExpr,
    JumpCmd,
    JumpiCmd,
    SymbolRef,
    TacCmd,
    TacExpr,
)
from ctac.rw_eq.model import BlockRef
from ctac.rw_eq.sim_precheck import SimDecomposition
from ctac.smt.encoding.path_skeleton import reachability_var_name


PredClass = Literal["stutter", "divergence", "common"]


def classify_pred(pred: BlockRef, decomp: SimDecomposition) -> PredClass:
    """3-way case split that determines ``val_i`` for ``IN_DEST_B``.

    - ``stutter``: pred is an LHS-only stutter block.
    - ``divergence``: pred is a matched block with mismatched
      successors (so RHS's terminator at pred is conditional / leads
      elsewhere; pred has its own ``DEST_{pred}``).
    - ``common``: pred is a matched block with identical successor
      lists (the lockstep walker's per-block CHKs make the runtime
      branch taken at pred agree between LHS and RHS, so
      ``id_of[B]`` is the sound value).
    """
    if pred in decomp.stutter:
        return "stutter"
    if pred in decomp.divergence_points:
        return "divergence"
    if pred in decomp.matched:
        return "common"
    raise ValueError(
        f"predecessor {pred.id!r} is neither matched nor stutter; "
        f"decomp is malformed for this pred"
    )


def emit_dest_write(
    divergence: BlockRef,
    rw_terminator: JumpCmd | JumpiCmd,
    dest_sym: SymbolRef,
    id_of: dict[BlockRef, int],
) -> AssignExpCmd:
    """Build ``DEST_<A> := <expr>`` to splice before A's LHS terminator.

    ``rw_terminator`` is RHS's terminator at A — we encode RHS's
    committed destination into ``DEST_A``. LHS's terminator stays
    intact (the walker emits it verbatim afterward).
    """
    if isinstance(rw_terminator, JumpCmd):
        rhs: TacExpr = _const_int(id_of[BlockRef(id=rw_terminator.target)])
    else:
        # JumpiCmd: encode the conditional commitment.
        cond = rw_terminator.condition_expr()
        then_id = _const_int(id_of[BlockRef(id=rw_terminator.then_target)])
        else_id = _const_int(id_of[BlockRef(id=rw_terminator.else_target)])
        rhs = ApplyExpr(op="Ite", args=(cond, then_id, else_id))
    return AssignExpCmd(raw="", lhs=dest_sym.name, rhs=rhs)


def emit_in_dest_ite(
    sync: BlockRef,
    in_dest_sym: SymbolRef,
    lhs_preds: list[BlockRef],
    decomp: SimDecomposition,
    id_of: dict[BlockRef, int],
    dest_sym_for: dict[BlockRef, SymbolRef],
    *,
    chk_name: str,
) -> list[TacCmd]:
    """Build the IN_DEST_B := <RC-gated ITE chain> and the CHK assert.

    Returns ``[assign, chk_def, assert]`` to splice at the entry of
    sync block B (ahead of any other body content).

    Empty ``lhs_preds`` is a contract violation — sync points always
    have at least one LHS predecessor by construction.
    """
    if not lhs_preds:
        raise ValueError(
            f"sync point {sync.id!r} has no LHS predecessors; "
            f"caller should have skipped IN_DEST emission for this block"
        )
    # Sort predecessors by id for deterministic ITE shape.
    preds = sorted(lhs_preds, key=lambda b: b.id)

    def _val_for(pred: BlockRef) -> TacExpr:
        cls = classify_pred(pred, decomp)
        if cls == "stutter":
            owner = decomp.stutter_owner[pred]
            return SymbolRef(name=dest_sym_for[owner].name)
        if cls == "divergence":
            return SymbolRef(name=dest_sym_for[pred].name)
        # common: lockstep CHKs at pred ensure the branch taken to B
        # in LHS aligns with RHS's branch.
        return _const_int(id_of[sync])

    # Build the chain from innermost outward. Last pred's val is the
    # else-arm of the innermost ITE (or the whole RHS if n == 1).
    rhs: TacExpr = _val_for(preds[-1])
    for pred in reversed(preds[:-1]):
        rc_var = SymbolRef(name=reachability_var_name(pred.id))
        rhs = ApplyExpr(op="Ite", args=(rc_var, _val_for(pred), rhs))

    assign = AssignExpCmd(raw="", lhs=in_dest_sym.name, rhs=rhs)
    eq_expr = ApplyExpr(
        op="Eq", args=(SymbolRef(name=in_dest_sym.name), _const_int(id_of[sync]))
    )
    chk_def = AssignExpCmd(raw="", lhs=chk_name, rhs=eq_expr)
    chk_assert = AssertCmd(
        raw="",
        predicate=SymbolRef(name=chk_name),
        message=f"rw-eq:sim:{sync.id} in-dest",
    )
    return [assign, chk_def, chk_assert]


def _const_int(value: int) -> ConstExpr:
    """TAC int literal."""
    return ConstExpr(value=str(value))


__all__ = ["PredClass", "classify_pred", "emit_dest_write", "emit_in_dest_ite"]
