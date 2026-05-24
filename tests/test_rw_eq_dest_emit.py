"""Unit tests for the rw-eq stuttering-simulation DEST / IN_DEST helpers.

Helpers are exercised on synthetically-constructed SimDecomposition
values — no walker integration, no parsing, no SMT.
"""

from __future__ import annotations

import pytest

from ctac.ast.nodes import (
    ApplyExpr,
    AssertCmd,
    AssignExpCmd,
    ConstExpr,
    JumpCmd,
    JumpiCmd,
    SymbolRef,
)
from ctac.rw_eq.dest_emit import (
    classify_pred,
    emit_dest_write,
    emit_in_dest_ite,
)
from ctac.rw_eq.model import BlockRef
from ctac.rw_eq.sim_precheck import SimDecomposition


def _b(bid: str) -> BlockRef:
    return BlockRef(id=bid)


# --- classify_pred -----------------------------------------------------


def test_classify_pred_three_way():
    decomp = SimDecomposition(
        matched=frozenset({_b("A"), _b("B"), _b("C")}),
        stutter=frozenset({_b("S")}),
        divergence_points=frozenset({_b("A")}),
        sync_points=frozenset({_b("C")}),
        stutter_owner={_b("S"): _b("A")},
    )
    assert classify_pred(_b("S"), decomp) == "stutter"
    assert classify_pred(_b("A"), decomp) == "divergence"
    assert classify_pred(_b("B"), decomp) == "common"


def test_classify_pred_unknown_block_raises():
    decomp = SimDecomposition(
        matched=frozenset({_b("A")}),
        stutter=frozenset(),
        divergence_points=frozenset(),
        sync_points=frozenset(),
        stutter_owner={},
    )
    with pytest.raises(ValueError, match="X"):
        classify_pred(_b("X"), decomp)


# --- emit_dest_write ----------------------------------------------------


def test_emit_dest_write_jumpcmd_unconditional():
    """RHS terminator at divergence A is JumpCmd(target=B). DEST_A
    should be the constant id_of[B]."""
    A = _b("A")
    rw_term = JumpCmd(raw="JumpCmd B", target="B")
    dest_sym = SymbolRef(name="DEST_A")
    id_of = {_b("A"): 0, _b("B"): 1}

    cmd = emit_dest_write(A, rw_term, dest_sym, id_of)

    assert isinstance(cmd, AssignExpCmd)
    assert cmd.lhs == "DEST_A"
    assert cmd.rhs == ConstExpr(value="1")


def test_emit_dest_write_jumpicmd_conditional():
    """RHS terminator at divergence A is JumpiCmd(cond, B, C). DEST_A
    should be ite(COND_R, id_of[B], id_of[C])."""
    A = _b("A")
    rw_term = JumpiCmd(
        raw="JumpiCmd B C COND",
        then_target="B",
        else_target="C",
        condition="COND",
    )
    dest_sym = SymbolRef(name="DEST_A")
    id_of = {_b("A"): 0, _b("B"): 1, _b("C"): 2}

    cmd = emit_dest_write(A, rw_term, dest_sym, id_of)

    assert isinstance(cmd, AssignExpCmd)
    assert cmd.lhs == "DEST_A"
    # rhs should be Ite(SymbolRef(COND), ConstExpr(1), ConstExpr(2))
    assert isinstance(cmd.rhs, ApplyExpr)
    assert cmd.rhs.op == "Ite"
    assert cmd.rhs.args[0] == SymbolRef(name="COND")
    assert cmd.rhs.args[1] == ConstExpr(value="1")
    assert cmd.rhs.args[2] == ConstExpr(value="2")


# --- emit_in_dest_ite ---------------------------------------------------


def test_emit_in_dest_ite_single_pred_degenerate():
    """One LHS pred at sync B — chain degenerates to the val directly,
    no Ite wrap."""
    decomp = SimDecomposition(
        matched=frozenset({_b("A"), _b("B")}),
        stutter=frozenset({_b("S")}),
        divergence_points=frozenset({_b("A")}),
        sync_points=frozenset({_b("B")}),
        stutter_owner={_b("S"): _b("A")},
    )
    id_of = {_b("A"): 0, _b("B"): 1}
    dest_sym_for = {_b("A"): SymbolRef(name="DEST_A")}
    in_dest_sym = SymbolRef(name="IN_DEST_B")

    cmds = emit_in_dest_ite(
        sync=_b("B"),
        in_dest_sym=in_dest_sym,
        lhs_preds=[_b("S")],
        decomp=decomp,
        id_of=id_of,
        dest_sym_for=dest_sym_for,
        chk_name="CHK0",
    )

    # 3 cmds: assign IN_DEST, assign CHK, assert CHK
    assert len(cmds) == 3
    assign_in_dest, assign_chk, chk_assert = cmds

    assert isinstance(assign_in_dest, AssignExpCmd)
    assert assign_in_dest.lhs == "IN_DEST_B"
    # Single pred (stutter S, owner A) → val is DEST_A directly, no Ite
    assert assign_in_dest.rhs == SymbolRef(name="DEST_A")

    assert isinstance(assign_chk, AssignExpCmd)
    assert assign_chk.lhs == "CHK0"
    assert assign_chk.rhs == ApplyExpr(
        op="Eq",
        args=(SymbolRef(name="IN_DEST_B"), ConstExpr(value="1")),
    )

    assert isinstance(chk_assert, AssertCmd)
    assert chk_assert.predicate == SymbolRef(name="CHK0")


def test_emit_in_dest_ite_three_way_case_split():
    """Sync B with three LHS preds — one stutter S, one divergence D,
    one non-divergence common N. Verify the ITE chain mixes the three
    val shapes correctly."""
    decomp = SimDecomposition(
        matched=frozenset({_b("D"), _b("N"), _b("B")}),
        stutter=frozenset({_b("S")}),
        divergence_points=frozenset({_b("D")}),
        sync_points=frozenset({_b("B")}),
        stutter_owner={_b("S"): _b("D")},
    )
    id_of = {_b("D"): 0, _b("N"): 1, _b("B"): 2}
    dest_sym_for = {_b("D"): SymbolRef(name="DEST_D")}
    in_dest_sym = SymbolRef(name="IN_DEST_B")

    cmds = emit_in_dest_ite(
        sync=_b("B"),
        in_dest_sym=in_dest_sym,
        lhs_preds=[_b("S"), _b("D"), _b("N")],
        decomp=decomp,
        id_of=id_of,
        dest_sym_for=dest_sym_for,
        chk_name="CHK0",
    )

    assign_in_dest = cmds[0]
    assert assign_in_dest.lhs == "IN_DEST_B"
    # Preds sorted by id: D, N, S. Last (S) is else-arm directly,
    # preceding two are ite-gated.
    rhs = assign_in_dest.rhs
    # Outermost: Ite(RC_D, val_D, Ite(RC_N, val_N, val_S))
    assert isinstance(rhs, ApplyExpr) and rhs.op == "Ite"
    rc_d, val_d, inner = rhs.args
    assert rc_d == SymbolRef(name="ReachabilityCertoraD")
    # D is divergence → val_D = DEST_D
    assert val_d == SymbolRef(name="DEST_D")

    assert isinstance(inner, ApplyExpr) and inner.op == "Ite"
    rc_n, val_n, val_s = inner.args
    assert rc_n == SymbolRef(name="ReachabilityCertoraN")
    # N is non-divergence common → val_N = id_of[B] = 2
    assert val_n == ConstExpr(value="2")
    # S is stutter owned by D → val_S = DEST_D
    assert val_s == SymbolRef(name="DEST_D")


def test_emit_in_dest_ite_rejects_empty_preds():
    decomp = SimDecomposition(
        matched=frozenset({_b("B")}),
        stutter=frozenset(),
        divergence_points=frozenset(),
        sync_points=frozenset({_b("B")}),
        stutter_owner={},
    )
    with pytest.raises(ValueError, match="no LHS predecessors"):
        emit_in_dest_ite(
            sync=_b("B"),
            in_dest_sym=SymbolRef(name="IN_DEST_B"),
            lhs_preds=[],
            decomp=decomp,
            id_of={_b("B"): 0},
            dest_sym_for={},
            chk_name="CHK0",
        )


# --- _WalkerState fresh helpers ----------------------------------------


def test_walker_state_fresh_dest_and_in_dest():
    """Verify _WalkerState mints DEST_/IN_DEST_ symbols correctly and
    registers them in extra_symbols."""
    from ctac.rw_eq.transform import _WalkerState

    state = _WalkerState(
        lhs_defined=frozenset(),
        rhs_defined=frozenset(),
        strict=False,
        check_feasibility=False,
    )
    dest_sym = state.fresh_dest_for(_b("A"))
    in_dest_sym = state.fresh_in_dest_for(_b("B"))

    assert dest_sym == SymbolRef(name="DEST_A")
    assert in_dest_sym == SymbolRef(name="IN_DEST_B")
    assert ("DEST_A", "int") in state.extra_symbols
    assert ("IN_DEST_B", "int") in state.extra_symbols
