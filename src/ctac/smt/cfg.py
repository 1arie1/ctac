"""CFG-constraint encoding for sea_vc.

Defines a small CFG model (`CfgEncodeInput`, `CfgEdge`) with
integer-indexed blocks and pre-resolved per-block guard terms,
plus a registry of encoders keyed by short string names. The
client (sea_vc) builds the input via `build_cfg_input` and
dispatches through `CFG_ENCODERS[name]` — encoders themselves
depend only on the data class and `smt.util` combinators."""

from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass, field
from typing import Callable

from ctac.ir.models import TacProgram
from ctac.smt.encoding.path_skeleton import block_guard, predecessor_edges
from ctac.smt.util import and_terms, at_most_one_terms, iff, implies, or_terms


@dataclass(frozen=True)
class CfgEdge:
    pred: int          # index into CfgEncodeInput.block_ids
    succ: int          # index into CfgEncodeInput.block_ids
    branch_cond: str   # SMT term, already encoded


@dataclass(frozen=True)
class CfgEncodeInput:
    block_ids: tuple[str, ...]
    block_guards: tuple[str, ...]
    entry: int
    edges: tuple[CfgEdge, ...]
    _preds_by_succ: dict[int, tuple[CfgEdge, ...]] = field(
        default_factory=dict, init=False, repr=False, compare=False
    )
    _succs_by_pred: dict[int, tuple[CfgEdge, ...]] = field(
        default_factory=dict, init=False, repr=False, compare=False
    )

    def __post_init__(self) -> None:
        preds: dict[int, list[CfgEdge]] = defaultdict(list)
        succs: dict[int, list[CfgEdge]] = defaultdict(list)
        for e in self.edges:
            preds[e.succ].append(e)
            succs[e.pred].append(e)
        # Frozen dataclass — bypass `__setattr__` to populate the
        # private cache fields once.
        object.__setattr__(self, "_preds_by_succ", {k: tuple(v) for k, v in preds.items()})
        object.__setattr__(self, "_succs_by_pred", {k: tuple(v) for k, v in succs.items()})

    def preds_of(self, succ: int) -> tuple[CfgEdge, ...]:
        return self._preds_by_succ.get(succ, ())

    def succs_of(self, pred: int) -> tuple[CfgEdge, ...]:
        return self._succs_by_pred.get(pred, ())


def build_cfg_input(
    program: TacProgram,
    *,
    entry_block_id: str,
    symbol_term: dict[str, str],
) -> CfgEncodeInput:
    """Build a `CfgEncodeInput` from a TacProgram and the encoder's
    symbol-term mapping. Owns: block-id-to-int indexing, edge
    construction (via `predecessor_edges`), pre-resolved block-guard
    terms (via `block_guard`)."""
    block_ids = tuple(b.id for b in program.blocks)
    block_id_to_idx = {bid: i for i, bid in enumerate(block_ids)}
    block_guards = tuple(
        block_guard(bid, entry_block_id=entry_block_id) for bid in block_ids
    )
    preds = predecessor_edges(program, symbol_term_by_name=symbol_term)
    edges = tuple(
        CfgEdge(
            pred=block_id_to_idx[pe.pred_block_id],
            succ=block_id_to_idx[pe.succ_block_id],
            branch_cond=pe.branch_cond,
        )
        for succ_edges in preds.values()
        for pe in succ_edges
    )
    return CfgEncodeInput(
        block_ids=block_ids,
        block_guards=block_guards,
        entry=block_id_to_idx[entry_block_id],
        edges=edges,
    )


@dataclass
class CfgEmit:
    """Sink object for CFG encoders: receives constraints and any
    auxiliary declarations (e.g. per-edge Bool vars introduced by
    edge-variable encoders)."""

    add_constraint: Callable[[str], None]
    add_decl: Callable[[str, str], None]   # (name, sort)


CfgEncoder = Callable[["CfgEncodeInput", "CfgEmit"], None]


def _edge_var(pred: int, succ: int) -> str:
    return f"e_{pred}_{succ}"


def encode_bwd0(inp: CfgEncodeInput, emit: CfgEmit) -> None:
    """Default encoding (matches the historical sea_vc shape).

    Per non-entry block S:
      * edge-level feasibility: ``BLK_S => ⋁_i (BLK_P_i ∧ cond_i)``
      * block-level existence:  ``BLK_S => ⋁_i BLK_P_i``
      * at-most-one over predecessor blocks (pairwise)."""
    for s in range(len(inp.block_ids)):
        if s == inp.entry:
            continue
        s_guard = inp.block_guards[s]
        in_edges = inp.preds_of(s)
        edge_terms = [
            and_terms([inp.block_guards[e.pred], e.branch_cond]) for e in in_edges
        ]
        pred_block_terms = [inp.block_guards[e.pred] for e in in_edges]
        emit.add_constraint(implies(s_guard, or_terms(edge_terms)))
        emit.add_constraint(implies(s_guard, or_terms(pred_block_terms)))
        for amo in at_most_one_terms(pred_block_terms):
            emit.add_constraint(implies(s_guard, amo))


def encode_bwd1(inp: CfgEncodeInput, emit: CfgEmit) -> None:
    """Per-edge clausal implications, equivalent to bwd0 under AMO.

    Per non-entry block S:
      * for each predecessor edge i:
          ``(BLK_S ∧ BLK_P_i) => cond_i``
      * block-level existence:  ``BLK_S => ⋁_i BLK_P_i``
      * at-most-one over predecessor blocks (pairwise).

    The per-edge implications are individually weaker than bwd0's
    edge-feasibility OR-of-ANDs; AMO over predecessor blocks
    (combined with block-level existence) recovers the strength
    by forcing exactly one predecessor's branch to fire."""
    for s in range(len(inp.block_ids)):
        if s == inp.entry:
            continue
        s_guard = inp.block_guards[s]
        in_edges = inp.preds_of(s)
        pred_block_terms = [inp.block_guards[e.pred] for e in in_edges]
        for e in in_edges:
            emit.add_constraint(
                implies(and_terms([s_guard, inp.block_guards[e.pred]]), e.branch_cond)
            )
        emit.add_constraint(implies(s_guard, or_terms(pred_block_terms)))
        for amo in at_most_one_terms(pred_block_terms):
            emit.add_constraint(implies(s_guard, amo))


def encode_fwd(inp: CfgEncodeInput, emit: CfgEmit) -> None:
    """Block-only forward encoding (forward analog of bwd1).

    Per non-terminal block i (i.e. ``succs_of(i)`` non-empty):
      * block-level existence: ``BLK_i => ⋁_j BLK_succ_j``
      * at-most-one over successor blocks (pairwise)
      * for each successor j with branch condition c:
          ``(BLK_i ∧ BLK_j) => c``

    Block existence is one-way ``=>`` (not iff): a node may have
    multiple parents in the CFG, so ``BLK_i ⇔ ⋁ BLK_succ`` would
    be over-tight (a successor reachable via a different parent
    would force this block reachable too). Use ``fwd-edge`` if a
    biconditional is desired — edge variables decouple the
    multi-parent ambiguity and make the iff sound."""
    for i in range(len(inp.block_ids)):
        out_edges = inp.succs_of(i)
        if not out_edges:
            continue
        i_guard = inp.block_guards[i]
        succ_block_terms = [inp.block_guards[e.succ] for e in out_edges]
        emit.add_constraint(implies(i_guard, or_terms(succ_block_terms)))
        for amo in at_most_one_terms(succ_block_terms):
            emit.add_constraint(implies(i_guard, amo))
        for e in out_edges:
            emit.add_constraint(
                implies(and_terms([i_guard, inp.block_guards[e.succ]]), e.branch_cond)
            )


def encode_fwd_edge(inp: CfgEncodeInput, emit: CfgEmit) -> None:
    """Forward encoding with per-edge Bool variables.

    Per non-terminal block i:
      * block existence (iff over edges):
          ``BLK_i ⇔ ⋁_j e_{i→j}``
      * at-most-one over outgoing edges of i
      * for each outgoing edge (i → j) with cond c:
          ``e_{i→j} => BLK_j``         (bidirectional half;
                                        the other half ``e ⇒ BLK_i``
                                        is implied by the iff)
          ``e_{i→j} => c``             (guard on edge variable)

    Edge variables decouple the multi-parent ambiguity that makes
    a block-only forward iff unsound. With edge vars, the iff is
    sound because each edge fires independently."""
    declared: set[str] = set()
    for i in range(len(inp.block_ids)):
        out_edges = inp.succs_of(i)
        if not out_edges:
            continue
        edge_vars: list[str] = []
        for e in out_edges:
            ev = _edge_var(e.pred, e.succ)
            if ev not in declared:
                emit.add_decl(ev, "Bool")
                declared.add(ev)
            edge_vars.append(ev)
        i_guard = inp.block_guards[i]
        emit.add_constraint(iff(i_guard, or_terms(edge_vars)))
        for amo in at_most_one_terms(edge_vars):
            emit.add_constraint(implies(i_guard, amo))
        for e, ev in zip(out_edges, edge_vars):
            emit.add_constraint(implies(ev, inp.block_guards[e.succ]))
            emit.add_constraint(implies(ev, e.branch_cond))


def encode_bwd_edge(inp: CfgEncodeInput, emit: CfgEmit) -> None:
    """Backward encoding with per-edge Bool variables (analog of
    bwd1 with the edge variables of fwd-edge).

    Per non-entry block j:
      * block existence (iff over edges):
          ``BLK_j ⇔ ⋁_i e_{i→j}``
      * at-most-one over incoming edges of j
      * for each incoming edge (i → j) with cond c:
          ``e_{i→j} => BLK_i``         (bidirectional half;
                                        ``e ⇒ BLK_j`` implied by iff)
          ``e_{i→j} => c``             (guard on edge variable)

    Entry block has no in-edges and is skipped (its guard is
    ``"true"`` by convention)."""
    declared: set[str] = set()
    for j in range(len(inp.block_ids)):
        if j == inp.entry:
            continue
        in_edges = inp.preds_of(j)
        if not in_edges:
            # Non-entry block with no predecessors — unreachable
            # by construction. Leave its block guard unconstrained
            # by this encoder; other parts of the formula handle it.
            continue
        edge_vars: list[str] = []
        for e in in_edges:
            ev = _edge_var(e.pred, e.succ)
            if ev not in declared:
                emit.add_decl(ev, "Bool")
                declared.add(ev)
            edge_vars.append(ev)
        j_guard = inp.block_guards[j]
        emit.add_constraint(iff(j_guard, or_terms(edge_vars)))
        for amo in at_most_one_terms(edge_vars):
            emit.add_constraint(implies(j_guard, amo))
        for e, ev in zip(in_edges, edge_vars):
            emit.add_constraint(implies(ev, inp.block_guards[e.pred]))
            emit.add_constraint(implies(ev, e.branch_cond))


CFG_ENCODERS: dict[str, CfgEncoder] = {
    "bwd0": encode_bwd0,
    "bwd1": encode_bwd1,
    "fwd": encode_fwd,
    "fwd-edge": encode_fwd_edge,
    "bwd-edge": encode_bwd_edge,
}
