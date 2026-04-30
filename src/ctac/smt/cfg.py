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
from ctac.smt.util import and_terms, at_most_one_terms, implies, or_terms


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


CfgEncoder = Callable[["CfgEncodeInput", Callable[[str], None]], None]


def encode_bwd0(inp: CfgEncodeInput, add_constraint: Callable[[str], None]) -> None:
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
        add_constraint(implies(s_guard, or_terms(edge_terms)))
        add_constraint(implies(s_guard, or_terms(pred_block_terms)))
        for amo in at_most_one_terms(pred_block_terms):
            add_constraint(implies(s_guard, amo))


def encode_bwd1(inp: CfgEncodeInput, add_constraint: Callable[[str], None]) -> None:
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
            add_constraint(
                implies(and_terms([s_guard, inp.block_guards[e.pred]]), e.branch_cond)
            )
        add_constraint(implies(s_guard, or_terms(pred_block_terms)))
        for amo in at_most_one_terms(pred_block_terms):
            add_constraint(implies(s_guard, amo))


CFG_ENCODERS: dict[str, CfgEncoder] = {
    "bwd0": encode_bwd0,
    "bwd1": encode_bwd1,
}
