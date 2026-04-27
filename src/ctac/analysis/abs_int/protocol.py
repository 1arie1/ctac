"""Domain protocol for the abstract-interpreter framework.

Domains own their own AbsState representation. The framework is uniform
across non-relational (per-var maps), DSA-aware split, and relational
(cluster DBMs) shapes — each plugs into the same protocol.
"""

from __future__ import annotations

from typing import Protocol, TypeVar

from ctac.ast.nodes import TacCmd, TacExpr
from ctac.ir.models import TacBlock

State = TypeVar("State")


class Domain(Protocol[State]):
    """Operations the framework calls on the domain.

    The framework keeps a `Frontier = dict[NBId, State]`. As blocks are
    visited in topological order, the framework calls into the domain
    via four primitives:

      - `init`     — produce the initial state at the entry block.
      - `transfer` — apply one command's effect to a block-local state.
      - `propagate`— move state along an edge from `src` to `dst`,
                     optionally specializing by `edge_cond`.
      - `join`     — merge multiple incoming states at a join point.

    `refine_assume` is a helper the domain typically calls from
    `transfer` (on `AssumeExpCmd`) and `propagate` (when an edge
    condition is present); the framework does not call it directly.
    """

    def init(self, entry: TacBlock) -> State:
        ...

    def transfer(self, state: State, cmd: TacCmd, *, block: TacBlock) -> State:
        ...

    def propagate(
        self,
        state: State,
        *,
        src: TacBlock,
        dst: TacBlock,
        edge_cond: TacExpr | None,
    ) -> State:
        ...

    def join(self, states: list[State], *, dst: TacBlock) -> State:
        ...

    def refine_assume(self, state: State, cond: TacExpr, *, block: TacBlock) -> State:
        ...
