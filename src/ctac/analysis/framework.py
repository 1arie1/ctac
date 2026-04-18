"""Small generic data-flow solver helpers."""

from __future__ import annotations

from collections import deque
from collections.abc import Callable
from dataclasses import dataclass
from typing import TypeVar

from ctac.graph import Cfg
from ctac.ir.models import TacProgram

T = TypeVar("T")


@dataclass(frozen=True)
class DataflowResult:
    in_state: dict[str, object]
    out_state: dict[str, object]


def _predecessors(program: TacProgram) -> dict[str, list[str]]:
    preds: dict[str, list[str]] = {b.id: [] for b in program.blocks}
    for b in program.blocks:
        for s in b.successors:
            if s in preds:
                preds[s].append(b.id)
    return preds


def run_forward(
    program: TacProgram,
    *,
    bottom: T,
    join: Callable[[list[T]], T],
    transfer: Callable[[str, T], T],
    equals: Callable[[T, T], bool],
) -> tuple[dict[str, T], dict[str, T]]:
    order = [b.id for b in Cfg(program).ordered_blocks()]
    if not order:
        return {}, {}

    preds = _predecessors(program)
    in_state = {bid: bottom for bid in order}
    out_state = {bid: bottom for bid in order}

    q = deque(order)
    queued = set(order)
    while q:
        bid = q.popleft()
        queued.discard(bid)

        pred_states = [out_state[p] for p in preds.get(bid, [])]
        new_in = join(pred_states) if pred_states else bottom
        new_out = transfer(bid, new_in)

        if not equals(new_in, in_state[bid]) or not equals(new_out, out_state[bid]):
            in_state[bid] = new_in
            out_state[bid] = new_out
            succs = next((b.successors for b in program.blocks if b.id == bid), [])
            for succ in succs:
                if succ in in_state and succ not in queued:
                    q.append(succ)
                    queued.add(succ)

    return in_state, out_state


def run_backward(
    program: TacProgram,
    *,
    bottom: T,
    join: Callable[[list[T]], T],
    transfer: Callable[[str, T], T],
    equals: Callable[[T, T], bool],
) -> tuple[dict[str, T], dict[str, T]]:
    order = [b.id for b in Cfg(program).ordered_blocks()]
    if not order:
        return {}, {}

    succ = {b.id: [s for s in b.successors if s in {x.id for x in program.blocks}] for b in program.blocks}
    preds = _predecessors(program)

    in_state = {bid: bottom for bid in order}
    out_state = {bid: bottom for bid in order}

    q = deque(reversed(order))
    queued = set(order)
    while q:
        bid = q.popleft()
        queued.discard(bid)

        succ_states = [in_state[s] for s in succ.get(bid, [])]
        new_out = join(succ_states) if succ_states else bottom
        new_in = transfer(bid, new_out)

        if not equals(new_in, in_state[bid]) or not equals(new_out, out_state[bid]):
            in_state[bid] = new_in
            out_state[bid] = new_out
            for pred in preds.get(bid, []):
                if pred in in_state and pred not in queued:
                    q.append(pred)
                    queued.add(pred)

    return in_state, out_state
