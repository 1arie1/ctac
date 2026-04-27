"""Framework-level tests for the abstract-interpreter scaffolding.

Uses a synthetic trace-domain that records every call into the domain.
This exercises the frontier mechanics, topological order, and edge-
condition extraction independent of any specific abstract domain.
"""

from __future__ import annotations

from dataclasses import dataclass, field

from ctac.analysis.abs_int.framework import edge_condition, run
from ctac.ast.nodes import (
    AnnotationCmd,
    ApplyExpr,
    AssignExpCmd,
    JumpCmd,
    JumpiCmd,
    LabelCmd,
    SymbolRef,
    TacCmd,
    TacExpr,
)
from ctac.ir.models import TacBlock, TacProgram


@dataclass
class _TraceState:
    log: list[str] = field(default_factory=list)
    visited: list[str] = field(default_factory=list)


@dataclass
class _TraceDomain:
    """A domain that just records every framework call."""

    inits: int = 0

    def init(self, entry: TacBlock) -> _TraceState:
        self.inits += 1
        s = _TraceState()
        s.log.append(f"init({entry.id})")
        return s

    def transfer(self, state: _TraceState, cmd: TacCmd, *, block: TacBlock) -> _TraceState:
        state.log.append(f"transfer({block.id}, {type(cmd).__name__})")
        return state

    def propagate(
        self,
        state: _TraceState,
        *,
        src: TacBlock,
        dst: TacBlock,
        edge_cond: TacExpr | None,
    ) -> _TraceState:
        cond_repr = "uncond" if edge_cond is None else "cond"
        state.log.append(f"propagate({src.id}->{dst.id}, {cond_repr})")
        return state

    def join(self, states: list[_TraceState], *, dst: TacBlock) -> _TraceState:
        # Coalesce all incoming states into the first (their logs already
        # share an instance under storage strategy 1, so this is idempotent).
        states[0].log.append(f"join@{dst.id}(n={len(states)})")
        return states[0]

    def refine_assume(
        self, state: _TraceState, cond: TacExpr, *, block: TacBlock
    ) -> _TraceState:
        state.log.append(f"refine_assume({block.id})")
        return state


def _block(bid: str, succs: list[str], cmds: list[TacCmd]) -> TacBlock:
    return TacBlock(id=bid, successors=succs, commands=cmds)


def _assign(lhs: str, rhs: TacExpr) -> AssignExpCmd:
    return AssignExpCmd(raw=f"{lhs} = ...", lhs=lhs, rhs=rhs)


def _sym(name: str) -> SymbolRef:
    return SymbolRef(name=name)


def _jumpi(then_blk: str, else_blk: str, cond: str) -> JumpiCmd:
    return JumpiCmd(
        raw=f"JumpiCmd {then_blk} {else_blk} {cond}",
        then_target=then_blk,
        else_target=else_blk,
        condition=cond,
    )


def _jump(target: str) -> JumpCmd:
    return JumpCmd(raw=f"JumpCmd {target}", target=target)


def test_run_empty_program_returns_empty_frontier() -> None:
    program = TacProgram(blocks=[])
    domain = _TraceDomain()
    frontier = run(program, domain)
    assert frontier == {}
    assert domain.inits == 0


def test_run_single_block_calls_init_and_transfer() -> None:
    program = TacProgram(
        blocks=[
            _block("B0", [], [_assign("R", _sym("X"))]),
        ]
    )
    domain = _TraceDomain()
    frontier = run(program, domain)
    assert domain.inits == 1
    state = next(iter(frontier.values()))
    assert state.log == ["init(B0)", "transfer(B0, AssignExpCmd)"]


def test_run_skips_noise_commands() -> None:
    program = TacProgram(
        blocks=[
            _block(
                "B0",
                [],
                [
                    AnnotationCmd(raw="AnnotationCmd JSON{}", payload="JSON{}"),
                    LabelCmd(raw="LabelCmd hi", text="hi"),
                    _assign("R", _sym("X")),
                ],
            ),
        ]
    )
    domain = _TraceDomain()
    frontier = run(program, domain)
    state = next(iter(frontier.values()))
    # Only the AssignExpCmd should have been transferred — Annotation
    # and Label are filtered.
    assert state.log == ["init(B0)", "transfer(B0, AssignExpCmd)"]


def test_run_unconditional_edge_propagate() -> None:
    program = TacProgram(
        blocks=[
            _block("B0", ["B1"], [_jump("B1")]),
            _block("B1", [], []),
        ]
    )
    domain = _TraceDomain()
    frontier = run(program, domain)
    state = next(iter(frontier.values()))
    assert state.log == [
        "init(B0)",
        "transfer(B0, JumpCmd)",
        "propagate(B0->B1, uncond)",
    ]


def test_run_conditional_edges_propagate_with_cond() -> None:
    program = TacProgram(
        blocks=[
            _block("B0", ["BT", "BF"], [_jumpi("BT", "BF", "c")]),
            _block("BT", [], []),
            _block("BF", [], []),
        ]
    )
    domain = _TraceDomain()
    run(program, domain)
    # No assertion on exact ordering across the two propagates, but
    # both edges must be marked conditional.
    # Reach the live state through any frontier entry.
    # (Both BT and BF are leaves; either's log carries the trace.)
    # We rebuild by running again with a deterministic check:
    program2 = TacProgram(
        blocks=[
            _block("B0", ["BT", "BF"], [_jumpi("BT", "BF", "c")]),
            _block("BT", [], []),
            _block("BF", [], []),
        ]
    )
    d2 = _TraceDomain()
    frontier = run(program2, d2)
    state = next(iter(frontier.values()))
    propagate_lines = [line for line in state.log if line.startswith("propagate")]
    assert "propagate(B0->BT, cond)" in propagate_lines
    assert "propagate(B0->BF, cond)" in propagate_lines


def test_run_join_called_when_two_preds_meet() -> None:
    # B0 -> B1, B0 -> B2, B1 -> B3, B2 -> B3 (diamond)
    program = TacProgram(
        blocks=[
            _block("B0", ["B1", "B2"], [_jumpi("B1", "B2", "c")]),
            _block("B1", ["B3"], [_jump("B3")]),
            _block("B2", ["B3"], [_jump("B3")]),
            _block("B3", [], []),
        ]
    )
    domain = _TraceDomain()
    frontier = run(program, domain)
    state = next(iter(frontier.values()))
    join_lines = [line for line in state.log if line.startswith("join")]
    assert join_lines == ["join@B3(n=2)"]


def test_edge_condition_then_branch() -> None:
    src = _block("B0", ["BT", "BF"], [_jumpi("BT", "BF", "c")])
    bt = _block("BT", [], [])
    cond = edge_condition(src, bt)
    assert cond == SymbolRef(name="c")


def test_edge_condition_else_branch() -> None:
    src = _block("B0", ["BT", "BF"], [_jumpi("BT", "BF", "c")])
    bf = _block("BF", [], [])
    cond = edge_condition(src, bf)
    assert cond == ApplyExpr(op="LNot", args=(SymbolRef(name="c"),))


def test_edge_condition_unconditional() -> None:
    src = _block("B0", ["B1"], [_jump("B1")])
    dst = _block("B1", [], [])
    assert edge_condition(src, dst) is None


def test_edge_condition_skips_noise_to_find_terminator() -> None:
    src = _block(
        "B0",
        ["BT", "BF"],
        [
            _jumpi("BT", "BF", "c"),
            AnnotationCmd(raw="AnnotationCmd JSON{}", payload="JSON{}"),
        ],
    )
    bt = _block("BT", [], [])
    assert edge_condition(src, bt) == SymbolRef(name="c")
