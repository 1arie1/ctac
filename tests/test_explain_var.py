"""Tests for the per-variable interval-domain diagnostic."""

from __future__ import annotations

from ctac.analysis.abs_int import explain_var, format_var_explanation
from ctac.analysis.abs_int.interval_ops import Interval
from ctac.ast.nodes import (
    ApplyExpr,
    AssertCmd,
    AssignExpCmd,
    AssignHavocCmd,
    AssumeExpCmd,
    ConstExpr,
    JumpCmd,
    JumpiCmd,
    SymbolRef,
    TacCmd,
    TacExpr,
)
from ctac.ir.models import TacBlock, TacProgram


def _block(bid: str, succs: list[str], cmds: list[TacCmd]) -> TacBlock:
    return TacBlock(id=bid, successors=succs, commands=cmds)


def _havoc(lhs: str) -> AssignHavocCmd:
    return AssignHavocCmd(raw=f"AssignHavocCmd {lhs}", lhs=lhs)


def _assign(lhs: str, rhs: TacExpr) -> AssignExpCmd:
    return AssignExpCmd(raw=f"AssignExpCmd {lhs}", lhs=lhs, rhs=rhs)


def _assume(cond: TacExpr) -> AssumeExpCmd:
    return AssumeExpCmd(raw="AssumeExpCmd", condition=cond)


def _sym(name: str) -> SymbolRef:
    return SymbolRef(name=name)


def _const(v: str) -> ConstExpr:
    return ConstExpr(value=v)


def _apply(op: str, *args: TacExpr) -> ApplyExpr:
    return ApplyExpr(op=op, args=tuple(args))


def _jumpi(then_blk: str, else_blk: str, cond: str) -> JumpiCmd:
    return JumpiCmd(
        raw=f"JumpiCmd {then_blk} {else_blk} {cond}",
        then_target=then_blk,
        else_target=else_blk,
        condition=cond,
    )


def _jump(t: str) -> JumpCmd:
    return JumpCmd(raw=f"JumpCmd {t}", target=t)


def test_explain_dsa_static_with_entry_assume() -> None:
    """Entry-block refinement promotes to static. Explain should show
    static = the refined value, single def site, one refinement."""
    program = TacProgram(
        blocks=[
            _block(
                "e",
                [],
                [
                    _havoc("X"),
                    _assume(_apply("Le", _sym("X"), _const("0x64"))),
                ],
            ),
        ]
    )
    exp = explain_var(program, "X", symbol_sorts={"X": "bv256"})
    assert exp.var == "X"
    assert exp.sort == "bv256"
    assert exp.is_dsa_dynamic is False
    assert exp.static == Interval(0, 100)
    assert len(exp.defs) == 1
    assert exp.defs[0].block_id == "e"
    assert exp.defs[0].cmd_kind == "AssignHavocCmd"
    assert len(exp.refinements) == 1
    assert exp.refinements[0].block_id == "e"
    assert "Le(X 0x64)" in exp.refinements[0].cond_text


def test_explain_dsa_dynamic_two_defs_diverge() -> None:
    """A var with two defs (DSA-dynamic) where one def evaluates to a
    point and the other to a sort-default range. The tightest is the
    meet — explain must surface that distinction with the warning
    note about tightest being a meet, not a universal."""
    program = TacProgram(
        blocks=[
            _block("e", ["B1", "B2"], [_havoc("c"), _jumpi("B1", "B2", "c")]),
            _block("B1", ["J"], [_assign("X", _const("0x0")), _jump("J")]),
            _block(
                "B2",
                ["J"],
                [_havoc("X"), _jump("J")],
            ),
            _block("J", [], []),
        ]
    )
    exp = explain_var(program, "X", symbol_sorts={"X": "bv256", "c": "bool"})
    assert exp.is_dsa_dynamic is True
    assert exp.static is None  # DSA-dynamic vars don't appear in static
    # Two defs.
    assert len(exp.defs) == 2
    blocks_with_def = sorted(d.block_id for d in exp.defs)
    assert blocks_with_def == ["B1", "B2"]
    # The tightest is meet([0, 0], sort_default) at minimum, =
    # something including [0, 0].
    assert exp.tightest.lo == 0
    # Format produces a "note" line because views diverge.
    text = "\n".join(format_var_explanation(exp))
    assert "tightest is the meet across views" in text


def test_explain_picks_up_non_entry_refinement() -> None:
    """A non-entry block assume tightens local but not static. Explain
    should list the refinement at the right block, and the tightest
    note should fire."""
    program = TacProgram(
        blocks=[
            _block("e", ["B1"], [_havoc("X"), _jump("B1")]),
            _block(
                "B1",
                [],
                [_assume(_apply("Le", _sym("X"), _const("0xa")))],
            ),
        ]
    )
    exp = explain_var(program, "X", symbol_sorts={"X": "bv256"})
    # Static stays at the sort default (no entry refinement).
    assert exp.static == Interval(0, (1 << 256) - 1)
    # One refinement, at B1.
    assert len(exp.refinements) == 1
    assert exp.refinements[0].block_id == "B1"
    assert exp.refinements[0].local_value == Interval(0, 10)
    # Tightest is the refinement.
    assert exp.tightest == Interval(0, 10)
    text = "\n".join(format_var_explanation(exp))
    assert "tightest is the meet across views" in text


def test_explain_undefined_symbol_returns_top() -> None:
    """A symbol that's never defined or refined yields a TOP / empty
    explanation — useful for catching typos in --explain VAR."""
    program = TacProgram(
        blocks=[
            _block(
                "e",
                [],
                [_havoc("X")],
            ),
        ]
    )
    exp = explain_var(program, "Y", symbol_sorts={"X": "bv256", "Y": "bv256"})
    assert exp.defs == ()
    assert exp.refinements == ()
    text = "\n".join(format_var_explanation(exp))
    assert "(none — symbol used without a def" in text


def test_format_handles_assert_cmd_terminator() -> None:
    """Plain rendering must not crash on programs whose blocks
    terminate in AssertCmd (the materialize-validate pipeline produces
    these)."""
    program = TacProgram(
        blocks=[
            _block(
                "e",
                [],
                [
                    _havoc("X"),
                    _assume(_apply("Le", _sym("X"), _const("0x64"))),
                    AssertCmd(
                        raw="AssertCmd:1 Le(X 0x64)",
                        predicate=_apply("Le", _sym("X"), _const("0x64")),
                        message="bound",
                    ),
                ],
            ),
        ]
    )
    exp = explain_var(program, "X", symbol_sorts={"X": "bv256"})
    text = "\n".join(format_var_explanation(exp))
    assert "explain X" in text
    assert "static: [0, 100]" in text
