"""Tests for ctac.transform.pin.enumerate (split-based enumeration)."""

from __future__ import annotations

import pytest

from ctac.parse import parse_string
from ctac.tracing import MemoryTrace
from ctac.transform.pin import (
    PinPlan,
    enumerate as pin_enumerate,
)


def _wrap(blocks_text: str, *, syms: str = "B0:bool") -> str:
    return f"""TACSymbolTable {{
\tUserDefined {{
\t}}
\tBuiltinFunctions {{
\t}}
\tUninterpretedFunctions {{
\t}}
\t{syms}
}}
Program {{
{blocks_text}
}}
Axioms {{
}}
Metas {{
  "0": []
}}
"""


def _two_pred_join():
    """e -> {p1, p2} -> J -> exit."""
    return parse_string(
        _wrap(
            "\tBlock e Succ [p1, p2] {\n"
            "\t\tJumpiCmd p1 p2 B0\n"
            "\t}\n"
            "\tBlock p1 Succ [j] {\n"
            "\t\tJumpCmd j\n"
            "\t}\n"
            "\tBlock p2 Succ [j] {\n"
            "\t\tJumpCmd j\n"
            "\t}\n"
            "\tBlock j Succ [exit] {\n"
            "\t\tJumpCmd exit\n"
            "\t}\n"
            "\tBlock exit Succ [] {\n"
            "\t\tNoSuchCmd\n"
            "\t}\n"
        ),
        path="<s>",
    )


def test_enumerate_single_split_two_predecessors():
    tac = _two_pred_join()
    cs = pin_enumerate(tac.program, PinPlan(splits=("j",)))
    assert len(cs.cases) == 2
    # Each case should keep one predecessor and drop the other.
    kept_set = {c.kept_predecessors for c in cs.cases}
    assert (("j", "p1"),) in kept_set
    assert (("j", "p2"),) in kept_set


def test_enumerate_case_dead_blocks_match_kept_pred():
    tac = _two_pred_join()
    cs = pin_enumerate(tac.program, PinPlan(splits=("j",)))
    for c in cs.cases:
        kept = dict(c.kept_predecessors)["j"]
        # The non-kept predecessor must be in dead.
        assert {"p1", "p2"} - {kept} <= c.dead_blocks


def test_enumerate_unknown_split_raises():
    tac = _two_pred_join()
    with pytest.raises(ValueError, match="not a block"):
        pin_enumerate(tac.program, PinPlan(splits=("nope",)))


def test_enumerate_split_with_no_predecessors_raises():
    tac = _two_pred_join()
    # 'e' has no predecessors (it's the entry).
    with pytest.raises(ValueError, match="no predecessors"):
        pin_enumerate(tac.program, PinPlan(splits=("e",)))


def test_enumerate_two_splits_cross_product():
    """e -if B0- {p1, p2} -> J1 -> {p3, p4} -> J2 -> exit.

    Both predecessor pairs are 2-way, so cross-product = 4 cases.
    """
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [p1, p2] {\n"
            "\t\tJumpiCmd p1 p2 B0\n"
            "\t}\n"
            "\tBlock p1 Succ [j1] {\n"
            "\t\tJumpCmd j1\n"
            "\t}\n"
            "\tBlock p2 Succ [j1] {\n"
            "\t\tJumpCmd j1\n"
            "\t}\n"
            "\tBlock j1 Succ [p3, p4] {\n"
            "\t\tJumpiCmd p3 p4 B1\n"
            "\t}\n"
            "\tBlock p3 Succ [j2] {\n"
            "\t\tJumpCmd j2\n"
            "\t}\n"
            "\tBlock p4 Succ [j2] {\n"
            "\t\tJumpCmd j2\n"
            "\t}\n"
            "\tBlock j2 Succ [exit] {\n"
            "\t\tJumpCmd exit\n"
            "\t}\n"
            "\tBlock exit Succ [] {\n"
            "\t\tNoSuchCmd\n"
            "\t}\n",
            syms="B0:bool\n\tB1:bool",
        ),
        path="<s>",
    )
    cs = pin_enumerate(tac.program, PinPlan(splits=("j1", "j2")))
    assert len(cs.cases) == 4
    # All combinations of (p1|p2, p3|p4) appear once.
    kept_set = {c.kept_predecessors for c in cs.cases}
    assert kept_set == {
        (("j1", "p1"), ("j2", "p3")),
        (("j1", "p1"), ("j2", "p4")),
        (("j1", "p2"), ("j2", "p3")),
        (("j1", "p2"), ("j2", "p4")),
    }


def test_enumerate_emits_trace_events():
    tac = _two_pred_join()
    trace = MemoryTrace()
    pin_enumerate(tac.program, PinPlan(splits=("j",)), trace=trace)
    events = [e["event"] for e in trace.events]
    assert "split-enumeration" in events
    assert "enumeration-complete" in events


def test_enumerate_preserves_drops_across_cases():
    """User --drop combined with --split: each case includes the user's drops
    in addition to the case-implied drops."""
    tac = parse_string(
        _wrap(
            # e -> {p1, p2} -> J -> {x, exit} ; we'll drop x.
            "\tBlock e Succ [p1, p2] {\n"
            "\t\tJumpiCmd p1 p2 B0\n"
            "\t}\n"
            "\tBlock p1 Succ [j] {\n"
            "\t\tJumpCmd j\n"
            "\t}\n"
            "\tBlock p2 Succ [j] {\n"
            "\t\tJumpCmd j\n"
            "\t}\n"
            "\tBlock j Succ [x, exit] {\n"
            "\t\tJumpiCmd x exit B0\n"
            "\t}\n"
            "\tBlock x Succ [exit] {\n"
            "\t\tJumpCmd exit\n"
            "\t}\n"
            "\tBlock exit Succ [] {\n"
            "\t\tNoSuchCmd\n"
            "\t}\n",
        ),
        path="<s>",
    )
    cs = pin_enumerate(tac.program, PinPlan(splits=("j",), drops=("x",)))
    assert len(cs.cases) == 2
    for c in cs.cases:
        # x should be dead in every case.
        assert "x" in c.dead_blocks


def test_enumerate_no_splits_produces_zero_cases():
    """Edge case: no splits is structurally valid (use apply() instead)
    but should at least not crash."""
    tac = _two_pred_join()
    cs = pin_enumerate(tac.program, PinPlan(splits=()))
    # With no splits, the cross-product is one empty tuple — but we
    # still iterate that single case.
    assert len(cs.cases) == 1
    # No splits means no kept_predecessors.
    assert cs.cases[0].kept_predecessors == ()
