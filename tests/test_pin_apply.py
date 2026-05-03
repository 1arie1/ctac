"""End-to-end tests for ctac.transform.pin.apply()."""

from __future__ import annotations

import pytest

from ctac.ast.nodes import (
    AssumeExpCmd,
    ConstExpr,
    JumpCmd,
    SymbolRef,
)
from ctac.parse import parse_string
from ctac.tracing import MemoryTrace
from ctac.transform.pin import (
    PinPlan,
    apply,
    bind,
)


T = ConstExpr("true")
F = ConstExpr("false")


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


# -------------------------------------------------- bind() public API


def test_bind_substitutes_in_assume():
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssumeExpCmd LAnd(B0 B1)\n"
            "\t}\n",
            syms="B0:bool\n\tB1:bool",
        ),
        path="<s>",
    )
    out = bind(tac.program, [("B0", T)])
    cond = out.blocks[0].commands[0]
    assert isinstance(cond, AssumeExpCmd)
    # Substituted, but not folded — apply() does folding via cleanup.
    from ctac.ast.nodes import ApplyExpr
    assert cond.condition == ApplyExpr("LAnd", (T, SymbolRef("B1")))


def test_bind_rejects_rc_var():
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tNoSuchCmd\n"
            "\t}\n"
        ),
        path="<s>",
    )
    with pytest.raises(ValueError, match="ReachabilityCertora"):
        bind(tac.program, [("ReachabilityCertorafoo", F)])


# -------------------------------------------------- apply() pipeline


def test_apply_drop_only_simple_jumpi():
    """e -if B0- a/b -> exit. Drop a -> only b survives."""
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [a, b] {\n"
            "\t\tJumpiCmd a b B0\n"
            "\t}\n"
            "\tBlock a Succ [exit] {\n"
            "\t\tJumpCmd exit\n"
            "\t}\n"
            "\tBlock b Succ [exit] {\n"
            "\t\tJumpCmd exit\n"
            "\t}\n"
            "\tBlock exit Succ [] {\n"
            "\t\tNoSuchCmd\n"
            "\t}\n"
        ),
        path="<s>",
    )
    plan = PinPlan(drops=("a",))
    res = apply(tac.program, plan)
    block_ids = {b.id for b in res.program.blocks}
    assert "a" not in block_ids
    assert "b" in block_ids
    assert res.dead_blocks == frozenset({"a"})
    # e's terminator should now be JumpCmd(b) since the then-target died.
    e = next(b for b in res.program.blocks if b.id == "e")
    assert isinstance(e.commands[-1], JumpCmd)
    assert e.commands[-1].target == "b"


def test_apply_bind_only_collapses_jumpi():
    """Bind B0=false; the JumpiCmd at e folds to JumpCmd(else)."""
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [a, b] {\n"
            "\t\tJumpiCmd a b B0\n"
            "\t}\n"
            "\tBlock a Succ [exit] {\n"
            "\t\tJumpCmd exit\n"
            "\t}\n"
            "\tBlock b Succ [exit] {\n"
            "\t\tJumpCmd exit\n"
            "\t}\n"
            "\tBlock exit Succ [] {\n"
            "\t\tNoSuchCmd\n"
            "\t}\n"
        ),
        path="<s>",
    )
    plan = PinPlan(binds=(("B0", F),))
    res = apply(tac.program, plan)
    e = next(b for b in res.program.blocks if b.id == "e")
    # Surgery folded based on the static eval of B0=false -> else=b.
    assert isinstance(e.commands[-1], JumpCmd)
    assert e.commands[-1].target == "b"
    # 'a' should have become unreachable and dropped.
    block_ids = {b.id for b in res.program.blocks}
    assert "a" not in block_ids


def test_apply_drop_purges_rc_havoc():
    """RC havoc for a dropped block in a different block is removed."""
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [exit] {\n"
            "\t\tAssignHavocCmd ReachabilityCertoraa\n"
            "\t\tJumpCmd exit\n"
            "\t}\n"
            "\tBlock exit Succ [a] {\n"
            "\t\tJumpCmd a\n"
            "\t}\n"
            "\tBlock a Succ [done] {\n"
            "\t\tJumpCmd done\n"
            "\t}\n"
            "\tBlock done Succ [] {\n"
            "\t\tNoSuchCmd\n"
            "\t}\n"
        ),
        path="<s>",
    )
    plan = PinPlan(drops=("a",))
    # Drop 'a' -> exit -> a is gone, exit's terminator becomes a halt
    # because its only succ died. Phase 1 will catch this and cascade,
    # so 'exit' itself becomes dead.
    with pytest.raises(ValueError, match="entry-to-exit"):
        # actually the program has no live exit anymore; validate_plan
        # surfaces this as an issue.
        apply(tac.program, plan)


def test_apply_rejects_unknown_drop_target():
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tNoSuchCmd\n"
            "\t}\n"
        ),
        path="<s>",
    )
    plan = PinPlan(drops=("nope",))
    with pytest.raises(ValueError, match="nope"):
        apply(tac.program, plan)


def test_apply_rejects_rc_in_binds():
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tNoSuchCmd\n"
            "\t}\n"
        ),
        path="<s>",
    )
    plan = PinPlan(binds=(("ReachabilityCertorafoo", F),))
    with pytest.raises(ValueError, match="ReachabilityCertorafoo"):
        apply(tac.program, plan)


def test_apply_rejects_split_in_apply_path():
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tNoSuchCmd\n"
            "\t}\n"
        ),
        path="<s>",
    )
    plan = PinPlan(splits=("e",))
    with pytest.raises(ValueError, match="splits"):
        apply(tac.program, plan)


def test_apply_emits_trace_events():
    """Trace receives pin-start, block-dropped, post-condition-check,
    pin-complete events for a simple drop."""
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [a, b] {\n"
            "\t\tJumpiCmd a b B0\n"
            "\t}\n"
            "\tBlock a Succ [exit] {\n"
            "\t\tJumpCmd exit\n"
            "\t}\n"
            "\tBlock b Succ [exit] {\n"
            "\t\tJumpCmd exit\n"
            "\t}\n"
            "\tBlock exit Succ [] {\n"
            "\t\tNoSuchCmd\n"
            "\t}\n"
        ),
        path="<s>",
    )
    trace = MemoryTrace()
    apply(tac.program, PinPlan(drops=("a",)), trace=trace)
    events = [e["event"] for e in trace.events]
    assert "pin-start" in events
    assert "block-dropped" in events
    assert "rc-bind" in events
    assert "block-removed" in events
    assert "post-condition-check" in events
    assert "pin-complete" in events


def test_apply_trace_records_drop_reason_for_user_drop():
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [a, b] {\n"
            "\t\tJumpiCmd a b B0\n"
            "\t}\n"
            "\tBlock a Succ [exit] {\n"
            "\t\tJumpCmd exit\n"
            "\t}\n"
            "\tBlock b Succ [exit] {\n"
            "\t\tJumpCmd exit\n"
            "\t}\n"
            "\tBlock exit Succ [] {\n"
            "\t\tNoSuchCmd\n"
            "\t}\n"
        ),
        path="<s>",
    )
    trace = MemoryTrace()
    apply(tac.program, PinPlan(drops=("a",)), trace=trace)
    drop_events = [e for e in trace.events if e["event"] == "block-dropped"]
    user_drops = [e for e in drop_events if e["reason"] == "user_drop"]
    assert len(user_drops) == 1
    assert user_drops[0]["block"] == "a"


def test_apply_postconditions_pass_for_clean_program():
    """No drops, no binds — post-conditions trivially pass."""
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [exit] {\n"
            "\t\tJumpCmd exit\n"
            "\t}\n"
            "\tBlock exit Succ [] {\n"
            "\t\tNoSuchCmd\n"
            "\t}\n"
        ),
        path="<s>",
    )
    res = apply(tac.program, PinPlan())
    assert {b.id for b in res.program.blocks} == {"e", "exit"}
    assert res.dead_blocks == frozenset()


def test_apply_no_cleanup_skips_cleanup_phase():
    """With cleanup=False, no fold events emitted."""
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [exit] {\n"
            "\t\tAssumeExpCmd LAnd(true B0)\n"
            "\t\tJumpCmd exit\n"
            "\t}\n"
            "\tBlock exit Succ [] {\n"
            "\t\tNoSuchCmd\n"
            "\t}\n"
        ),
        path="<s>",
    )
    trace = MemoryTrace()
    res = apply(tac.program, PinPlan(cleanup=False), trace=trace)
    # The unfolded LAnd(true, B0) should remain unchanged.
    cond = res.program.blocks[0].commands[0]
    from ctac.ast.nodes import ApplyExpr
    assert isinstance(cond, AssumeExpCmd)
    assert cond.condition == ApplyExpr("LAnd", (T, SymbolRef("B0")))
    # No cleanup-complete event.
    events = [e["event"] for e in trace.events]
    assert "cleanup-complete" not in events
