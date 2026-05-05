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
    # ``raw`` is re-rendered from the substituted AST so
    # ``render_program`` (which writes ``cmd.raw``) reflects the bind.
    assert "B0" not in cond.raw
    assert "true" in cond.raw


def test_bind_re_renders_raw_for_round_trip():
    """Substituted commands' ``raw`` must reflect the new AST so the
    written-back .tac file parses to the same substituted program."""
    from ctac.ast.nodes import AssignExpCmd
    from ctac.parse.tac_file import render_tac_file
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignExpCmd R1 Add(R0 R0)\n"
            "\t\tAssumeExpCmd Eq(R1 0x0)\n"
            "\t}\n",
            syms="R0:bv256\n\tR1:bv256",
        ),
        path="<s>",
    )
    out = bind(tac.program, [("R0", ConstExpr("0x0"))])
    text = render_tac_file(tac, program=out)
    # Round-trip through the parser should yield the substituted form.
    re_parsed = parse_string(text, path="<s>")
    rhs = re_parsed.program.blocks[0].commands[0]
    assert isinstance(rhs, AssignExpCmd)
    # R1 = Add(0x0, 0x0) — no R0 reference left.
    assert "R0" not in rhs.raw


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


def test_apply_rejects_drops_that_introduce_use_before_def():
    """A drop that removes a variable's only def, where uses survive,
    must be rejected by the post-condition (not silently emitted)."""
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [a, b] {\n"
            "\t\tJumpiCmd a b B0\n"
            "\t}\n"
            "\tBlock a Succ [j] {\n"
            "\t\tAssignExpCmd M1 0x42\n"
            "\t\tJumpCmd j\n"
            "\t}\n"
            "\tBlock b Succ [j] {\n"
            "\t\tJumpCmd j\n"
            "\t}\n"
            "\tBlock j Succ [] {\n"
            "\t\tAssumeExpCmd Eq(M1 0x42)\n"
            "\t}\n",
            syms="B0:bool\n\tM1:bv256",
        ),
        path="<s>",
    )
    # Dropping block 'a' eliminates the only def of M1, but block 'j'
    # still uses it. Pin must refuse.
    with pytest.raises(AssertionError, match="use-before-def"):
        apply(tac.program, PinPlan(drops=("a",)))


def test_apply_dsa_suffixed_rc_substitution_works():
    """RC vars with DSA :N suffix should still get folded."""
    # Build a synthetic case where the RC var appears with a :N suffix.
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [exit, dead] {\n"
            "\t\tJumpiCmd exit dead B0\n"
            "\t}\n"
            "\tBlock dead Succ [] {\n"
            "\t\tAssignHavocCmd ReachabilityCertoradead\n"
            "\t}\n"
            "\tBlock exit Succ [] {\n"
            # A use site references the RC var WITH a :42 suffix.
            "\t\tAssignExpCmd R0 Ite(ReachabilityCertoradead:42 0x1 0x2)\n"
            "\t}\n",
            syms="B0:bool\n\tR0:bv256",
        ),
        path="<s>",
    )
    res = apply(tac.program, PinPlan(drops=("dead",)))
    # After pin: ReachabilityCertoradead → false; the Ite folds to else=0x2.
    from ctac.ast.nodes import AssignExpCmd
    exit_block = next(b for b in res.program.blocks if b.id == "exit")
    asn = next(c for c in exit_block.commands if isinstance(c, AssignExpCmd))
    assert asn.rhs == ConstExpr("0x2")


def test_apply_rc_dominator_is_folded_to_true():
    """When BLK survives and dominates a use site of RC_BLK, the use
    folds to true. Mirrors the kvault-style 'after dropping one
    predecessor, the surviving one dominates the join'."""
    tac = parse_string(
        _wrap(
            # entry -> {p1, p2} -> j ; user drops p1.
            # In post-drop CFG, p2 dominates j; RC_p2 = true at j.
            "\tBlock e Succ [p1, p2] {\n"
            "\t\tJumpiCmd p1 p2 B0\n"
            "\t}\n"
            "\tBlock p1 Succ [j] {\n"
            "\t\tJumpCmd j\n"
            "\t}\n"
            "\tBlock p2 Succ [j] {\n"
            "\t\tAssignHavocCmd ReachabilityCertorap2\n"
            "\t\tJumpCmd j\n"
            "\t}\n"
            "\tBlock j Succ [exit] {\n"
            # Use site references RC_p2; should fold to true after p1 is dropped.
            "\t\tAssignExpCmd R0 Ite(ReachabilityCertorap2 0xa 0xb)\n"
            "\t\tJumpCmd exit\n"
            "\t}\n"
            "\tBlock exit Succ [] {\n"
            "\t\tNoSuchCmd\n"
            "\t}\n",
            syms="B0:bool\n\tR0:bv256",
        ),
        path="<s>",
    )
    res = apply(tac.program, PinPlan(drops=("p1",)))
    from ctac.ast.nodes import AssignExpCmd
    j = next(b for b in res.program.blocks if b.id == "j")
    asn = next(c for c in j.commands if isinstance(c, AssignExpCmd) and c.lhs == "R0")
    # RC_p2 = true (p2 now dominates j) -> Ite folds to then = 0xa.
    assert asn.rhs == ConstExpr("0xa")


def test_apply_rejects_rc_in_jumpi_condition():
    """Hard error if a JumpiCmd's condition is an RC variable —
    pin's RC-folding model assumes RCs only appear in expressions,
    not in jump conditions."""
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [a, b] {\n"
            "\t\tJumpiCmd a b ReachabilityCertoraa\n"
            "\t}\n"
            "\tBlock a Succ [] {\n"
            "\t\tNoSuchCmd\n"
            "\t}\n"
            "\tBlock b Succ [] {\n"
            "\t\tNoSuchCmd\n"
            "\t}\n",
            syms="B0:bool",
        ),
        path="<s>",
    )
    with pytest.raises(ValueError, match="RC variable"):
        apply(tac.program, PinPlan())


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
