"""Tests for ctac.transform.pin Phase 2 (transformation primitives).

Covers: substitution, terminator surgery, block removal, RC-havoc
purging, cleanup, and post-condition validators.
"""

from __future__ import annotations

import pytest

from ctac.ast.nodes import (
    ApplyExpr,
    AssignExpCmd,
    AssignHavocCmd,
    AssumeExpCmd,
    ConstExpr,
    JumpCmd,
    SymbolRef,
)
from ctac.parse import parse_string
from ctac.transform.pin import (
    _cleanup,
    _drop_cfg_surgery,
    _drop_havoc_defs_for_dead_rcs,
    _fold_lor_rc_self_dominance,
    _remove_blocks,
    _substitute_in_program,
    _used_block_ids,
    assert_no_dangling_jumps,
    assert_no_orphans,
)


T = ConstExpr("true")
F = ConstExpr("false")


def _wrap(blocks_text: str, *, syms: str = "B0:bool\n\tB1:bool") -> str:
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


# ------------------------------------------------- substitution


def test_substitute_replaces_in_assume():
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssumeExpCmd LAnd(B0 B1)\n"
            "\t}\n"
        ),
        path="<s>",
    )
    out = _substitute_in_program(tac.program, {"B0": T})
    assume = out.blocks[0].commands[0]
    assert isinstance(assume, AssumeExpCmd)
    assert assume.condition == ApplyExpr("LAnd", (T, SymbolRef("B1")))


def test_substitute_replaces_in_assign_rhs():
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignExpCmd R0 Ite(B0 0x0 0x1)\n"
            "\t}\n",
            syms="R0:bv256\n\tB0:bool",
        ),
        path="<s>",
    )
    out = _substitute_in_program(tac.program, {"B0": F})
    asn = out.blocks[0].commands[0]
    assert isinstance(asn, AssignExpCmd)
    # RHS becomes Ite(false, 0x0, 0x1) — substitution only; folding is later.
    assert asn.rhs == ApplyExpr("Ite", (F, ConstExpr("0x0"), ConstExpr("0x1")))


def test_substitute_empty_mapping_is_noop():
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssumeExpCmd B0\n"
            "\t}\n"
        ),
        path="<s>",
    )
    out = _substitute_in_program(tac.program, {})
    assert out is tac.program


# -------------------------------------- terminator surgery (CFG drop)


def test_drop_surgery_jumpi_with_dead_then_target():
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
    out = _drop_cfg_surgery(tac.program, frozenset({"a"}), {}, {})
    e = out.blocks[0]
    assert e.id == "e"
    assert e.successors == ["b"]
    assert isinstance(e.commands[-1], JumpCmd)
    assert e.commands[-1].target == "b"


def test_drop_surgery_jumpi_with_constant_condition():
    """B0 bound to true -> JumpiCmd folded to JumpCmd(then)."""
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [a, b] {\n"
            "\t\tJumpiCmd a b B0\n"
            "\t}\n"
            "\tBlock a Succ [] {\n"
            "\t\tNoSuchCmd\n"
            "\t}\n"
            "\tBlock b Succ [] {\n"
            "\t\tNoSuchCmd\n"
            "\t}\n"
        ),
        path="<s>",
    )
    out = _drop_cfg_surgery(tac.program, frozenset(), {"B0": T}, {})
    e = out.blocks[0]
    assert e.successors == ["a"]
    assert isinstance(e.commands[-1], JumpCmd)
    assert e.commands[-1].target == "a"


def test_drop_surgery_unconditional_jump_to_dead_raises():
    """Phase 1 contract: unconditional jump to dead means caller is dead too."""
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [a] {\n"
            "\t\tJumpCmd a\n"
            "\t}\n"
            "\tBlock a Succ [] {\n"
            "\t\tNoSuchCmd\n"
            "\t}\n"
        ),
        path="<s>",
    )
    with pytest.raises(AssertionError, match="unconditional jump to dead"):
        _drop_cfg_surgery(tac.program, frozenset({"a"}), {}, {})


def test_drop_surgery_both_jumpi_targets_dead_raises():
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [a, b] {\n"
            "\t\tJumpiCmd a b B0\n"
            "\t}\n"
            "\tBlock a Succ [] {\n"
            "\t\tNoSuchCmd\n"
            "\t}\n"
            "\tBlock b Succ [] {\n"
            "\t\tNoSuchCmd\n"
            "\t}\n"
        ),
        path="<s>",
    )
    with pytest.raises(AssertionError, match="both dead"):
        _drop_cfg_surgery(tac.program, frozenset({"a", "b"}), {}, {})


def test_drop_surgery_keeps_unrelated_blocks_intact():
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
    out = _drop_cfg_surgery(tac.program, frozenset(), {}, {})
    # No-op: dead set empty, no folds requested.
    assert [b.id for b in out.blocks] == ["e", "exit"]


# -------------------------------------------------- block removal


def test_remove_blocks_drops_blocks_and_cleans_successor_lists():
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [a, b] {\n"
            "\t\tNoSuchCmd\n"
            "\t}\n"
            "\tBlock a Succ [] {\n"
            "\t\tNoSuchCmd\n"
            "\t}\n"
            "\tBlock b Succ [] {\n"
            "\t\tNoSuchCmd\n"
            "\t}\n"
        ),
        path="<s>",
    )
    out = _remove_blocks(tac.program, frozenset({"a"}))
    assert {b.id for b in out.blocks} == {"e", "b"}
    e = next(b for b in out.blocks if b.id == "e")
    assert e.successors == ["b"]


def test_remove_blocks_empty_dead_is_noop():
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tNoSuchCmd\n"
            "\t}\n"
        ),
        path="<s>",
    )
    out = _remove_blocks(tac.program, frozenset())
    assert out is tac.program


# -------------------------------------------------- RC havoc purging


def test_drop_havoc_defs_removes_dead_rc_havocs():
    """A block can host a havoc def for an RC of a different (dead) block;
    purging that havoc is part of pin's contract."""
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd ReachabilityCertoraa\n"
            "\t\tAssignHavocCmd ReachabilityCertorab\n"
            "\t}\n",
            syms="B0:bool",
        ),
        path="<s>",
    )
    out = _drop_havoc_defs_for_dead_rcs(tac.program, frozenset({"a"}))
    cmds = out.blocks[0].commands
    havoc_lhs = [c.lhs for c in cmds if isinstance(c, AssignHavocCmd)]
    assert havoc_lhs == ["ReachabilityCertorab"]


def test_drop_havoc_defs_noop_when_no_dead():
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd ReachabilityCertoraa\n"
            "\t}\n",
            syms="B0:bool",
        ),
        path="<s>",
    )
    out = _drop_havoc_defs_for_dead_rcs(tac.program, frozenset())
    assert out is tac.program


# ------------------------------------------------- cleanup integration


def test_cleanup_folds_bool_const_in_assume():
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssumeExpCmd LAnd(true LOr(false B0))\n"
            "\t}\n"
        ),
        path="<s>",
    )
    out = _cleanup(tac.program)
    cond = out.blocks[0].commands[0]
    assert isinstance(cond, AssumeExpCmd)
    assert cond.condition == SymbolRef("B0")


# ----------------------------------------------------- post-conditions


def test_assert_no_orphans_passes_on_clean_program():
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
    assert_no_orphans(tac.program)  # no exception


def test_assert_no_orphans_fails_on_unreachable_block():
    """Build a program with an orphan block that's not reachable from entry."""
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [exit] {\n"
            "\t\tJumpCmd exit\n"
            "\t}\n"
            "\tBlock exit Succ [] {\n"
            "\t\tNoSuchCmd\n"
            "\t}\n"
            "\tBlock orphan Succ [] {\n"
            "\t\tNoSuchCmd\n"
            "\t}\n"
        ),
        path="<s>",
    )
    with pytest.raises(AssertionError, match="orphan"):
        assert_no_orphans(tac.program)


def test_assert_no_dangling_jumps_passes_on_clean_program():
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
    assert_no_dangling_jumps(tac.program)


def test_used_block_ids_collects_jump_targets():
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [a, b] {\n"
            "\t\tJumpiCmd a b B0\n"
            "\t}\n"
            "\tBlock a Succ [] {\n"
            "\t\tNoSuchCmd\n"
            "\t}\n"
            "\tBlock b Succ [] {\n"
            "\t\tNoSuchCmd\n"
            "\t}\n"
        ),
        path="<s>",
    )
    used = _used_block_ids(tac.program)
    assert used == {"a", "b"}


# ----------------------------- LOr-of-RC self-dominance fold


def test_lor_rc_folds_when_operands_match_predecessors():
    """LOr(RC[a], RC[b]) at join with preds={a,b} folds to true."""
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [a, b] {\n"
            "\t\tJumpiCmd a b B0\n"
            "\t}\n"
            "\tBlock a Succ [join] {\n"
            "\t\tJumpCmd join\n"
            "\t}\n"
            "\tBlock b Succ [join] {\n"
            "\t\tJumpCmd join\n"
            "\t}\n"
            "\tBlock join Succ [exit] {\n"
            "\t\tAssumeExpCmd "
            "LOr(ReachabilityCertoraa ReachabilityCertorab)\n"
            "\t\tJumpCmd exit\n"
            "\t}\n"
            "\tBlock exit Succ [] {\n"
            "\t\tNoSuchCmd\n"
            "\t}\n"
        ),
        path="<s>",
    )
    out = _fold_lor_rc_self_dominance(tac.program)
    join = next(b for b in out.blocks if b.id == "join")
    assume = join.commands[0]
    assert isinstance(assume, AssumeExpCmd)
    assert assume.condition == T


def test_lor_rc_no_fold_when_operands_strict_subset():
    """LOr(RC[a]) at join with preds={a,b} does not fold (could be false on b path)."""
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [a, b] {\n"
            "\t\tJumpiCmd a b B0\n"
            "\t}\n"
            "\tBlock a Succ [join] {\n"
            "\t\tJumpCmd join\n"
            "\t}\n"
            "\tBlock b Succ [join] {\n"
            "\t\tJumpCmd join\n"
            "\t}\n"
            "\tBlock join Succ [exit] {\n"
            "\t\tAssumeExpCmd "
            "LOr(ReachabilityCertoraa ReachabilityCertoraa)\n"
            "\t\tJumpCmd exit\n"
            "\t}\n"
            "\tBlock exit Succ [] {\n"
            "\t\tNoSuchCmd\n"
            "\t}\n"
        ),
        path="<s>",
    )
    out = _fold_lor_rc_self_dominance(tac.program)
    join = next(b for b in out.blocks if b.id == "join")
    assume = join.commands[0]
    assert isinstance(assume, AssumeExpCmd)
    assert isinstance(assume.condition, ApplyExpr)
    assert assume.condition.op == "LOr"


def test_lor_rc_folds_inside_nested_ite():
    """LOr inside an Ite gate is rewritten in-place; outer expression
    structure preserved."""
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [a, b] {\n"
            "\t\tJumpiCmd a b B0\n"
            "\t}\n"
            "\tBlock a Succ [join] {\n"
            "\t\tJumpCmd join\n"
            "\t}\n"
            "\tBlock b Succ [join] {\n"
            "\t\tJumpCmd join\n"
            "\t}\n"
            "\tBlock join Succ [exit] {\n"
            "\t\tAssumeExpCmd "
            "Ite(LOr(ReachabilityCertoraa ReachabilityCertorab) B0 B1)\n"
            "\t\tJumpCmd exit\n"
            "\t}\n"
            "\tBlock exit Succ [] {\n"
            "\t\tNoSuchCmd\n"
            "\t}\n"
        ),
        path="<s>",
    )
    out = _fold_lor_rc_self_dominance(tac.program)
    join = next(b for b in out.blocks if b.id == "join")
    assume = join.commands[0]
    assert isinstance(assume, AssumeExpCmd)
    # Outer Ite preserved; gate became true.
    assert isinstance(assume.condition, ApplyExpr)
    assert assume.condition.op == "Ite"
    assert assume.condition.args[0] == T
    assert assume.condition.args[1] == SymbolRef("B0")
    assert assume.condition.args[2] == SymbolRef("B1")


def test_lor_rc_no_fold_when_non_rc_operand():
    """LOr(RC[a], B0) — non-RC operand disqualifies the rule."""
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [a, b] {\n"
            "\t\tJumpiCmd a b B0\n"
            "\t}\n"
            "\tBlock a Succ [join] {\n"
            "\t\tJumpCmd join\n"
            "\t}\n"
            "\tBlock b Succ [join] {\n"
            "\t\tJumpCmd join\n"
            "\t}\n"
            "\tBlock join Succ [exit] {\n"
            "\t\tAssumeExpCmd LOr(ReachabilityCertoraa B0)\n"
            "\t\tJumpCmd exit\n"
            "\t}\n"
            "\tBlock exit Succ [] {\n"
            "\t\tNoSuchCmd\n"
            "\t}\n"
        ),
        path="<s>",
    )
    out = _fold_lor_rc_self_dominance(tac.program)
    join = next(b for b in out.blocks if b.id == "join")
    assume = join.commands[0]
    assert isinstance(assume, AssumeExpCmd)
    assert isinstance(assume.condition, ApplyExpr)
    assert assume.condition.op == "LOr"
