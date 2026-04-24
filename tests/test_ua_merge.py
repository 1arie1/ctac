"""Tests for ctac.ua.merge_asserts (the merge strategy primitive)."""

from __future__ import annotations

import pytest

from ctac.ast.nodes import (
    AssertCmd,
    AssumeExpCmd,
    ConstExpr,
    JumpCmd,
    JumpiCmd,
    SymbolRef,
)
from ctac.parse import parse_string
from ctac.ua import merge_asserts
from ctac.ua.merge import ERROR_BLOCK_ID


def _wrap(body: str, *, syms: str = "R0:bv256\n\tTA0:bool\n\tTA1:bool") -> str:
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
{body}
}}
Axioms {{
}}
Metas {{
  "0": []
}}
"""


def _cmds(program, block_id):
    for b in program.blocks:
        if b.id == block_id:
            return b.commands
    raise AssertionError(f"no block {block_id!r} in program")


def _block_ids(program) -> list[str]:
    return [b.id for b in program.blocks]


def test_single_assert_is_noop():
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd TA0\n"
            "\t\tAssertCmd TA0 \"msg\"\n"
            "\t}"
        ),
        path="<s>",
    )
    res = merge_asserts(tac.program)
    assert res.was_noop is True
    assert res.asserts_merged == 0
    assert res.error_block_id == ""
    # Program is unchanged.
    assert res.program is tac.program


def test_zero_asserts_is_noop():
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd R0\n"
            "\t}"
        ),
        path="<s>",
    )
    res = merge_asserts(tac.program)
    assert res.was_noop is True
    assert res.asserts_merged == 0


def test_two_asserts_in_separate_blocks_split_and_redirect():
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [b1] {\n"
            "\t\tAssignHavocCmd TA0\n"
            "\t\tAssertCmd TA0 \"m1\"\n"
            "\t\tJumpCmd b1\n"
            "\t}\n"
            "\tBlock b1 Succ [] {\n"
            "\t\tAssignHavocCmd TA1\n"
            "\t\tAssertCmd TA1 \"m2\"\n"
            "\t}"
        ),
        path="<s>",
    )
    res = merge_asserts(tac.program)
    assert res.was_noop is False
    assert res.asserts_merged == 2
    assert res.error_block_id == ERROR_BLOCK_ID
    ids = _block_ids(res.program)
    # Expected shape:
    # - `e` ends with `if (TA0) goto e_UA0 else goto e_UA0_land`
    # - `e_UA0_land` has a single `goto __UA_ERROR` (single-successor shim,
    #   breaks what would be a critical edge into __UA_ERROR)
    # - `e_UA0` begins with `assume TA0` and inherits e's old goto b1
    # - `b1` ends with `if (TA1) goto b1_UA<N> else goto b1_UA<N>_land`
    # - `b1_UA<N>_land` has a single `goto __UA_ERROR`
    # - `b1_UA<N>` begins with `assume TA1` and inherits empty successors
    # - `__UA_ERROR` appended last
    assert ids[0] == "e"
    assert ids[-1] == ERROR_BLOCK_ID
    assert "e_UA0" in ids
    assert "e_UA0_land" in ids
    assert any(bid.startswith("b1_UA") and not bid.endswith("_land") for bid in ids)
    assert any(bid.startswith("b1_UA") and bid.endswith("_land") for bid in ids)

    # `e` terminator is a conditional jump to (e_UA0, e_UA0_land) on TA0.
    e_cmds = _cmds(res.program, "e")
    term = e_cmds[-1]
    assert isinstance(term, JumpiCmd)
    assert term.then_target == "e_UA0"
    assert term.else_target == "e_UA0_land"
    assert term.condition == "TA0"

    # Landing block is exactly one `goto __UA_ERROR`.
    land_cmds = _cmds(res.program, "e_UA0_land")
    assert len(land_cmds) == 1
    assert isinstance(land_cmds[0], JumpCmd)
    assert land_cmds[0].target == ERROR_BLOCK_ID

    # Continuation block starts with `assume TA0`, keeps original goto b1.
    cont_cmds = _cmds(res.program, "e_UA0")
    assert isinstance(cont_cmds[0], AssumeExpCmd)
    assert cont_cmds[0].condition == SymbolRef("TA0")
    assert isinstance(cont_cmds[-1], JumpCmd) and cont_cmds[-1].target == "b1"

    # Error block is a single `assert false`.
    err_cmds = _cmds(res.program, ERROR_BLOCK_ID)
    assert len(err_cmds) == 1
    err = err_cmds[0]
    assert isinstance(err, AssertCmd)
    assert err.predicate == ConstExpr("false")


def test_assert_false_becomes_unconditional_goto():
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [b1] {\n"
            "\t\tAssignHavocCmd TA0\n"
            "\t\tAssertCmd TA0 \"first\"\n"
            "\t\tJumpCmd b1\n"
            "\t}\n"
            "\tBlock b1 Succ [] {\n"
            "\t\tAssertCmd false \"boom\"\n"
            "\t}"
        ),
        path="<s>",
    )
    res = merge_asserts(tac.program)
    assert res.asserts_merged == 2
    # b1's terminator is an unconditional goto __UA_ERROR.
    b1_cmds = _cmds(res.program, "b1")
    assert len(b1_cmds) == 1
    term = b1_cmds[0]
    assert isinstance(term, JumpCmd)
    assert term.target == ERROR_BLOCK_ID


def test_multiple_asserts_in_one_block_split_sequentially():
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd TA0\n"
            "\t\tAssignHavocCmd TA1\n"
            "\t\tAssertCmd TA0 \"m1\"\n"
            "\t\tAssertCmd TA1 \"m2\"\n"
            "\t}"
        ),
        path="<s>",
    )
    res = merge_asserts(tac.program)
    assert res.asserts_merged == 2
    # Expected order after each split: source, landing, continuation.
    # So ids[:5] = [e, e_UA0_land, e_UA0, e_UA1_land, e_UA1].
    ids = _block_ids(res.program)
    assert ids[:5] == ["e", "e_UA0_land", "e_UA0", "e_UA1_land", "e_UA1"]
    assert ids[-1] == ERROR_BLOCK_ID
    # First continuation starts with `assume TA0`.
    c0 = _cmds(res.program, "e_UA0")
    assert isinstance(c0[0], AssumeExpCmd)
    assert c0[0].condition == SymbolRef("TA0")
    # Second continuation starts with `assume TA1`.
    c1 = _cmds(res.program, "e_UA1")
    assert isinstance(c1[0], AssumeExpCmd)
    assert c1[0].condition == SymbolRef("TA1")
    # Each landing is a single `goto __UA_ERROR`.
    for land_id in ("e_UA0_land", "e_UA1_land"):
        land_cmds = _cmds(res.program, land_id)
        assert len(land_cmds) == 1
        assert isinstance(land_cmds[0], JumpCmd)
        assert land_cmds[0].target == ERROR_BLOCK_ID


def test_non_purified_predicate_raises():
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd R0\n"
            "\t\tAssertCmd Lt(R0 0x10) \"raw\"\n"
            "\t\tAssertCmd Lt(R0 0x20) \"raw2\"\n"
            "\t}",
            syms="R0:bv256",
        ),
        path="<s>",
    )
    with pytest.raises(ValueError, match="PURIFY_ASSERT"):
        merge_asserts(tac.program)


def test_existing_ua_error_block_raises():
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [__UA_ERROR] {\n"
            "\t\tAssignHavocCmd TA0\n"
            "\t\tAssertCmd TA0 \"m1\"\n"
            "\t\tJumpCmd __UA_ERROR\n"
            "\t}\n"
            "\tBlock __UA_ERROR Succ [] {\n"
            "\t\tAssertCmd false \"existing\"\n"
            "\t}"
        ),
        path="<s>",
    )
    with pytest.raises(ValueError, match="already exists"):
        merge_asserts(tac.program)


def test_ua_output_has_no_critical_edges():
    # Regression guard: ua output must be free of critical edges so that
    # sea_vc's predecessor-exclusivity encoding stays sound. An edge (u, v)
    # is critical iff |succ(u)| > 1 and |pred(v)| > 1; landing blocks break
    # the assert-site → __UA_ERROR edges that would otherwise be critical.
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [b1] {\n"
            "\t\tAssignHavocCmd TA0\n"
            "\t\tAssertCmd TA0 \"m1\"\n"
            "\t\tJumpCmd b1\n"
            "\t}\n"
            "\tBlock b1 Succ [] {\n"
            "\t\tAssignHavocCmd TA1\n"
            "\t\tAssertCmd TA1 \"m2\"\n"
            "\t}"
        ),
        path="<s>",
    )
    res = merge_asserts(tac.program)
    # Reuse the validator so this test and the smt precondition share one
    # definition of what "no critical edges" means.
    from ctac.smt.validate import ensure_no_critical_edges

    ensure_no_critical_edges(res.program)  # raises on any critical edge
