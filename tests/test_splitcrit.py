"""Tests for ctac.splitcrit.split_critical_edges."""

from __future__ import annotations

from ctac.ast.nodes import JumpCmd, JumpiCmd
from ctac.parse import parse_string
from ctac.smt.validate import ensure_no_critical_edges
from ctac.splitcrit import split_critical_edges


def _wrap(body: str, *, syms: str = "c:bool") -> str:
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


def _ids(program) -> list[str]:
    return [b.id for b in program.blocks]


def _cmds(program, block_id):
    for b in program.blocks:
        if b.id == block_id:
            return b.commands
    raise AssertionError(f"no block {block_id!r} in program")


def test_noop_when_no_critical_edges():
    # Simple diamond: edges are all non-critical (each end has exactly
    # one pred or one succ).
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [a, b] {\n"
            "\t\tAssignExpCmd c true\n"
            "\t\tJumpiCmd a b c\n"
            "\t}\n"
            "\tBlock a Succ [j] {\n"
            "\t\tJumpCmd j\n"
            "\t}\n"
            "\tBlock b Succ [j] {\n"
            "\t\tJumpCmd j\n"
            "\t}\n"
            "\tBlock j Succ [] {\n"
            "\t}"
        ),
        path="<s>",
    )
    res = split_critical_edges(tac.program)
    assert res.was_noop is True
    assert res.shims_added == 0
    assert res.program is tac.program


def test_splits_single_critical_edge():
    # u -> v and u -> w with v also reachable from w; v has 2 preds,
    # u has 2 succs => (u, v) is critical.
    tac = parse_string(
        _wrap(
            "\tBlock u Succ [v, w] {\n"
            "\t\tAssignExpCmd c true\n"
            "\t\tJumpiCmd v w c\n"
            "\t}\n"
            "\tBlock w Succ [v] {\n"
            "\t\tJumpCmd v\n"
            "\t}\n"
            "\tBlock v Succ [] {\n"
            "\t}"
        ),
        path="<s>",
    )
    res = split_critical_edges(tac.program)
    assert res.was_noop is False
    assert res.shims_added == 1
    assert ("u", "v") in res.edges_split
    # The shim block exists with id `u_to_v`, single JumpCmd v.
    ids = _ids(res.program)
    assert "u_to_v" in ids
    shim_cmds = _cmds(res.program, "u_to_v")
    assert len(shim_cmds) == 1
    assert isinstance(shim_cmds[0], JumpCmd) and shim_cmds[0].target == "v"
    # u's terminator is rewritten to point at the shim.
    u_term = _cmds(res.program, "u")[-1]
    assert isinstance(u_term, JumpiCmd)
    assert u_term.then_target == "u_to_v"
    assert u_term.else_target == "w"
    # No critical edges remain.
    ensure_no_critical_edges(res.program)


def test_splits_both_branches_when_both_critical():
    # Both (u, v) and (u, w) critical: each end has multi-pred+multi-succ.
    tac = parse_string(
        _wrap(
            "\tBlock u Succ [v, w] {\n"
            "\t\tAssignExpCmd c true\n"
            "\t\tJumpiCmd v w c\n"
            "\t}\n"
            "\tBlock a Succ [v] {\n"
            "\t\tJumpCmd v\n"
            "\t}\n"
            "\tBlock b Succ [w] {\n"
            "\t\tJumpCmd w\n"
            "\t}\n"
            "\tBlock v Succ [] {\n"
            "\t}\n"
            "\tBlock w Succ [] {\n"
            "\t}"
        ),
        path="<s>",
    )
    # Add fake predecessors by declaring a/b as also-valid entries —
    # the parser accepts them as blocks. a->v and b->w each add 1 pred.
    res = split_critical_edges(tac.program)
    assert res.shims_added == 2
    assert {("u", "v"), ("u", "w")} <= set(res.edges_split)
    u_term = _cmds(res.program, "u")[-1]
    assert isinstance(u_term, JumpiCmd)
    assert u_term.then_target == "u_to_v"
    assert u_term.else_target == "u_to_w"
    ensure_no_critical_edges(res.program)


def test_shim_id_collision_uses_suffix():
    # Pre-seed a block named `u_to_v` so the shim has to pick a different
    # id. The synthetic block is disconnected — still a legal program.
    tac = parse_string(
        _wrap(
            "\tBlock u Succ [v, w] {\n"
            "\t\tAssignExpCmd c true\n"
            "\t\tJumpiCmd v w c\n"
            "\t}\n"
            "\tBlock w Succ [v] {\n"
            "\t\tJumpCmd v\n"
            "\t}\n"
            "\tBlock u_to_v Succ [] {\n"
            "\t}\n"
            "\tBlock v Succ [] {\n"
            "\t}"
        ),
        path="<s>",
    )
    res = split_critical_edges(tac.program)
    assert res.shims_added == 1
    ids = _ids(res.program)
    # The pre-existing u_to_v is still there; the new shim has a suffix.
    assert "u_to_v" in ids
    assert "u_to_v_1" in ids
    assert _cmds(res.program, "u_to_v_1")[0].target == "v"


def test_ua_chain_is_cleaned_when_fed_through_split():
    # The ua transform now emits landing blocks, so its output is
    # already critical-edge-free. Feeding it through split_critical_edges
    # should be a no-op.
    from ctac.ua import merge_asserts

    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd TA0\n"
            "\t\tAssignHavocCmd TA1\n"
            "\t\tAssertCmd TA0 \"m1\"\n"
            "\t\tAssertCmd TA1 \"m2\"\n"
            "\t}",
            syms="TA0:bool\n\tTA1:bool",
        ),
        path="<s>",
    )
    ua_res = merge_asserts(tac.program)
    split_res = split_critical_edges(ua_res.program)
    assert split_res.was_noop is True
