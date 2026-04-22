"""Tests for remove_true_asserts (standalone + wired through DCE)."""

from __future__ import annotations

from ctac.analysis import eliminate_dead_assignments, remove_true_asserts
from ctac.ast.nodes import AssertCmd
from ctac.parse import parse_string


def _wrap(body: str, *, syms: str = "R0:bv256") -> str:
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
\tBlock e Succ [] {{
{body}
\t}}
}}
Axioms {{
}}
Metas {{
  "0": []
}}
"""


def _asserts(program) -> list[AssertCmd]:
    return [c for b in program.blocks for c in b.commands if isinstance(c, AssertCmd)]


def test_standalone_removes_only_const_true():
    tac = parse_string(
        _wrap(
            "\t\tAssignHavocCmd R0\n"
            "\t\tAssertCmd true \"trivial\"\n"
            "\t\tAssertCmd Lt(R0 0x10) \"keep\"\n"
            "\t\tAssertCmd false \"boom\""
        ),
        path="<s>",
    )
    out, removed = remove_true_asserts(tac.program)
    assert len(removed) == 1
    assert removed[0].block_id == "e"
    # Surviving asserts: the Lt(...) one and the false one.
    surviving = _asserts(out)
    assert len(surviving) == 2
    messages = [a.message for a in surviving]
    assert messages == ["keep", "boom"]


def test_standalone_no_asserts_is_noop():
    tac = parse_string(
        _wrap("\t\tAssignHavocCmd R0"),
        path="<s>",
    )
    out, removed = remove_true_asserts(tac.program)
    assert removed == ()
    # Program unchanged structurally (block + command count preserved).
    assert [b.id for b in out.blocks] == [b.id for b in tac.program.blocks]
    assert sum(len(b.commands) for b in out.blocks) == sum(
        len(b.commands) for b in tac.program.blocks
    )


def test_dce_opt_in_drops_true_asserts_and_reports():
    tac = parse_string(
        _wrap(
            "\t\tAssignHavocCmd R0\n"
            "\t\tAssertCmd true \"trivial\"\n"
            "\t\tAssertCmd Lt(R0 0x10) \"keep\""
        ),
        path="<s>",
    )
    dce = eliminate_dead_assignments(tac.program, drop_true_asserts=True)
    assert len(dce.removed_asserts) == 1
    # The surviving assert is the compound one.
    surviving = _asserts(dce.program)
    assert len(surviving) == 1
    assert surviving[0].message == "keep"


def test_dce_default_leaves_true_asserts_alone():
    tac = parse_string(
        _wrap(
            "\t\tAssignHavocCmd R0\n"
            "\t\tAssertCmd true \"trivial\"\n"
            "\t\tAssertCmd Lt(R0 0x10) \"keep\""
        ),
        path="<s>",
    )
    dce = eliminate_dead_assignments(tac.program)
    assert dce.removed_asserts == ()
    # Both asserts survive.
    assert len(_asserts(dce.program)) == 2
