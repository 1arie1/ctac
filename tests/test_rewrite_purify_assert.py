"""Unit tests for PURIFY_ASSERT (naming non-trivial AssertCmd predicates)."""

from __future__ import annotations

from ctac.ast.nodes import AssertCmd, AssignExpCmd, SymbolRef
from ctac.parse import parse_string
from ctac.rewrite import rewrite_program
from ctac.rewrite.rules import PURIFY_ASSERT


def _wrap(body: str, *, syms: str = "R0:bv256\n\tR1:bv256") -> str:
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


def _assert_cmd(program) -> AssertCmd:
    for b in program.blocks:
        for cmd in b.commands:
            if isinstance(cmd, AssertCmd):
                return cmd
    raise AssertionError("no AssertCmd in program")


def test_compound_predicate_is_named():
    tac = parse_string(
        _wrap(
            "\t\tAssignHavocCmd R0\n"
            "\t\tAssertCmd Lt(R0 0x10) \"msg\""
        ),
        path="<s>",
    )
    res = rewrite_program(tac.program, (PURIFY_ASSERT,))
    assert res.hits_by_rule == {"PURIFY_ASSERT": 1}
    assert res.extra_symbols == (("TA0", "bool"),)
    # The AssertCmd now references TA0; TA0's defining assignment is inserted
    # just before the assert.
    a = _assert_cmd(res.program)
    assert a.predicate == SymbolRef("TA0")
    assert a.message == "msg"
    block = res.program.blocks[0]
    ta0_idx = next(
        i for i, c in enumerate(block.commands)
        if isinstance(c, AssignExpCmd) and c.lhs == "TA0"
    )
    assert_idx = next(
        i for i, c in enumerate(block.commands) if isinstance(c, AssertCmd)
    )
    assert ta0_idx < assert_idx


def test_symbolref_predicate_is_untouched():
    tac = parse_string(
        _wrap(
            "\t\tAssignHavocCmd B0\n"
            "\t\tAssertCmd B0",
            syms="B0:bool",
        ),
        path="<s>",
    )
    res = rewrite_program(tac.program, (PURIFY_ASSERT,))
    assert res.hits_by_rule == {}


def test_constexpr_predicate_is_untouched():
    """`assert true` / `assert false` are literals; not PURIFY_ASSERT's problem."""
    tac = parse_string(
        _wrap("\t\tAssertCmd false \"boom\""),
        path="<s>",
    )
    res = rewrite_program(tac.program, (PURIFY_ASSERT,))
    assert res.hits_by_rule == {}


def test_multiple_asserts_each_get_fresh_ta():
    tac = parse_string(
        _wrap(
            "\t\tAssignHavocCmd R0\n"
            "\t\tAssertCmd Lt(R0 0x10) \"a\"\n"
            "\t\tAssertCmd Gt(R0 0x0) \"b\""
        ),
        path="<s>",
    )
    res = rewrite_program(tac.program, (PURIFY_ASSERT,))
    assert res.hits_by_rule == {"PURIFY_ASSERT": 2}
    assert {n for n, _ in res.extra_symbols} == {"TA0", "TA1"}
