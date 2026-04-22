"""Unit tests for PURIFY_ASSUME (naming non-trivial AssumeExpCmd conditions)."""

from __future__ import annotations

from ctac.ast.nodes import AssignExpCmd, AssumeExpCmd, SymbolRef
from ctac.parse import parse_string
from ctac.rewrite import rewrite_program
from ctac.rewrite.rules import PURIFY_ASSUME


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


def _assume(program) -> AssumeExpCmd:
    for b in program.blocks:
        for cmd in b.commands:
            if isinstance(cmd, AssumeExpCmd):
                return cmd
    raise AssertionError("no AssumeExpCmd in program")


def test_compound_condition_is_named():
    tac = parse_string(
        _wrap(
            "\t\tAssignHavocCmd R0\n"
            "\t\tAssumeExpCmd Lt(R0 0x10)"
        ),
        path="<s>",
    )
    res = rewrite_program(tac.program, (PURIFY_ASSUME,))
    assert res.hits_by_rule == {"PURIFY_ASSUME": 1}
    assert res.extra_symbols == (("TA0", "bool"),)
    a = _assume(res.program)
    assert a.condition == SymbolRef("TA0")
    block = res.program.blocks[0]
    ta0_idx = next(
        i for i, c in enumerate(block.commands)
        if isinstance(c, AssignExpCmd) and c.lhs == "TA0"
    )
    assume_idx = next(
        i for i, c in enumerate(block.commands) if isinstance(c, AssumeExpCmd)
    )
    assert ta0_idx < assume_idx


def test_symbolref_condition_is_untouched():
    tac = parse_string(
        _wrap(
            "\t\tAssignHavocCmd B0\n"
            "\t\tAssumeExpCmd B0",
            syms="B0:bool",
        ),
        path="<s>",
    )
    res = rewrite_program(tac.program, (PURIFY_ASSUME,))
    assert res.hits_by_rule == {}
