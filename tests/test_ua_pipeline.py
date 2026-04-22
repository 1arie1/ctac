"""Tests for ctac.ua.uniquify_asserts (pre-passes + strategy, one entry point)."""

from __future__ import annotations

import pytest

from ctac.ast.nodes import AssertCmd
from ctac.parse import parse_string
from ctac.ua import uniquify_asserts
from ctac.ua.merge import ERROR_BLOCK_ID


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
{body}
}}
Axioms {{
}}
Metas {{
  "0": []
}}
"""


def _count_asserts(program) -> int:
    return sum(
        1 for b in program.blocks for c in b.commands if isinstance(c, AssertCmd)
    )


def test_pipeline_strips_true_asserts_purifies_and_merges():
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd R0\n"
            "\t\tAssertCmd true \"trivial\"\n"
            "\t\tAssertCmd Lt(R0 0x10) \"real1\"\n"
            "\t\tAssertCmd Gt(R0 0x0) \"real2\"\n"
            "\t}"
        ),
        path="<s>",
    )
    res = uniquify_asserts(tac.program)
    assert res.removed_true_asserts == 1
    # The two compound asserts were purified into TA0 / TA1, then merged.
    assert res.asserts_merged == 2
    assert res.was_noop is False
    assert res.error_block_id == ERROR_BLOCK_ID
    # Output has exactly one AssertCmd (in the error block).
    assert _count_asserts(res.program) == 1
    # PURIFY_ASSERT introduced two TA<N>:bool symbols.
    names = [n for n, _ in res.extra_symbols]
    assert set(names) == {"TA0", "TA1"}


def test_pipeline_noop_on_single_compound_assert_still_purifies():
    """Single assert: merge is a no-op, but purification still runs."""
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd R0\n"
            "\t\tAssertCmd Lt(R0 0x10) \"only\"\n"
            "\t}"
        ),
        path="<s>",
    )
    res = uniquify_asserts(tac.program)
    assert res.was_noop is True
    assert res.asserts_merged == 0
    # PURIFY_ASSERT still introduced a fresh TA<N>.
    names = [n for n, _ in res.extra_symbols]
    assert names == ["TA0"]


def test_pipeline_unknown_strategy_raises():
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd R0\n"
            "\t}"
        ),
        path="<s>",
    )
    with pytest.raises(ValueError, match="unknown uniquify-asserts strategy"):
        uniquify_asserts(tac.program, strategy="split")
