"""Tests for ``SAR_TO_SHR_NONNEG``."""

from __future__ import annotations

from ctac.ast.nodes import ApplyExpr
from ctac.parse import parse_string
from ctac.rewrite.framework import rewrite_program
from ctac.rewrite.rules import SAR_TO_SHR_NONNEG


def _wrap(body: str, *, syms: str) -> str:
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


def test_fires_when_operand_proves_top_bit_zero():
    """``Mod(R, 2^64)`` pins the operand to ``[0, 2^64-1]``, well below
    ``2^255``; the rule rewrites SAR to LSHR."""
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd R\n"
            "\t\tAssignExpCmd Y Mod(R 0x10000000000000000)\n"
            "\t\tAssignExpCmd Z ShiftRightArithmetical(Y 0x3f)\n"
            "\t\tAssertCmd Le(Z 0x100)\n"
            "\t}\n",
            syms="R:bv256\n\tY:bv256\n\tZ:bv256",
        ),
        path="<s>",
    )
    res = rewrite_program(
        tac.program, (SAR_TO_SHR_NONNEG,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule.get("SarToShrNonneg") == 1
    z_cmd = next(
        c for b in res.program.blocks for c in b.commands
        if getattr(c, "lhs", None) == "Z"
    )
    rhs = z_cmd.rhs
    assert isinstance(rhs, ApplyExpr) and rhs.op == "ShiftRightLogical"


def test_does_not_fire_when_top_bit_unknown():
    """Without a range-pinning def, the rule declines — operand could
    have its top bit set."""
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd R\n"
            "\t\tAssignExpCmd Z ShiftRightArithmetical(R 0x3f)\n"
            "\t\tAssertCmd Le(Z 0x100)\n"
            "\t}\n",
            syms="R:bv256\n\tZ:bv256",
        ),
        path="<s>",
    )
    res = rewrite_program(
        tac.program, (SAR_TO_SHR_NONNEG,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule.get("SarToShrNonneg", 0) == 0


def test_fires_when_range_exactly_at_threshold():
    """Boundary: operand in [0, 2^255 - 1] is the largest safe range
    (top bit zero). The rule still fires."""
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd R\n"
            # 2^255 - 1 = 0x7fff...ffff (64 f's after 7).
            "\t\tAssignExpCmd Y Mod(R 0x8000000000000000000000000000000000000000000000000000000000000000)\n"
            "\t\tAssignExpCmd Z ShiftRightArithmetical(Y 0x10)\n"
            "\t\tAssertCmd Le(Z 0x100)\n"
            "\t}\n",
            syms="R:bv256\n\tY:bv256\n\tZ:bv256",
        ),
        path="<s>",
    )
    res = rewrite_program(
        tac.program, (SAR_TO_SHR_NONNEG,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule.get("SarToShrNonneg") == 1


def test_does_not_fire_when_range_covers_top_bit():
    """``Mod(R, 2^256)`` is no constraint at all; rule declines."""
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd R\n"
            # 2^256 — the full bv256 range, top bit can be set.
            "\t\tAssignExpCmd Y Mod(R 0x10000000000000000000000000000000000000000000000000000000000000000)\n"
            "\t\tAssignExpCmd Z ShiftRightArithmetical(Y 0x3f)\n"
            "\t\tAssertCmd Le(Z 0x100)\n"
            "\t}\n",
            syms="R:bv256\n\tY:bv256\n\tZ:bv256",
        ),
        path="<s>",
    )
    res = rewrite_program(
        tac.program, (SAR_TO_SHR_NONNEG,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule.get("SarToShrNonneg", 0) == 0
