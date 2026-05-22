"""Unit tests for ``SHIFT_LEFT_TO_INT_MUL`` and ``CHUNK_MERGE``."""

from __future__ import annotations

from ctac.ast.nodes import ApplyExpr, AssumeExpCmd, ConstExpr, SymbolRef
from ctac.parse import parse_string
from ctac.rewrite import rewrite_program
from ctac.rewrite.rules import CHUNK_MERGE, SHIFT_LEFT_TO_INT_MUL


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


def _assume_cond(prog):
    for b in prog.blocks:
        for cmd in b.commands:
            if isinstance(cmd, AssumeExpCmd):
                return cmd.condition
    return None


def test_shift_left_to_int_mul_fires_when_bound_known():
    """``ShiftLeft(X, 64)`` with X bounded ≤ 2^64-1 rewrites to
    ``IntMul(X, 2^64)``."""
    body = (
        "\t\tAssignHavocCmd X\n"
        "\t\tAssumeExpCmd Le(X 0xffffffffffffffff)\n"
        "\t\tAssumeExpCmd Eq(ShiftLeft(X 0x40) 0x0)\n"
        "\t\tAssertCmd false\n"
    )
    tac = parse_string(_wrap(body, syms="X:bv256"), path="<s>")
    res = rewrite_program(
        tac.program, (SHIFT_LEFT_TO_INT_MUL,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule.get("ShiftLeftToIntMul", 0) >= 1


def test_shift_left_to_int_mul_skips_when_overflow_possible():
    """Without a tight bound on X, X * 2^64 might overflow bv256 →
    the rule abstains."""
    body = (
        "\t\tAssignHavocCmd X\n"
        # No bound — bv256 sort default puts X in [0, 2^256-1].
        # Then X * 2^64 can exceed 2^256.
        "\t\tAssumeExpCmd Eq(ShiftLeft(X 0x40) 0x0)\n"
        "\t\tAssertCmd false\n"
    )
    tac = parse_string(_wrap(body, syms="X:bv256"), path="<s>")
    res = rewrite_program(
        tac.program, (SHIFT_LEFT_TO_INT_MUL,), symbol_sorts=tac.symbol_sorts
    )
    assert "ShiftLeftToIntMul" not in res.hits_by_rule


def test_chunk_merge_collapses_euclidean_recombination():
    """``narrow(IntAdd(IntMul(Div(T, K), K), Mod(T, K)))`` -> T."""
    body = (
        "\t\tAssignHavocCmd T\n"
        "\t\tAssignExpCmd Hi Div(T 0x10000000000000000)\n"
        "\t\tAssignExpCmd Lo Mod(T 0x10000000000000000)\n"
        "\t\tAssumeExpCmd Eq("
        "Apply(safe_math_narrow_bv256:bif "
        "IntAdd(IntMul(Hi 0x10000000000000000(int)) Lo)) T)\n"
        "\t\tAssertCmd false\n"
    )
    syms = (
        "T:bv256\n\tHi:bv256\n\tLo:bv256\n\t"
        "safe_math_narrow_bv256:bif"
    )
    tac = parse_string(_wrap(body, syms=syms), path="<s>")
    res = rewrite_program(
        tac.program, (CHUNK_MERGE,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule.get("ChunkMerge", 0) >= 1
    cond = _assume_cond(res.program)
    # The narrow(IntAdd(IntMul(Div, K), Mod)) collapsed to T.
    assert cond is not None
    assert isinstance(cond, ApplyExpr) and cond.op == "Eq"
    assert cond.args[0] == SymbolRef("T")


def test_chunk_merge_handles_symmetric_intadd_order():
    """``narrow(IntAdd(Mod(T, K), IntMul(Div(T, K), K)))`` -> T."""
    body = (
        "\t\tAssignHavocCmd T\n"
        "\t\tAssignExpCmd Hi Div(T 0x10000000000000000)\n"
        "\t\tAssignExpCmd Lo Mod(T 0x10000000000000000)\n"
        "\t\tAssumeExpCmd Eq("
        "Apply(safe_math_narrow_bv256:bif "
        "IntAdd(Lo IntMul(Hi 0x10000000000000000(int)))) T)\n"
        "\t\tAssertCmd false\n"
    )
    syms = (
        "T:bv256\n\tHi:bv256\n\tLo:bv256\n\t"
        "safe_math_narrow_bv256:bif"
    )
    tac = parse_string(_wrap(body, syms=syms), path="<s>")
    res = rewrite_program(
        tac.program, (CHUNK_MERGE,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule.get("ChunkMerge", 0) >= 1


def test_chunk_merge_skips_when_constants_dont_match():
    """``narrow(IntAdd(IntMul(Div(T, K1), K2), Mod(T, K3)))`` with
    differing K — no Euclidean identity, no fire."""
    body = (
        "\t\tAssignHavocCmd T\n"
        "\t\tAssignExpCmd Hi Div(T 0x10000000000000000)\n"
        "\t\tAssignExpCmd Lo Mod(T 0x10000000000000000)\n"
        "\t\tAssumeExpCmd Eq("
        "Apply(safe_math_narrow_bv256:bif "
        "IntAdd(IntMul(Hi 0x10000000000000001(int)) Lo)) T)\n"
        "\t\tAssertCmd false\n"
    )
    syms = (
        "T:bv256\n\tHi:bv256\n\tLo:bv256\n\t"
        "safe_math_narrow_bv256:bif"
    )
    tac = parse_string(_wrap(body, syms=syms), path="<s>")
    res = rewrite_program(
        tac.program, (CHUNK_MERGE,), symbol_sorts=tac.symbol_sorts
    )
    assert "ChunkMerge" not in res.hits_by_rule


# Silence unused-import warnings for symbols referenced only by tests above.
_ = (ConstExpr,)
