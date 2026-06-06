"""CHUNKED_U128_LT: lift the chunked-u128 lexicographic compare
ladder to a positional wide compare.

Fixture mirrors fluid lopu block 29_1 / kvault case2 block 43_1:
TB-named conditions, the SBF 0/1-int arm convention, chunk extracts
via bv Mod / Div by 2^64, and dominating range assumes.
"""

from __future__ import annotations

from ctac.ast.nodes import ApplyExpr, AssignExpCmd, ConstExpr
from ctac.parse import parse_string
from ctac.rewrite import rewrite_program
from ctac.rewrite.rules import CHUNKED_U128_LT


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


def _rhs(prog, lhs):
    for b in prog.blocks:
        for cmd in b.commands:
            if isinstance(cmd, AssignExpCmd) and cmd.lhs == lhs:
                return cmd.rhs
    raise AssertionError(f"no def of {lhs!r}")


_SYMS = (
    "W:bv256\n\tHp:bv256\n\tLp:bv256\n\tH:bv256\n\tL:bv256\n"
    "\tTBe:bool\n\tTBl:bool\n\tTBh:bool\n\tB:bv256"
)


def test_ladder_lifts_and_chunk_side_collapses_to_wide_source():
    """(H, L) = chunks of W; the ladder vs (Hp, Lp) lifts to
    Lt(W, Hp*2^64 + Lp). 0/1-int convention preserved."""
    body = (
        "\t\tAssignHavocCmd W\n"
        "\t\tAssumeExpCmd Le(W 0xffffffffffffffffffffffffffffffff)\n"
        "\t\tAssignHavocCmd Hp\n"
        "\t\tAssumeExpCmd Le(Hp 0xffffffffffffffff)\n"
        "\t\tAssignHavocCmd Lp\n"
        "\t\tAssumeExpCmd Le(Lp 0xffffffffffffffff)\n"
        "\t\tAssignExpCmd L Mod(W 0x10000000000000000)\n"
        "\t\tAssignExpCmd H Div(W 0x10000000000000000)\n"
        "\t\tAssignExpCmd TBe Eq(H Hp)\n"
        "\t\tAssignExpCmd TBl Lt(L Lp)\n"
        "\t\tAssignExpCmd TBh Lt(H Hp)\n"
        "\t\tAssignExpCmd B Ite(TBe Ite(TBl 0x1 0x0) Ite(TBh 0x1 0x0))\n"
    )
    tac = parse_string(_wrap(body, syms=_SYMS), path="<s>")
    res = rewrite_program(
        tac.program, (CHUNKED_U128_LT,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule.get("ChunkedU128Lt", 0) == 1
    rhs = _rhs(res.program, "B")
    # 0/1 convention preserved: Ite(Lt(...), 1, 0).
    assert isinstance(rhs, ApplyExpr) and rhs.op == "Ite"
    lt = rhs.args[0]
    assert isinstance(lt, ApplyExpr) and lt.op == "Lt"
    # Left side collapsed to the wide source W.
    left, right = lt.args
    assert str(left).find("W") != -1 and "Mod" not in str(left)
    # Right side reassembled: IntAdd(IntMul(Hp, 2^64), Lp).
    assert isinstance(right, ApplyExpr) and right.op == "IntAdd"


def test_no_fire_without_lo_range_fact():
    """Lp has no dominating bound: lexicographic != positional in
    general, the gate must hold the rewrite back."""
    body = (
        "\t\tAssignHavocCmd W\n"
        "\t\tAssumeExpCmd Le(W 0xffffffffffffffffffffffffffffffff)\n"
        "\t\tAssignHavocCmd Hp\n"
        "\t\tAssumeExpCmd Le(Hp 0xffffffffffffffff)\n"
        "\t\tAssignHavocCmd Lp\n"
        "\t\tAssignExpCmd L Mod(W 0x10000000000000000)\n"
        "\t\tAssignExpCmd H Div(W 0x10000000000000000)\n"
        "\t\tAssignExpCmd TBe Eq(H Hp)\n"
        "\t\tAssignExpCmd TBl Lt(L Lp)\n"
        "\t\tAssignExpCmd TBh Lt(H Hp)\n"
        "\t\tAssignExpCmd B Ite(TBe Ite(TBl 0x1 0x0) Ite(TBh 0x1 0x0))\n"
    )
    tac = parse_string(_wrap(body, syms=_SYMS), path="<s>")
    res = rewrite_program(
        tac.program, (CHUNKED_U128_LT,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule.get("ChunkedU128Lt", 0) == 0


def test_eq_orientation_flipped_still_fires():
    """Eq(Hp, H) with else-arm Lt(H, Hp): same hi pair, flipped Eq."""
    body = (
        "\t\tAssignHavocCmd W\n"
        "\t\tAssumeExpCmd Le(W 0xffffffffffffffffffffffffffffffff)\n"
        "\t\tAssignHavocCmd Hp\n"
        "\t\tAssumeExpCmd Le(Hp 0xffffffffffffffff)\n"
        "\t\tAssignHavocCmd Lp\n"
        "\t\tAssumeExpCmd Le(Lp 0xffffffffffffffff)\n"
        "\t\tAssignExpCmd L Mod(W 0x10000000000000000)\n"
        "\t\tAssignExpCmd H Div(W 0x10000000000000000)\n"
        "\t\tAssignExpCmd TBe Eq(Hp H)\n"
        "\t\tAssignExpCmd TBl Lt(L Lp)\n"
        "\t\tAssignExpCmd TBh Lt(H Hp)\n"
        "\t\tAssignExpCmd B Ite(TBe Ite(TBl 0x1 0x0) Ite(TBh 0x1 0x0))\n"
    )
    tac = parse_string(_wrap(body, syms=_SYMS), path="<s>")
    res = rewrite_program(
        tac.program, (CHUNKED_U128_LT,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule.get("ChunkedU128Lt", 0) == 1


def test_unrelated_pair_in_else_no_fire():
    """Else-arm compares a different pair than the Eq tests: not a
    lexicographic ladder."""
    body = (
        "\t\tAssignHavocCmd W\n"
        "\t\tAssumeExpCmd Le(W 0xffffffffffffffffffffffffffffffff)\n"
        "\t\tAssignHavocCmd Hp\n"
        "\t\tAssumeExpCmd Le(Hp 0xffffffffffffffff)\n"
        "\t\tAssignHavocCmd Lp\n"
        "\t\tAssumeExpCmd Le(Lp 0xffffffffffffffff)\n"
        "\t\tAssignExpCmd L Mod(W 0x10000000000000000)\n"
        "\t\tAssignExpCmd H Div(W 0x10000000000000000)\n"
        "\t\tAssignExpCmd TBe Eq(H Hp)\n"
        "\t\tAssignExpCmd TBl Lt(L Lp)\n"
        "\t\tAssignExpCmd TBh Lt(L Hp)\n"
        "\t\tAssignExpCmd B Ite(TBe Ite(TBl 0x1 0x0) Ite(TBh 0x1 0x0))\n"
    )
    tac = parse_string(_wrap(body, syms=_SYMS), path="<s>")
    res = rewrite_program(
        tac.program, (CHUNKED_U128_LT,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule.get("ChunkedU128Lt", 0) == 0
