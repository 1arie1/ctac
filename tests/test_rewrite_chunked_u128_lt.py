"""CHUNKED_U128_LT: lift the chunked-u128 lexicographic compare
ladder to a positional wide compare.

Fixture mirrors fluid lopu block 29_1 / kvault case2 block 43_1:
TB-named conditions, the SBF 0/1-int arm convention, chunk extracts
via bv Mod / Div by 2^64, and dominating range assumes.
"""

from __future__ import annotations

from ctac.ast.nodes import ApplyExpr, AssignExpCmd
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


# ---------------------------------------------------------------------------
# MulDivConstCancel
# ---------------------------------------------------------------------------


def _muldiv_tac(divisor_hex: str):
    """The lopu 67_1 shape: product behind narrow + havoc equate."""
    from ctac.parse import parse_string as _ps
    body = (
        "\t\tAssignHavocCmd X\n"
        "\t\tAssumeExpCmd Le(X 0xffff)\n"
        "\t\tAssignExpCmd I IntMul(0x16345785d8a0000(int) X)\n"
        "\t\tAssignExpCmd P Apply(safe_math_narrow_bv256:bif I)\n"
        "\t\tAssignHavocCmd E\n"
        "\t\tAssumeExpCmd Eq(P E)\n"
        f"\t\tAssignExpCmd R Apply(safe_math_narrow_bv256:bif IntMulDiv(0x2710(int) E {divisor_hex}))\n"
    )
    syms = "X:bv256\n\tI:int\n\tP:bv256\n\tE:bv256\n\tR:bv256"
    return _ps(_wrap("\t\tBlock-ignored", syms=syms).replace(
        "\tBlock e Succ [] {\n\t\tBlock-ignored\n\t}",
        f"\tBlock e Succ [] {{\n{body}\t}}",
    ), path="<s>")


def test_muldiv_const_cancel_exact():
    """muldiv(10^4, E, 10^17) with E == narrow(10^17 * X) -> 10^4 * X.
    (0x16345785d8a0000 = 10^17.)"""
    from ctac.rewrite.rules import MULDIV_CONST_CANCEL
    tac = _muldiv_tac("0x16345785d8a0000(int)")
    res = rewrite_program(
        tac.program, (MULDIV_CONST_CANCEL,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule.get("MulDivConstCancel") == 1
    rhs = _rhs(res.program, "R")
    inner = rhs.args[1]
    assert isinstance(inner, ApplyExpr) and inner.op == "IntMul"
    # q == 1: bare IntMul(10^4, X).
    assert str(inner.args[1]) == "SymbolRef(name='X')"


def test_muldiv_const_cancel_divisible():
    """Divisor 10^8 divides the 10^17 factor: q = 10^9 folds in."""
    from ctac.rewrite.rules import MULDIV_CONST_CANCEL
    tac = _muldiv_tac("0x5f5e100(int)")  # 10^8
    res = rewrite_program(
        tac.program, (MULDIV_CONST_CANCEL,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule.get("MulDivConstCancel") == 1


def test_muldiv_const_cancel_non_divisor_no_fire():
    """Divisor 3 does not divide 10^17: no fire (the floor matters)."""
    from ctac.rewrite.rules import MULDIV_CONST_CANCEL
    tac = _muldiv_tac("0x3(int)")
    res = rewrite_program(
        tac.program, (MULDIV_CONST_CANCEL,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule.get("MulDivConstCancel", 0) == 0


def test_muldiv_const_cancel_combined_factors():
    """The cascade shape: muldiv(10^4, E, 10^17) with E == narrow(
    10^13 * X) -- neither const alone is divisible, but 10^4 * 10^13
    = 10^17 cancels the divisor exactly: result is bare X."""
    from ctac.parse import parse_string as _ps
    from ctac.rewrite.rules import MULDIV_CONST_CANCEL
    body = (
        "\t\tAssignHavocCmd X\n"
        "\t\tAssumeExpCmd Le(X 0xffff)\n"
        "\t\tAssignExpCmd I IntMul(0x9184e72a000(int) X)\n"  # 10^13
        "\t\tAssignExpCmd P Apply(safe_math_narrow_bv256:bif I)\n"
        "\t\tAssignHavocCmd E\n"
        "\t\tAssumeExpCmd Eq(P E)\n"
        "\t\tAssignExpCmd R Apply(safe_math_narrow_bv256:bif "
        "IntMulDiv(0x2710(int) E 0x16345785d8a0000(int)))\n"  # 10^4, 10^17
    )
    syms = "X:bv256\n\tI:int\n\tP:bv256\n\tE:bv256\n\tR:bv256"
    tac = _ps(
        _wrap("\t\tplaceholder", syms=syms).replace(
            "\tBlock e Succ [] {\n\t\tplaceholder\n\t}",
            f"\tBlock e Succ [] {{\n{body}\t}}",
        ),
        path="<s>",
    )
    res = rewrite_program(
        tac.program, (MULDIV_CONST_CANCEL,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule.get("MulDivConstCancel") == 1
    rhs = _rhs(res.program, "R")
    # q == 1, single sym: narrow(X) directly.
    assert str(rhs.args[1]) == "SymbolRef(name='X')"
