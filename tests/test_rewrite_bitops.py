"""Unit tests for bit-op normalization rules (N2 low-mask, N3 high-mask, N4 shr-const)."""

from __future__ import annotations

from ctac.ast.nodes import ApplyExpr, AssignExpCmd, ConstExpr, SymbolRef
from ctac.parse import parse_string
from ctac.rewrite import rewrite_program
from ctac.rewrite.rules import N2_LOW_MASK, N3_HIGH_MASK, N4_SHR_CONST


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


def _rhs(res_program, lhs: str):
    for b in res_program.blocks:
        for cmd in b.commands:
            if isinstance(cmd, AssignExpCmd) and cmd.lhs == lhs:
                return cmd.rhs
    raise AssertionError(f"no assignment for {lhs}")


def test_n2_low_mask_byte():
    """BWAnd(X, 0xff) -> Mod(X, 0x100)."""
    tac = parse_string(_wrap("\t\tAssignExpCmd R1 BWAnd(R0 0xff)"), path="<s>")
    res = rewrite_program(tac.program, (N2_LOW_MASK,))
    assert res.hits_by_rule == {"N2": 1}
    rhs = _rhs(res.program, "R1")
    assert isinstance(rhs, ApplyExpr) and rhs.op == "Mod"
    assert rhs.args[0] == SymbolRef("R0")
    assert isinstance(rhs.args[1], ConstExpr) and int(rhs.args[1].value, 0) == 0x100


def test_n2_low_mask_64bit():
    """BWAnd(X, 0xffffffffffffffff) -> Mod(X, 0x10000000000000000)."""
    tac = parse_string(
        _wrap("\t\tAssignExpCmd R1 BWAnd(R0 0xffffffffffffffff)"), path="<s>"
    )
    res = rewrite_program(tac.program, (N2_LOW_MASK,))
    assert res.hits_by_rule == {"N2": 1}
    rhs = _rhs(res.program, "R1")
    assert isinstance(rhs, ApplyExpr) and rhs.op == "Mod"
    assert int(rhs.args[1].value, 0) == (1 << 64)


def test_n2_does_not_fire_on_shifted_mask():
    """Shifted-contiguous masks belong to N1, not N2."""
    tac = parse_string(
        _wrap("\t\tAssignExpCmd R1 BWAnd(R0 0x3fffffffc000)"), path="<s>"
    )
    res = rewrite_program(tac.program, (N2_LOW_MASK,))
    assert res.hits_by_rule == {}


def test_n2_does_not_fire_on_non_mask():
    """Arbitrary constants that aren't 2^w - 1 don't match."""
    tac = parse_string(_wrap("\t\tAssignExpCmd R1 BWAnd(R0 0x5)"), path="<s>")
    res = rewrite_program(tac.program, (N2_LOW_MASK,))
    assert res.hits_by_rule == {}


def test_n3_high_mask_clears_low_k():
    """BWAnd(X, 2^256 - 2^k) -> Mul(Div(X, 2^k), 2^k)."""
    k = 8
    mask = (1 << 256) - (1 << k)
    tac = parse_string(
        _wrap(f"\t\tAssignExpCmd R1 BWAnd(R0 {hex(mask)})"), path="<s>"
    )
    res = rewrite_program(tac.program, (N3_HIGH_MASK,))
    assert res.hits_by_rule == {"N3": 1}
    rhs = _rhs(res.program, "R1")
    assert isinstance(rhs, ApplyExpr) and rhs.op == "Mul"
    div = rhs.args[0]
    assert isinstance(div, ApplyExpr) and div.op == "Div"
    assert div.args[0] == SymbolRef("R0")
    assert int(div.args[1].value, 0) == (1 << k)
    assert int(rhs.args[1].value, 0) == (1 << k)


def test_n3_does_not_fire_on_full_mask():
    """``2^256 - 1`` (all bits set) is caught by N2, not N3 (k would be 0)."""
    full = (1 << 256) - 1
    tac = parse_string(
        _wrap(f"\t\tAssignExpCmd R1 BWAnd(R0 {hex(full)})"), path="<s>"
    )
    res = rewrite_program(tac.program, (N3_HIGH_MASK,))
    assert res.hits_by_rule == {}


def test_n4_shr_const():
    """ShiftRightLogical(X, 4) -> Div(X, 0x10)."""
    tac = parse_string(
        _wrap("\t\tAssignExpCmd R1 ShiftRightLogical(R0 0x4)"), path="<s>"
    )
    res = rewrite_program(tac.program, (N4_SHR_CONST,))
    assert res.hits_by_rule == {"N4": 1}
    rhs = _rhs(res.program, "R1")
    assert isinstance(rhs, ApplyExpr) and rhs.op == "Div"
    assert rhs.args[0] == SymbolRef("R0")
    assert int(rhs.args[1].value, 0) == 16


def test_n4_shr_6_bits():
    """ShiftRightLogical(X, 0x40) -> Div(X, 2^64) — exact 64-bit shift from ceiling chain."""
    tac = parse_string(
        _wrap("\t\tAssignExpCmd R1 ShiftRightLogical(R0 0x40)"), path="<s>"
    )
    res = rewrite_program(tac.program, (N4_SHR_CONST,))
    assert res.hits_by_rule == {"N4": 1}
    rhs = _rhs(res.program, "R1")
    assert isinstance(rhs, ApplyExpr) and rhs.op == "Div"
    assert int(rhs.args[1].value, 0) == (1 << 64)


def test_n4_does_not_fire_on_variable_shift():
    """Non-const shift amounts don't match."""
    tac = parse_string(
        _wrap(
            "\t\tAssignExpCmd R1 ShiftRightLogical(R0 R2)",
            syms="R0:bv256\n\tR1:bv256\n\tR2:bv256",
        ),
        path="<s>",
    )
    res = rewrite_program(tac.program, (N4_SHR_CONST,))
    assert res.hits_by_rule == {}


def test_n4_does_not_fire_on_zero_shift():
    """Shift by 0 is a no-op; don't rewrite to Div(X, 1)."""
    tac = parse_string(
        _wrap("\t\tAssignExpCmd R1 ShiftRightLogical(R0 0x0)"), path="<s>"
    )
    res = rewrite_program(tac.program, (N4_SHR_CONST,))
    assert res.hits_by_rule == {}
