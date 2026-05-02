"""Tests for CHUNKED_MUL_BY_2N + MUL_DIV_TO_MULDIV recognizers."""

from __future__ import annotations

from ctac.ast.nodes import ApplyExpr, AssignExpCmd, ConstExpr, SymbolRef
from ctac.parse import parse_string
from ctac.rewrite import rewrite_program
from ctac.rewrite.rules import CHUNKED_MUL_BY_2N, MUL_DIV_TO_MULDIV


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


def _rhs(prog, lhs):
    for b in prog.blocks:
        for cmd in b.commands:
            if isinstance(cmd, AssignExpCmd) and cmd.lhs == lhs:
                return cmd.rhs
    raise AssertionError(f"no def for {lhs}")


# ---------- CHUNKED_MUL_BY_2N ----------

_CHUNK_SYMS = (
    "R641:bv256\n"
    "\tR642:bv256\n"
    "\tR643:bv256\n"
    "\tI645:int\n"
    "\tIout:int"
)


def test_chunked_mul_recognized():
    """The canonical Q50.14 shape from request_elevation_group:

      R642 = (R641 << 14) mod 2^64
      R643 = R641 mod 2^64
      I645 = 2^64 * (R643 / 2^50)
      Iout = narrow(I645) +int R642     -> IntMul(R641, 2^14)
    """
    body = (
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd R641\n"
        "\t\tAssignExpCmd R642 Mod(ShiftLeft(R641 0xe) 0x10000000000000000)\n"
        "\t\tAssignExpCmd R643 Mod(R641 0x10000000000000000)\n"
        "\t\tAssignExpCmd I645 IntMul(0x10000000000000000(int) Div(R643 0x4000000000000))\n"
        "\t\tAssignExpCmd Iout IntAdd(Apply(safe_math_narrow_bv256:bif I645) R642)\n"
        "\t}"
    )
    tac = parse_string(_wrap(body, syms=_CHUNK_SYMS), path="<s>")
    res = rewrite_program(
        tac.program, (CHUNKED_MUL_BY_2N,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule == {"ChunkedMul": 1}
    rhs = _rhs(res.program, "Iout")
    # Iout's RHS: IntMul(Mod(R641, 2^M), 2^N) — the `Mod` preserves
    # soundness when R641 may be a bv256 with bits above M.
    assert isinstance(rhs, ApplyExpr) and rhs.op == "IntMul"
    inner = rhs.args[0]
    assert isinstance(inner, ApplyExpr) and inner.op == "Mod"
    assert inner.args[0] == SymbolRef("R641")
    assert isinstance(rhs.args[1], ConstExpr)


def test_chunked_mul_arg_order_swapped():
    """Same shape but IntAdd args in the other order — still matches."""
    body = (
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd R641\n"
        "\t\tAssignExpCmd R642 Mod(ShiftLeft(R641 0xe) 0x10000000000000000)\n"
        "\t\tAssignExpCmd R643 Mod(R641 0x10000000000000000)\n"
        "\t\tAssignExpCmd I645 IntMul(0x10000000000000000(int) Div(R643 0x4000000000000))\n"
        "\t\tAssignExpCmd Iout IntAdd(R642 Apply(safe_math_narrow_bv256:bif I645))\n"
        "\t}"
    )
    tac = parse_string(_wrap(body, syms=_CHUNK_SYMS), path="<s>")
    res = rewrite_program(
        tac.program, (CHUNKED_MUL_BY_2N,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule == {"ChunkedMul": 1}


def test_chunked_mul_bails_on_K_plus_N_mismatch():
    """K + N != M (the constants don't compose to the register width).
    Pattern shape correct but constants don't fit — must bail."""
    body = (
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd R641\n"
        # ShiftLeft by 14, but Div by 2^49 (K=49) — sum 14+49=63, not 64
        "\t\tAssignExpCmd R642 Mod(ShiftLeft(R641 0xe) 0x10000000000000000)\n"
        "\t\tAssignExpCmd R643 Mod(R641 0x10000000000000000)\n"
        "\t\tAssignExpCmd I645 IntMul(0x10000000000000000(int) Div(R643 0x2000000000000))\n"
        "\t\tAssignExpCmd Iout IntAdd(Apply(safe_math_narrow_bv256:bif I645) R642)\n"
        "\t}"
    )
    tac = parse_string(_wrap(body, syms=_CHUNK_SYMS), path="<s>")
    res = rewrite_program(
        tac.program, (CHUNKED_MUL_BY_2N,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule == {}


def test_chunked_mul_bails_on_different_R():
    """Two arms reference different R variables — must bail."""
    body = (
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd R641\n"
        "\t\tAssignHavocCmd R641b\n"
        "\t\tAssignExpCmd R642 Mod(ShiftLeft(R641 0xe) 0x10000000000000000)\n"
        "\t\tAssignExpCmd R643 Mod(R641b 0x10000000000000000)\n"        # different R!
        "\t\tAssignExpCmd I645 IntMul(0x10000000000000000(int) Div(R643 0x4000000000000))\n"
        "\t\tAssignExpCmd Iout IntAdd(Apply(safe_math_narrow_bv256:bif I645) R642)\n"
        "\t}"
    )
    tac = parse_string(
        _wrap(body, syms=_CHUNK_SYMS + "\n\tR641b:bv256"), path="<s>"
    )
    res = rewrite_program(
        tac.program, (CHUNKED_MUL_BY_2N,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule == {}


def test_chunked_mul_bails_on_non_powers_of_two():
    """2^M is not a power of 2 — must bail."""
    body = (
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd R641\n"
        "\t\tAssignExpCmd R642 Mod(ShiftLeft(R641 0xe) 0x100)\n"        # 2^8 OK
        "\t\tAssignExpCmd R643 Mod(R641 0x100)\n"                        # 2^8 OK
        "\t\tAssignExpCmd I645 IntMul(0x100(int) Div(R643 0x100))\n"   # K=8 but K+N != 8
        "\t\tAssignExpCmd Iout IntAdd(Apply(safe_math_narrow_bv256:bif I645) R642)\n"
        "\t}"
    )
    tac = parse_string(_wrap(body, syms=_CHUNK_SYMS), path="<s>")
    res = rewrite_program(
        tac.program, (CHUNKED_MUL_BY_2N,), symbol_sorts=tac.symbol_sorts
    )
    # K=8, N=14, M=8. K+N=22 != M=8. Bail.
    assert res.hits_by_rule == {}


# ---------- MUL_DIV_TO_MULDIV ----------


def test_muldiv_basic():
    """IntDiv(IntMul(a, b), c) -> IntMulDiv(a, b, c) when c is
    provably positive (assume gives the bound)."""
    body = (
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd a\n"
        "\t\tAssignHavocCmd b\n"
        "\t\tAssignHavocCmd c\n"
        ""
        "\t\tAssignExpCmd I IntDiv(IntMul(a b) c)\n"
        "\t}"
    )
    tac = parse_string(
        _wrap(body, syms="a:int\n\tb:int\n\tc:int\n\tI:int"), path="<s>"
    )
    res = rewrite_program(
        tac.program, (MUL_DIV_TO_MULDIV,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule == {"MulDiv": 1}
    rhs = _rhs(res.program, "I")
    assert isinstance(rhs, ApplyExpr) and rhs.op == "IntMulDiv"
    assert rhs.args == (SymbolRef("a"), SymbolRef("b"), SymbolRef("c"))


def test_muldiv_through_lookthrough():
    """IntDiv(<sym>, c) where <sym>'s static def is IntMul(a, b) -
    rule looks through and fires."""
    body = (
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd a\n"
        "\t\tAssignHavocCmd b\n"
        "\t\tAssignHavocCmd c\n"
        ""
        "\t\tAssignExpCmd Mab IntMul(a b)\n"
        "\t\tAssignExpCmd I IntDiv(Mab c)\n"
        "\t}"
    )
    tac = parse_string(
        _wrap(body, syms="a:int\n\tb:int\n\tc:int\n\tMab:int\n\tI:int"), path="<s>"
    )
    res = rewrite_program(
        tac.program, (MUL_DIV_TO_MULDIV,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule == {"MulDiv": 1}
    rhs = _rhs(res.program, "I")
    assert isinstance(rhs, ApplyExpr) and rhs.op == "IntMulDiv"
    assert rhs.args == (SymbolRef("a"), SymbolRef("b"), SymbolRef("c"))


def test_muldiv_bails_on_non_intmul_numerator():
    """Numerator is IntAdd, not IntMul — rule bails."""
    body = (
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd a\n"
        "\t\tAssignHavocCmd b\n"
        "\t\tAssignHavocCmd c\n"
        "\t\tAssignExpCmd I IntDiv(IntAdd(a b) c)\n"
        "\t}"
    )
    tac = parse_string(
        _wrap(body, syms="a:int\n\tb:int\n\tc:int\n\tI:int"), path="<s>"
    )
    res = rewrite_program(
        tac.program, (MUL_DIV_TO_MULDIV,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule == {}


# ---------- Composition: chunk + muldiv together ----------


def test_chunked_mul_then_muldiv_composes():
    """End-to-end: the full Solana QFP chain (chunk arithmetic +
    division) collapses to a single IntMulDiv. The narrow between
    IntDiv and IntMul peels through (narrow is a no-op type
    assertion, sea_vc.py:619-620). Divisor R633 needs a positivity
    bound for MUL_DIV to fire — added as an assume here."""
    body = (
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd R641\n"
        "\t\tAssignHavocCmd R633\n"
        "\t\tAssignExpCmd R642 Mod(ShiftLeft(R641 0xe) 0x10000000000000000)\n"
        "\t\tAssignExpCmd R643 Mod(R641 0x10000000000000000)\n"
        "\t\tAssignExpCmd I645 IntMul(0x10000000000000000(int) Div(R643 0x4000000000000))\n"
        "\t\tAssignExpCmd I650 IntDiv(Apply(safe_math_narrow_bv256:bif IntAdd(Apply(safe_math_narrow_bv256:bif I645) R642)) R633)\n"
        "\t}"
    )
    tac = parse_string(
        _wrap(
            body,
            syms="R641:bv256\n\tR642:bv256\n\tR643:bv256\n\tI645:int\n\tR633:int\n\tI650:int",
        ),
        path="<s>",
    )
    res = rewrite_program(
        tac.program,
        (CHUNKED_MUL_BY_2N, MUL_DIV_TO_MULDIV),
        symbol_sorts=tac.symbol_sorts,
    )
    assert res.hits_by_rule.get("ChunkedMul", 0) == 1
    assert res.hits_by_rule.get("MulDiv", 0) == 1
    rhs = _rhs(res.program, "I650")
    # I650 = IntMulDiv(Mod(R641, 2^M), 2^N, R633).
    assert isinstance(rhs, ApplyExpr) and rhs.op == "IntMulDiv"
    inner = rhs.args[0]
    assert isinstance(inner, ApplyExpr) and inner.op == "Mod"
    assert inner.args[0] == SymbolRef("R641")
    assert isinstance(rhs.args[1], ConstExpr)
    assert rhs.args[2] == SymbolRef("R633")


def test_muldiv_fires_without_positivity_assume():
    """The IntMulDiv axiom is now total (covers all c via the c<=0
    branch tying to z3's div). The rewrite is sound for any c, so
    no divisor-range gate is needed."""
    body = (
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd a\n"
        "\t\tAssignHavocCmd b\n"
        "\t\tAssignHavocCmd c\n"
        "\t\tAssignExpCmd I IntDiv(IntMul(a b) c)\n"
        "\t}"
    )
    tac = parse_string(
        _wrap(body, syms="a:int\n\tb:int\n\tc:int\n\tI:int"),
        path="<s>",
    )
    res = rewrite_program(
        tac.program, (MUL_DIV_TO_MULDIV,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule == {"MulDiv": 1}
