"""Tests for ctac.rewrite.range_infer.infer_expr_range."""

from __future__ import annotations

from ctac.ast.nodes import ApplyExpr, ConstExpr, SymbolRef
from ctac.parse import parse_string
from ctac.rewrite.context import RewriteCtx
from ctac.rewrite.range_infer import infer_expr_range


def _wrap(body: str, *, syms: str = "R850:bv256") -> str:
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


def _ctx(tac) -> RewriteCtx:
    return RewriteCtx(tac.program, symbol_sorts=tac.symbol_sorts)


def test_bv256_symbol_defaults_to_full_range_without_assume():
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd R850\n"
            "\t}"
        ),
        path="<s>",
    )
    ctx = _ctx(tac)
    ctx.set_position("e", 0)
    r = infer_expr_range(SymbolRef("R850"), ctx)
    assert r == (0, (1 << 256) - 1)


def test_bv64_symbol_defaults_to_64_bit_range():
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd X\n"
            "\t}",
            syms="X:bv64",
        ),
        path="<s>",
    )
    ctx = _ctx(tac)
    ctx.set_position("e", 0)
    r = infer_expr_range(SymbolRef("X"), ctx)
    assert r == (0, (1 << 64) - 1)


def test_assume_takes_precedence_over_sort_default():
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd R850\n"
            "\t\tAssumeExpCmd Le(R850 0x4000)\n"
            "\t\tAssumeExpCmd Ge(R850 0x1)\n"
            "\t}"
        ),
        path="<s>",
    )
    ctx = _ctx(tac)
    ctx.set_position("e", 3)
    r = infer_expr_range(SymbolRef("R850"), ctx)
    assert r == (1, 0x4000)


def test_div_by_positive_constant_scales_bounds():
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd R850\n"
            "\t}"
        ),
        path="<s>",
    )
    ctx = _ctx(tac)
    ctx.set_position("e", 0)
    # floor(2^256 - 1 / 2^14) == 2^242 - 1.
    expr = ApplyExpr(op="Div", args=(SymbolRef("R850"), ConstExpr("0x4000")))
    r = infer_expr_range(expr, ctx)
    assert r == (0, (1 << 242) - 1)


def test_div_bounds_compose_with_mul_to_fit_in_bv256():
    # Mul(Div(R850, 2^14), 2^14): with R850 in [0, 2^256 - 1],
    # Div gives [0, 2^242 - 1], then * 2^14 = [0, (2^242 - 1) * 2^14]
    # = [0, 2^256 - 2^14], which fits in bv256.
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd R850\n"
            "\t}"
        ),
        path="<s>",
    )
    ctx = _ctx(tac)
    ctx.set_position("e", 0)
    div = ApplyExpr(op="Div", args=(SymbolRef("R850"), ConstExpr("0x4000")))
    mul = ApplyExpr(op="Mul", args=(div, ConstExpr("0x4000")))
    r = infer_expr_range(mul, ctx)
    assert r is not None
    lo, hi = r
    assert lo == 0
    assert hi < (1 << 256)
    # Upper bound is exactly (2^242 - 1) * 2^14 = 2^256 - 2^14.
    assert hi == (1 << 256) - (1 << 14)


def test_div_by_zero_or_non_constant_yields_none():
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd R850\n"
            "\t\tAssignHavocCmd K\n"
            "\t}",
            syms="R850:bv256\n\tK:bv256",
        ),
        path="<s>",
    )
    ctx = _ctx(tac)
    ctx.set_position("e", 0)
    # Div by 0 constant: no bound.
    d0 = ApplyExpr(op="Div", args=(SymbolRef("R850"), ConstExpr("0x0")))
    assert infer_expr_range(d0, ctx) is None
    # Div by non-constant symbol: no bound.
    dk = ApplyExpr(op="Div", args=(SymbolRef("R850"), SymbolRef("K")))
    assert infer_expr_range(dk, ctx) is None


def test_mod_by_positive_constant_bounds_to_divisor_minus_one():
    # a mod K is always in [0, K-1] for positive K, regardless of a's range.
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd R1060\n"
            "\t}",
            syms="R1060:bv256",
        ),
        path="<s>",
    )
    ctx = _ctx(tac)
    ctx.set_position("e", 0)
    expr = ApplyExpr(op="Mod", args=(SymbolRef("R1060"), ConstExpr("0x100000000")))
    r = infer_expr_range(expr, ctx)
    assert r == (0, (1 << 32) - 1)


def test_mod_composes_with_mul_to_stay_in_bv256():
    # Mul(Mod(R1060, 2^32), 2^14) — mod bounds to [0, 2^32 - 1], times
    # 2^14 gives [0, (2^32 - 1) * 2^14] = [0, 2^46 - 2^14], easily fits.
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd R1060\n"
            "\t}",
            syms="R1060:bv256",
        ),
        path="<s>",
    )
    ctx = _ctx(tac)
    ctx.set_position("e", 0)
    inner = ApplyExpr(op="Mod", args=(SymbolRef("R1060"), ConstExpr("0x100000000")))
    expr = ApplyExpr(op="Mul", args=(inner, ConstExpr("0x4000")))
    r = infer_expr_range(expr, ctx)
    assert r is not None
    lo, hi = r
    assert lo == 0
    assert hi == ((1 << 32) - 1) * (1 << 14)
    assert hi < (1 << 256)


def test_unknown_sort_returns_none_without_assume():
    # int-sorted symbol, no dominating assume, no static def — no bound.
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd I1\n"
            "\t}",
            syms="I1:int",
        ),
        path="<s>",
    )
    ctx = _ctx(tac)
    ctx.set_position("e", 0)
    assert infer_expr_range(SymbolRef("I1"), ctx) is None


# ---------------------------------------------------------------------------
# Concept-op transfer functions (IntCeilDiv, IntMulDiv, IntMulDivCeil).
# Each is multi-fused arithmetic; the transfer is tighter than naively
# decomposing because the concept's contract pins non-negativity and
# positive divisor.
# ---------------------------------------------------------------------------


def test_int_ceil_div_const_divisor_bounds_tight():
    # IntCeilDiv(A, 2^14) with A in [0, 2^32-1]: ceil(0/2^14)=0,
    # ceil((2^32-1)/2^14) = ((2^32-1) + 2^14 - 1) / 2^14 = 2^18 (one above
    # the floor).
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd A\n"
            "\t\tAssumeExpCmd Le(A 0xffffffff)\n"
            "\t}",
            syms="A:bv256",
        ),
        path="<s>",
    )
    ctx = _ctx(tac)
    ctx.set_position("e", 2)
    expr = ApplyExpr(
        op="IntCeilDiv", args=(SymbolRef("A"), ConstExpr("0x4000"))
    )
    r = infer_expr_range(expr, ctx)
    assert r is not None
    lo, hi = r
    assert lo == 0
    assert hi == (1 << 18)


def test_int_ceil_div_symbolic_divisor_with_known_range():
    # IntCeilDiv(A, B) with A in [0, 100] and B in [1, 10]:
    # lo = ceil(0/10) = 0, hi = ceil(100/1) = 100.
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd A\n"
            "\t\tAssumeExpCmd Le(A 0x64)\n"
            "\t\tAssignHavocCmd B\n"
            "\t\tAssumeExpCmd LAnd(Ge(B 0x1) Le(B 0xa))\n"
            "\t}",
            syms="A:bv256\n\tB:bv256",
        ),
        path="<s>",
    )
    ctx = _ctx(tac)
    ctx.set_position("e", 4)
    expr = ApplyExpr(op="IntCeilDiv", args=(SymbolRef("A"), SymbolRef("B")))
    r = infer_expr_range(expr, ctx)
    assert r == (0, 100)


def test_int_mul_div_symbolic_divisor_uses_floor_div_nonneg():
    # IntMulDiv(A, B, C) with A in [0, 10], B in [0, 20], C in [1, 5]:
    # mul = [0, 200], floor_div = [0/5, 200/1] = [0, 200].
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd A\n"
            "\t\tAssumeExpCmd Le(A 0xa)\n"
            "\t\tAssignHavocCmd B\n"
            "\t\tAssumeExpCmd Le(B 0x14)\n"
            "\t\tAssignHavocCmd C\n"
            "\t\tAssumeExpCmd LAnd(Ge(C 0x1) Le(C 0x5))\n"
            "\t}",
            syms="A:bv256\n\tB:bv256\n\tC:bv256",
        ),
        path="<s>",
    )
    ctx = _ctx(tac)
    ctx.set_position("e", 6)
    expr = ApplyExpr(
        op="IntMulDiv",
        args=(SymbolRef("A"), SymbolRef("B"), SymbolRef("C")),
    )
    r = infer_expr_range(expr, ctx)
    assert r == (0, 200)


def test_int_mul_div_ceil_const_divisor_bounds_tight():
    # IntMulDivCeil(A, 2^14, 2^14) — degenerate b=c=2^14: ceil(A*2^14/2^14) = A.
    # With A in [0, 2^32-1], result is [0, 2^32-1].
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd A\n"
            "\t\tAssumeExpCmd Le(A 0xffffffff)\n"
            "\t}",
            syms="A:bv256",
        ),
        path="<s>",
    )
    ctx = _ctx(tac)
    ctx.set_position("e", 2)
    expr = ApplyExpr(
        op="IntMulDivCeil",
        args=(SymbolRef("A"), ConstExpr("0x4000"), ConstExpr("0x4000")),
    )
    r = infer_expr_range(expr, ctx)
    assert r is not None
    lo, hi = r
    assert lo == 0
    # The interval-arithmetic bound is loose: mul gives [0, A_hi * 2^14],
    # then ceil-div by 2^14 gives [0, A_hi]. So hi == 2^32-1.
    assert hi == (1 << 32) - 1


def test_int_mul_div_ceil_symbolic_divisor():
    # IntMulDivCeil(A, B, C): a in [0,10], b in [0,20], c in [1,5]:
    # mul = [0, 200]; ceil(0/5)=0; ceil(200/1)=200.
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd A\n"
            "\t\tAssumeExpCmd Le(A 0xa)\n"
            "\t\tAssignHavocCmd B\n"
            "\t\tAssumeExpCmd Le(B 0x14)\n"
            "\t\tAssignHavocCmd C\n"
            "\t\tAssumeExpCmd LAnd(Ge(C 0x1) Le(C 0x5))\n"
            "\t}",
            syms="A:bv256\n\tB:bv256\n\tC:bv256",
        ),
        path="<s>",
    )
    ctx = _ctx(tac)
    ctx.set_position("e", 6)
    expr = ApplyExpr(
        op="IntMulDivCeil",
        args=(SymbolRef("A"), SymbolRef("B"), SymbolRef("C")),
    )
    r = infer_expr_range(expr, ctx)
    assert r == (0, 200)


def test_int_mul_div_ceil_zero_operand_pins_zero():
    # IntMulDivCeil(0, B, C) with B, C symbolic: A=0 makes mul=0, hence
    # ceil(0/C)=0 for any positive C. Tight singleton.
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd B\n"
            "\t\tAssumeExpCmd Le(B 0x14)\n"
            "\t\tAssignHavocCmd C\n"
            "\t\tAssumeExpCmd LAnd(Ge(C 0x1) Le(C 0x5))\n"
            "\t}",
            syms="B:bv256\n\tC:bv256",
        ),
        path="<s>",
    )
    ctx = _ctx(tac)
    ctx.set_position("e", 4)
    expr = ApplyExpr(
        op="IntMulDivCeil",
        args=(ConstExpr("0x0"), SymbolRef("B"), SymbolRef("C")),
    )
    r = infer_expr_range(expr, ctx)
    assert r == (0, 0)
