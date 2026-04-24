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
