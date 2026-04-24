"""Tests for RANGE_FOLD and the tightened Mod range inference."""

from __future__ import annotations

from ctac.ast.nodes import ApplyExpr, AssignExpCmd, ConstExpr, SymbolRef
from ctac.parse import parse_string
from ctac.rewrite import rewrite_program
from ctac.rewrite.context import RewriteCtx
from ctac.rewrite.range_infer import infer_expr_range
from ctac.rewrite.rules import RANGE_FOLD, SUB_BV_TO_INT


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


def _rhs(program, lhs: str):
    for block in program.blocks:
        for cmd in block.commands:
            if isinstance(cmd, AssignExpCmd) and cmd.lhs == lhs:
                return cmd.rhs
    raise AssertionError(f"no AssignExpCmd for {lhs!r}")


# --- Mod range tightening --------------------------------------------------


def test_mod_range_tightens_when_dividend_fits():
    # Dividend ∈ [0, 100], divisor 2^64 → mod is identity, range (0, 100).
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd A\n"
            "\t\tAssumeExpCmd Le(A 0x64)\n"
            "\t}",
            syms="A:bv256",
        ),
        path="<s>",
    )
    ctx = RewriteCtx(tac.program, symbol_sorts=tac.symbol_sorts)
    ctx.set_position("e", 2)  # past the havoc + assume
    expr = ApplyExpr(
        op="Mod", args=(SymbolRef("A"), ConstExpr("0x10000000000000000"))
    )
    r = infer_expr_range(expr, ctx)
    assert r == (0, 100)


def test_mod_range_falls_back_to_divisor_when_dividend_unbounded():
    # Dividend is bv256 (range [0, 2^256-1]), so dividend doesn't fit in
    # [0, 2^64). Falls back to (0, 2^64 - 1).
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd A\n"
            "\t}",
            syms="A:bv256",
        ),
        path="<s>",
    )
    ctx = RewriteCtx(tac.program, symbol_sorts=tac.symbol_sorts)
    ctx.set_position("e", 1)
    expr = ApplyExpr(
        op="Mod", args=(SymbolRef("A"), ConstExpr("0x10000000000000000"))
    )
    r = infer_expr_range(expr, ctx)
    assert r == (0, (1 << 64) - 1)


# --- RANGE_FOLD ------------------------------------------------------------


def test_range_fold_collapses_sub_on_equality_assume():
    # `Sub(A, B)` with dominating `Eq(B, A)` → range (0, 0) → fold to 0x0.
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd A\n"
            "\t\tAssignHavocCmd B\n"
            "\t\tAssumeExpCmd Eq(B A)\n"
            "\t\tAssignExpCmd C Sub(A B)\n"
            "\t}",
            syms="A:bv256\n\tB:bv256\n\tC:bv256",
        ),
        path="<s>",
    )
    res = rewrite_program(
        tac.program,
        (SUB_BV_TO_INT, RANGE_FOLD),
        symbol_sorts=tac.symbol_sorts,
    )
    rhs = _rhs(res.program, "C")
    assert rhs == ConstExpr("0x0")


def test_range_fold_skips_const_input():
    # ConstExpr is already folded; rule must not fire on it.
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignExpCmd C 0x5\n"
            "\t}",
            syms="C:bv256",
        ),
        path="<s>",
    )
    res = rewrite_program(
        tac.program, (RANGE_FOLD,), symbol_sorts=tac.symbol_sorts
    )
    rhs = _rhs(res.program, "C")
    assert rhs == ConstExpr("0x5")


def test_range_fold_skips_symbol_input():
    # SymbolRef with a singleton range would normally fold, but we
    # intentionally let CP / DCE handle symbol-aliasing instead — the
    # rule only folds compound ApplyExpr.
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd A\n"
            "\t\tAssumeExpCmd Eq(A 0x5)\n"
            "\t\tAssignExpCmd C A\n"
            "\t}",
            syms="A:bv256\n\tC:bv256",
        ),
        path="<s>",
    )
    # Eq(A, 0x5) is a relational (symbol-vs-const) assume; not sure
    # it gives A a singleton range in current ctx. Regardless, the
    # rule is coded to skip SymbolRef inputs, so C stays as SymbolRef.
    res = rewrite_program(
        tac.program, (RANGE_FOLD,), symbol_sorts=tac.symbol_sorts
    )
    rhs = _rhs(res.program, "C")
    assert isinstance(rhs, SymbolRef)


def test_range_fold_cascades_through_mod():
    # Sub folds to 0, then Mod(0, 2^64) has range (0, 0) via the tighter
    # Mod handler, then folds to 0 as well.
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd A\n"
            "\t\tAssignHavocCmd B\n"
            "\t\tAssumeExpCmd Eq(B A)\n"
            "\t\tAssignExpCmd C Mod(Sub(A B) 0x10000000000000000)\n"
            "\t}",
            syms="A:bv256\n\tB:bv256\n\tC:bv256",
        ),
        path="<s>",
    )
    res = rewrite_program(
        tac.program,
        (SUB_BV_TO_INT, RANGE_FOLD),
        symbol_sorts=tac.symbol_sorts,
    )
    rhs = _rhs(res.program, "C")
    assert rhs == ConstExpr("0x0")
