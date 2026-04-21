"""Tests for RewriteCtx: DSA-based static classification and dominators."""

from __future__ import annotations

from ctac.parse import parse_string
from ctac.rewrite.context import RewriteCtx


def _tac_single_block() -> str:
    return """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tR0:bv256
\tR1:bv256
\tR2:bv256
}
Program {
\tBlock e Succ [] {
\t\tAssignHavocCmd R0
\t\tAssumeExpCmd Le(R0 0xff)
\t\tAssignExpCmd R1 Add(R0 R0)
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""


def test_havoc_defined_var_is_static():
    """Havoc'd single-def symbols count as DSA-static."""
    tac = parse_string(_tac_single_block(), path="<s>")
    ctx = RewriteCtx(tac.program)
    assert ctx.is_static("R0")
    # No RHS expression to return for a havoc, but is_static is still True.
    assert ctx.definition("R0") is None


def test_expcmd_defined_var_is_static_with_rhs():
    tac = parse_string(_tac_single_block(), path="<s>")
    ctx = RewriteCtx(tac.program)
    assert ctx.is_static("R1")
    assert ctx.definition("R1") is not None


def test_havoc_var_has_range_from_dominating_assume():
    """Range lookup still works for havoc-defined symbols."""
    tac = parse_string(_tac_single_block(), path="<s>")
    ctx = RewriteCtx(tac.program)
    ctx.set_position("e", 2)  # after the assume
    # Le(R0, 0xff) -> lower defaults to 0 via range() not directly;
    # but our range() returns (None, 255) — consumers fill in 0.
    r = ctx.range("R0")
    assert r is not None
    lo, hi = r
    assert hi == 0xFF


def test_dynamic_symbol_is_not_static():
    """Diamond-merged symbols are DSA-dynamic and therefore not static."""
    tac_src = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tx:bv256
\tc:bool
}
Program {
\tBlock entry Succ [L, R] {
\t\tAssignHavocCmd c
\t\tJumpiCmd L R c
\t}
\tBlock L Succ [J] {
\t\tAssignExpCmd x 0x1
\t\tJumpCmd J
\t}
\tBlock R Succ [J] {
\t\tAssignExpCmd x 0x2
\t\tJumpCmd J
\t}
\tBlock J Succ [] {
\t\tAssumeExpCmd Eq(x 0x1)
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""
    tac = parse_string(tac_src, path="<s>")
    ctx = RewriteCtx(tac.program)
    assert not ctx.is_static("x")
    assert ctx.definition("x") is None


def test_lookthrough_peels_narrow_wrapper():
    """``lookthrough`` should unwrap safe_math_narrow calls as semantic identity."""
    tac_src = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t\tsafe_math_narrow_bv256:JSON{"x":1}
\t}
\tUninterpretedFunctions {
\t}
\tR0:bv256
\tR1:bv256
\tR2:bv256
}
Program {
\tBlock e Succ [] {
\t\tAssignHavocCmd R0
\t\tAssignExpCmd R1 Apply(safe_math_narrow_bv256:bif R0)
\t\tAssignExpCmd R2 R1
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""
    from ctac.ast.nodes import SymbolRef

    tac = parse_string(tac_src, path="<s>")
    ctx = RewriteCtx(tac.program)
    # R2's def is SymbolRef(R1); R1's def is Apply(narrow, R0); narrow peels to R0.
    # lookthrough should chain these to arrive at SymbolRef(R0).
    assert ctx.lookthrough(SymbolRef("R2")) == SymbolRef("R0")
    # Calling lookthrough on the Apply(narrow, ...) directly peels the narrow.
    narrow_expr = ctx.definition("R1")
    assert narrow_expr is not None
    assert ctx.lookthrough(narrow_expr) == SymbolRef("R0")


def test_lookthrough_enables_r2_through_narrow():
    """R2 should fuse through a narrow wrapper on the inner div."""
    from ctac.ast.nodes import ApplyExpr, ConstExpr, SymbolRef

    from ctac.rewrite import rewrite_program
    from ctac.rewrite.rules import R2_DIV_FUSE

    tac_src = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t\tsafe_math_narrow_bv256:JSON{"x":1}
\t}
\tUninterpretedFunctions {
\t}
\tR0:bv256
\tR1:bv256
\tR2:bv256
}
Program {
\tBlock e Succ [] {
\t\tAssignHavocCmd R0
\t\tAssignExpCmd R1 Apply(safe_math_narrow_bv256:bif Div(R0 0x4))
\t\tAssignExpCmd R2 Div(R1 0x8)
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""
    tac = parse_string(tac_src, path="<s>")
    res = rewrite_program(tac.program, (R2_DIV_FUSE,))
    # R2 looks through R1 -> narrow -> Div(R0, 0x4); fuses with outer /0x8.
    assert res.hits_by_rule == {"R2": 1}
    # Expected: Div(R0, 0x20)
    for b in res.program.blocks:
        for cmd in b.commands:
            if getattr(cmd, "lhs", None) == "R2":
                assert cmd.rhs == ApplyExpr("Div", (SymbolRef("R0"), ConstExpr("0x20")))
                return
    raise AssertionError("no assignment for R2")


def test_dominators_via_networkx():
    """Entry dominates everything; diamond merge is dominated by entry."""
    tac_src = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tc:bool
}
Program {
\tBlock entry Succ [L, R] {
\t\tAssignHavocCmd c
\t\tJumpiCmd L R c
\t}
\tBlock L Succ [J] {
\t\tJumpCmd J
\t}
\tBlock R Succ [J] {
\t\tJumpCmd J
\t}
\tBlock J Succ [] {
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""
    tac = parse_string(tac_src, path="<s>")
    ctx = RewriteCtx(tac.program)
    # entry dominates every block in the CFG
    for bid in ("entry", "L", "R", "J"):
        assert "entry" in ctx.dominators[bid]
    # L does not dominate J (other path through R bypasses it)
    assert "L" not in ctx.dominators["J"]
    assert "R" not in ctx.dominators["J"]
    # Each block dominates itself
    for bid in ("entry", "L", "R", "J"):
        assert bid in ctx.dominators[bid]
