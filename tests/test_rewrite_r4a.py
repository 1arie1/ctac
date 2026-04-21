"""Unit tests for R4a (div purification on non-constant divisors)."""

from __future__ import annotations

from ctac.ast.nodes import (
    ApplyExpr,
    AssignExpCmd,
    AssignHavocCmd,
    AssumeExpCmd,
    ConstExpr,
    SymbolRef,
)
from ctac.parse import parse_string
from ctac.rewrite import rewrite_program
from ctac.rewrite.rules import R4A_DIV_PURIFY


def _cmds(res_program, kind):
    return [
        cmd
        for b in res_program.blocks
        for cmd in b.commands
        if isinstance(cmd, kind)
    ]


def _rhs(res_program, lhs: str):
    for b in res_program.blocks:
        for cmd in b.commands:
            if isinstance(cmd, AssignExpCmd) and cmd.lhs == lhs:
                return cmd.rhs
    raise AssertionError(f"no assignment for {lhs}")


def test_r4a_fires_on_symbolic_positive_divisor():
    """R76 = Div(A, B) with positive-range B becomes: havoc R76 + bound assumes on R76.

    The original LHS name is reused — no fresh ``T<n>`` variable introduced —
    so R76 continues to appear in the output under its original name.
    """
    tac_src = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tA:bv256
\tB:bv256
\tR76:bv256
}
Program {
\tBlock e Succ [] {
\t\tAssignHavocCmd A
\t\tAssignHavocCmd B
\t\tAssumeExpCmd LAnd(Ge(B 0x1 ) Le(B 0xffffffff ) )
\t\tAssignExpCmd R76 Div(A B )
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""
    tac = parse_string(tac_src, path="<s>")
    res = rewrite_program(tac.program, (R4A_DIV_PURIFY,))
    assert res.hits_by_rule.get("R4a", 0) == 1
    # No new symbol is introduced; the LHS (R76) is reused.
    assert res.extra_symbols == ()
    # The original `AssignExpCmd R76 Div(...)` is gone; replaced by
    # `AssignHavocCmd R76` + bound assumes referencing R76.
    block = res.program.blocks[0]
    r76_defs = [
        c for c in block.commands if isinstance(c, (AssignHavocCmd,)) and c.lhs == "R76"
    ]
    assert len(r76_defs) == 1, "R76 should be havoc'd"
    r76_exp_assigns = [
        c
        for c in block.commands
        if isinstance(c, AssignExpCmd) and c.lhs == "R76"
    ]
    assert not r76_exp_assigns, "R76 should no longer have a Div-expr assignment"

    def _refers_to_r76(expr: object) -> bool:
        if isinstance(expr, SymbolRef):
            return expr.name == "R76"
        if isinstance(expr, ApplyExpr):
            return any(_refers_to_r76(a) for a in expr.args)
        return False

    new_assumes = [
        c
        for c in block.commands
        if isinstance(c, AssumeExpCmd) and _refers_to_r76(c.condition)
    ]
    # Le(B*R76, A) and Lt(A, B*(R76+1)); optional Ge(R76, 0).
    assert len(new_assumes) >= 2


def test_r4a_does_not_fire_on_constant_divisor():
    """Constant divisor belongs to R2/R3/R4; R4a must step aside."""
    tac_src = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tA:bv256
\tR:bv256
}
Program {
\tBlock e Succ [] {
\t\tAssignHavocCmd A
\t\tAssignExpCmd R Div(A 0x4 )
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""
    tac = parse_string(tac_src, path="<s>")
    res = rewrite_program(tac.program, (R4A_DIV_PURIFY,))
    assert res.hits_by_rule.get("R4a", 0) == 0


def test_r4a_does_not_fire_when_divisor_range_nonpositive():
    """If B's range includes zero or negative, skip."""
    tac_src = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tA:bv256
\tB:bv256
\tR:bv256
}
Program {
\tBlock e Succ [] {
\t\tAssignHavocCmd A
\t\tAssignHavocCmd B
\t\tAssumeExpCmd Le(B 0xff )
\t\tAssignExpCmd R Div(A B )
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""
    # The assume gives B <= 0xff, and the default lo for a havoc'd bv is 0,
    # so B's range is [0, 0xff] -- lo == 0, R4a must not fire.
    tac = parse_string(tac_src, path="<s>")
    res = rewrite_program(tac.program, (R4A_DIV_PURIFY,))
    assert res.hits_by_rule.get("R4a", 0) == 0


def test_r4a_fires_when_divisor_is_in_another_block():
    """B defined in a non-entry block is fine under current-position placement:
    the havoc + assumes are inserted just before the div, where B is already defined.
    """
    tac_src = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tA:bv256
\tB:bv256
\tR:bv256
}
Program {
\tBlock entry Succ [next] {
\t\tAssignHavocCmd A
\t\tJumpCmd next
\t}
\tBlock next Succ [] {
\t\tAssignHavocCmd B
\t\tAssumeExpCmd LAnd(Ge(B 0x1 ) Le(B 0xff ) )
\t\tAssignExpCmd R Div(A B )
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""
    tac = parse_string(tac_src, path="<s>")
    res = rewrite_program(tac.program, (R4A_DIV_PURIFY,))
    assert res.hits_by_rule.get("R4a", 0) == 1
    # R (the LHS) is reused; the havoc is inserted in block 'next' (where the
    # original Div assignment lived) and the old AssignExpCmd is dropped.
    next_block = next(b for b in res.program.blocks if b.id == "next")
    from ctac.ast.nodes import AssignHavocCmd as _Havoc

    havocs = [c for c in next_block.commands if isinstance(c, _Havoc) and c.lhs == "R"]
    assert len(havocs) == 1
    # No lingering Div-valued assignment for R.
    div_assigns = [
        c
        for c in next_block.commands
        if isinstance(c, AssignExpCmd) and c.lhs == "R"
    ]
    assert not div_assigns


def test_r4a_emits_int_tagged_constants():
    """The +1 and optional 0 constants are (int)-tagged."""
    tac_src = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tA:bv256
\tB:bv256
\tR:bv256
}
Program {
\tBlock e Succ [] {
\t\tAssignHavocCmd A
\t\tAssumeExpCmd LAnd(Ge(A 0x0 ) Le(A 0xffffffff ) )
\t\tAssignHavocCmd B
\t\tAssumeExpCmd LAnd(Ge(B 0x1 ) Le(B 0xffffffff ) )
\t\tAssignExpCmd R Div(A B )
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""
    tac = parse_string(tac_src, path="<s>")
    res = rewrite_program(tac.program, (R4A_DIV_PURIFY,))
    assert res.hits_by_rule.get("R4a", 0) == 1
    # Verify at least one assume has an IntAdd(t, 0x1(int)) pattern.
    found_intadd_typed_one = False

    def walk(e):
        nonlocal found_intadd_typed_one
        if isinstance(e, ApplyExpr):
            if e.op == "IntAdd" and len(e.args) == 2:
                second = e.args[1]
                if isinstance(second, ConstExpr) and second.value == "0x1(int)":
                    found_intadd_typed_one = True
            for a in e.args:
                walk(a)

    for cmd in res.program.blocks[0].commands:
        if isinstance(cmd, AssumeExpCmd):
            walk(cmd.condition)
    assert found_intadd_typed_one


def test_r4a_emits_ge_zero_when_a_non_negative():
    """Optional Ge(T, 0) guard appears when A's range is [>=0, ...]."""
    tac_src = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tA:bv256
\tB:bv256
\tR:bv256
}
Program {
\tBlock e Succ [] {
\t\tAssignHavocCmd A
\t\tAssumeExpCmd LAnd(Ge(A 0x0 ) Le(A 0xffffffff ) )
\t\tAssignHavocCmd B
\t\tAssumeExpCmd LAnd(Ge(B 0x1 ) Le(B 0xffff ) )
\t\tAssignExpCmd R Div(A B )
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""
    tac = parse_string(tac_src, path="<s>")
    res = rewrite_program(tac.program, (R4A_DIV_PURIFY,))
    assert res.hits_by_rule.get("R4a", 0) == 1
    # The LHS (R) is reused; look for `Ge(R, 0x0(int))` among the new assumes.
    ge_zero_found = False
    for cmd in res.program.blocks[0].commands:
        if not isinstance(cmd, AssumeExpCmd):
            continue
        c = cmd.condition
        if (
            isinstance(c, ApplyExpr)
            and c.op == "Ge"
            and c.args[0] == SymbolRef("R")
            and isinstance(c.args[1], ConstExpr)
            and c.args[1].value == "0x0(int)"
        ):
            ge_zero_found = True
    assert ge_zero_found


def test_r4a_handles_intdiv():
    """IntDiv (Int-typed) is also accepted."""
    tac_src = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tA:bv256
\tB:bv256
\tR:bv256
}
Program {
\tBlock e Succ [] {
\t\tAssignHavocCmd A
\t\tAssignHavocCmd B
\t\tAssumeExpCmd LAnd(Ge(B 0x1 ) Le(B 0xffff ) )
\t\tAssignExpCmd R IntDiv(A B )
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""
    tac = parse_string(tac_src, path="<s>")
    res = rewrite_program(tac.program, (R4A_DIV_PURIFY,))
    assert res.hits_by_rule.get("R4a", 0) == 1


def test_r4a_dsa_still_valid_after_rewrite():
    """Post-rewrite DSA check reports no shape issues."""
    from ctac.analysis import analyze_dsa

    tac_src = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tA:bv256
\tB:bv256
\tR:bv256
}
Program {
\tBlock e Succ [] {
\t\tAssignHavocCmd A
\t\tAssignHavocCmd B
\t\tAssumeExpCmd LAnd(Ge(B 0x1 ) Le(B 0xffff ) )
\t\tAssignExpCmd R Div(A B )
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""
    tac = parse_string(tac_src, path="<s>")
    res = rewrite_program(tac.program, (R4A_DIV_PURIFY,))
    dsa = analyze_dsa(res.program)
    # No "shape" issues introduced.
    shape_issues = [i for i in dsa.issues if i.kind == "shape"]
    assert not shape_issues, f"DSA shape issues after R4a: {shape_issues}"
