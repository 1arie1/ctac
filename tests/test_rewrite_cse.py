"""Tests for CSE: fold duplicate static AssignExpCmd RHSes."""

from __future__ import annotations

from ctac.ast.nodes import ApplyExpr, AssignExpCmd, SymbolRef
from ctac.parse import parse_string
from ctac.rewrite import rewrite_program
from ctac.rewrite.rules import CP_ALIAS, CSE


def _wrap(body: str, *, syms: str = "R0:bv256\n\tR1:bv256\n\tR2:bv256\n\tR3:bv256") -> str:
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


def test_cse_folds_structurally_equal_rhs():
    """Two AssignExpCmds with identical RHS: second becomes a SymbolRef alias of the first."""
    tac = parse_string(
        _wrap(
            "\t\tAssignHavocCmd R0\n"
            "\t\tAssignExpCmd R1 IntMul(R0 R0)\n"
            "\t\tAssignExpCmd R2 IntMul(R0 R0)"
        ),
        path="<s>",
    )
    res = rewrite_program(tac.program, (CSE,))
    assert res.hits_by_rule == {"CSE": 1}
    # R1 unchanged (canonical first def).
    assert _rhs(res.program, "R1") == ApplyExpr("IntMul", (SymbolRef("R0"), SymbolRef("R0")))
    # R2 folded to SymbolRef(R1).
    assert _rhs(res.program, "R2") == SymbolRef("R1")


def test_cse_does_not_fire_on_non_duplicate():
    tac = parse_string(
        _wrap(
            "\t\tAssignHavocCmd R0\n"
            "\t\tAssignExpCmd R1 IntMul(R0 R0)\n"
            "\t\tAssignExpCmd R2 IntAdd(R0 R0)"
        ),
        path="<s>",
    )
    res = rewrite_program(tac.program, (CSE,))
    assert res.hits_by_rule == {}


def test_cse_skips_symbolref_rhs():
    """Plain `X = Y` aliases are CP's territory; CSE leaves them alone."""
    tac = parse_string(
        _wrap(
            "\t\tAssignHavocCmd R0\n"
            "\t\tAssignExpCmd R1 R0\n"
            "\t\tAssignExpCmd R2 R0"
        ),
        path="<s>",
    )
    res = rewrite_program(tac.program, (CSE,))
    assert res.hits_by_rule == {}


def test_cse_skips_const_rhs():
    """Constant RHSes aren't worth folding — they're already canonical."""
    tac = parse_string(
        _wrap(
            "\t\tAssignExpCmd R1 0x5\n"
            "\t\tAssignExpCmd R2 0x5"
        ),
        path="<s>",
    )
    res = rewrite_program(tac.program, (CSE,))
    assert res.hits_by_rule == {}


def test_cse_with_cp_collapses_alias_chain():
    """After CSE creates `R2 = R1`, CP propagates uses of R2 to R1."""
    tac = parse_string(
        _wrap(
            "\t\tAssignHavocCmd R0\n"
            "\t\tAssignExpCmd R1 IntMul(R0 R0)\n"
            "\t\tAssignExpCmd R2 IntMul(R0 R0)\n"
            "\t\tAssignExpCmd R3 IntAdd(R2 R2)"
        ),
        path="<s>",
    )
    res = rewrite_program(tac.program, (CSE, CP_ALIAS))
    # After both rules fire: R2 -> alias of R1, then R3's R2 refs -> R1.
    rhs_r3 = _rhs(res.program, "R3")
    assert isinstance(rhs_r3, ApplyExpr) and rhs_r3.op == "IntAdd"
    # R3's args both reference R1 (not R2) post-CP.
    assert rhs_r3.args == (SymbolRef("R1"), SymbolRef("R1"))


def test_cse_folds_canonically_equivalent_meta_suffixes():
    """SymbolRefs differing only by DSA meta-suffix count as equal under CSE."""
    tac_src = """TACSymbolTable {
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
\t\tAssignExpCmd R1 IntMul(R0:5 R0)
\t\tAssignExpCmd R2 IntMul(R0 R0:7)
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""
    tac = parse_string(tac_src, path="<s>")
    res = rewrite_program(tac.program, (CSE,))
    assert res.hits_by_rule == {"CSE": 1}


def test_cse_with_three_duplicates_keeps_the_first():
    tac = parse_string(
        _wrap(
            "\t\tAssignHavocCmd R0\n"
            "\t\tAssignExpCmd R1 IntMul(R0 R0)\n"
            "\t\tAssignExpCmd R2 IntMul(R0 R0)\n"
            "\t\tAssignExpCmd R3 IntMul(R0 R0)",
            syms="R0:bv256\n\tR1:bv256\n\tR2:bv256\n\tR3:bv256",
        ),
        path="<s>",
    )
    res = rewrite_program(tac.program, (CSE,))
    assert res.hits_by_rule.get("CSE", 0) == 2
    assert _rhs(res.program, "R2") == SymbolRef("R1")
    assert _rhs(res.program, "R3") == SymbolRef("R1")


def test_cse_does_not_self_alias_the_canonical_first():
    """The canonical first def must not be rewritten to reference itself."""
    tac = parse_string(
        _wrap(
            "\t\tAssignHavocCmd R0\n"
            "\t\tAssignExpCmd R1 IntMul(R0 R0)\n"
            "\t\tAssignExpCmd R2 IntMul(R0 R0)"
        ),
        path="<s>",
    )
    res = rewrite_program(tac.program, (CSE,))
    # R1's RHS remains the IntMul, not SymbolRef(R1).
    rhs_r1 = _rhs(res.program, "R1")
    assert isinstance(rhs_r1, ApplyExpr) and rhs_r1.op == "IntMul"
