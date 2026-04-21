"""Unit tests for ITE_PURIFY (naming non-trivial Ite conditions as fresh bool vars)."""

from __future__ import annotations

from ctac.ast.nodes import ApplyExpr, AssignExpCmd, SymbolRef
from ctac.parse import parse_string
from ctac.rewrite import rewrite_program
from ctac.rewrite.rules import ITE_PURIFY


def _wrap(body: str, *, syms: str = "R0:bv256\n\tR1:bv256\n\tR2:bv256") -> str:
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


def test_ite_with_compound_cond_is_named():
    """Ite(Eq(R0, 0x0), 0x5, 0x7) -> Ite(TB0, 0x5, 0x7) with `TB0 = Eq(...)` inserted."""
    tac = parse_string(
        _wrap(
            "\t\tAssignHavocCmd R0\n"
            "\t\tAssignExpCmd R1 Ite(Eq(R0 0x0) 0x5 0x7)"
        ),
        path="<s>",
    )
    res = rewrite_program(tac.program, (ITE_PURIFY,))
    assert res.hits_by_rule == {"ITE_PURIFY": 1}
    assert res.extra_symbols == (("TB0", "bool"),)
    # R1's RHS is now an Ite with a SymbolRef condition.
    rhs = _rhs(res.program, "R1")
    assert isinstance(rhs, ApplyExpr) and rhs.op == "Ite"
    assert rhs.args[0] == SymbolRef("TB0")
    # TB0 = Eq(R0, 0x0) is inserted just before R1's assignment.
    block = res.program.blocks[0]
    cmd_texts = [c.raw for c in block.commands]
    tb0_idx = next(i for i, c in enumerate(cmd_texts) if c == "AssignExpCmd TB0 Eq(R0 0x0)")
    r1_idx = next(i for i, c in enumerate(cmd_texts) if c.startswith("AssignExpCmd R1 "))
    assert tb0_idx < r1_idx


def test_ite_with_symbolref_cond_is_untouched():
    """Already-named bool conditions (SymbolRef) don't trigger the rule."""
    tac = parse_string(
        _wrap(
            "\t\tAssignHavocCmd R0\n"
            "\t\tAssignHavocCmd B1\n"
            "\t\tAssignExpCmd R2 Ite(B1 0x5 0x7)",
            syms="R0:bv256\n\tB1:bool\n\tR2:bv256",
        ),
        path="<s>",
    )
    res = rewrite_program(tac.program, (ITE_PURIFY,))
    assert res.hits_by_rule == {}
    assert res.extra_symbols == ()


def test_ite_with_constexpr_cond_is_untouched():
    """Trivial true/false literal conds are not named."""
    tac = parse_string(
        _wrap(
            "\t\tAssignExpCmd R1 Ite(true 0x5 0x7)\n"
            "\t\tAssignExpCmd R2 Ite(false 0x1 0x2)"
        ),
        path="<s>",
    )
    res = rewrite_program(tac.program, (ITE_PURIFY,))
    assert res.hits_by_rule == {}


def test_nested_ite_produces_multiple_tbs():
    """Ite inside Ite's branch: bottom-up creates TB0 for inner, TB1 for outer."""
    tac = parse_string(
        _wrap(
            "\t\tAssignHavocCmd R0\n"
            "\t\tAssignExpCmd R1 Ite(Eq(R0 0x0) Ite(Lt(R0 0x10) 0x1 0x2) 0x3)"
        ),
        path="<s>",
    )
    res = rewrite_program(tac.program, (ITE_PURIFY,))
    assert res.hits_by_rule == {"ITE_PURIFY": 2}
    assert {n for n, _ in res.extra_symbols} == {"TB0", "TB1"}


def test_multiple_ites_in_separate_commands_each_get_their_own_tb():
    tac = parse_string(
        _wrap(
            "\t\tAssignHavocCmd R0\n"
            "\t\tAssignExpCmd R1 Ite(Eq(R0 0x0) 0x5 0x7)\n"
            "\t\tAssignExpCmd R2 Ite(Lt(R0 0x10) 0x1 0x2)"
        ),
        path="<s>",
    )
    res = rewrite_program(tac.program, (ITE_PURIFY,))
    assert res.hits_by_rule == {"ITE_PURIFY": 2}
    assert {n for n, _ in res.extra_symbols} == {"TB0", "TB1"}
    # The TB0 assignment lives just before R1; TB1 just before R2.
    block = res.program.blocks[0]
    names_in_order = [
        c.lhs for c in block.commands if isinstance(c, AssignExpCmd)
    ]
    assert names_in_order == ["TB0", "R1", "TB1", "R2"]


def test_tb_appears_in_rendered_symbol_table():
    """``render_tac_file(extra_symbols=...)`` lists the TB declarations."""
    from ctac.parse import render_tac_file

    tac = parse_string(
        _wrap(
            "\t\tAssignHavocCmd R0\n"
            "\t\tAssignExpCmd R1 Ite(Eq(R0 0x0) 0x5 0x7)"
        ),
        path="<s>",
    )
    res = rewrite_program(tac.program, (ITE_PURIFY,))
    text = render_tac_file(tac, program=res.program, extra_symbols=res.extra_symbols)
    assert "TB0:bool" in text
    # And the result re-parses cleanly.
    reparsed = parse_string(text, path="<s2>")
    assert reparsed.program.blocks


def test_ite_purify_with_cse_folds_duplicate_tbs():
    """Two Ites with identical conds share a single TB after CSE runs in the same phase."""
    from ctac.rewrite.rules import CP_ALIAS, CSE

    tac = parse_string(
        _wrap(
            "\t\tAssignHavocCmd R0\n"
            "\t\tAssignExpCmd R1 Ite(Eq(R0 0x0) 0x5 0x7)\n"
            "\t\tAssignExpCmd R2 Ite(Eq(R0 0x0) 0x1 0x2)"
        ),
        path="<s>",
    )
    res = rewrite_program(tac.program, (ITE_PURIFY, CSE, CP_ALIAS))
    # Both R1 and R2 end up referencing a single TB (the first one).
    r1_cond = _rhs(res.program, "R1").args[0]
    r2_cond = _rhs(res.program, "R2").args[0]
    assert isinstance(r1_cond, SymbolRef) and isinstance(r2_cond, SymbolRef)
    assert r1_cond == r2_cond


def test_dsa_still_valid_after_ite_purify():
    from ctac.analysis import analyze_dsa

    tac = parse_string(
        _wrap(
            "\t\tAssignHavocCmd R0\n"
            "\t\tAssignExpCmd R1 Ite(Eq(R0 0x0) 0x5 0x7)"
        ),
        path="<s>",
    )
    res = rewrite_program(tac.program, (ITE_PURIFY,))
    dsa = analyze_dsa(res.program)
    shape_issues = [i for i in dsa.issues if i.kind == "shape"]
    assert not shape_issues, f"DSA shape issues: {shape_issues}"
