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


# ---------------------------------------------------------------------------
# Common-dominator hoist: when CSE's canonical RHS uses a non-entry-defined
# variable, the hoist target must be the deepest common dominator of all
# use sites, not the entry block. Hoisting to entry would either be unsound
# (TCSE in entry uses a variable defined later) or — with the current gate
# — bail entirely, missing the optimization.

_TCSE_HOIST_FIXTURE = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tA:int
\tW:int
\tY:int
\tZ:int
\tQ:int
\tc:bool
\tok:bool
}
Program {
\tBlock entry Succ [M] {
\t\tAssignHavocCmd A
\t\tAssignHavocCmd c
\t\tJumpCmd M
\t}
\tBlock M Succ [B, C] {
\t\tAssignExpCmd W IntAdd(A 0x5(int))
\t\tJumpiCmd B C c
\t}
\tBlock B Succ [J] {
\t\tAssignExpCmd Y IntAdd(W 0x1(int))
\t\tAssumeExpCmd Eq(Y 0x6(int))
\t\tJumpCmd J
\t}
\tBlock C Succ [J] {
\t\tAssignExpCmd Z IntAdd(W 0x1(int))
\t\tAssumeExpCmd Eq(Z 0x6(int))
\t\tJumpCmd J
\t}
\tBlock J Succ [] {
\t\tAssignExpCmd Q IntAdd(W 0x1(int))
\t\tAssignExpCmd ok Eq(Q 0x0(int))
\t\tAssertCmd ok "ok"
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""


def test_cse_hoists_to_common_dominator_when_rhs_uses_non_entry_var():
    """W is defined in block M (not entry); Y, Z, Q each compute
    ``W + 1`` in B, C, J respectively. None of these blocks dominates
    the others (B and C are siblings; J is their common successor),
    so CSE wants to hoist a TCSE.

    Hoisting to entry is wrong: entry doesn't have W defined, so
    ``TCSE = W + 1`` in entry would be a use-before-def. The correct
    target is the deepest block that dominates all of {B, C, J} —
    here that's M, where W is in scope.

    After CSE fires, all three uses should share a single TCSE
    that lives at the end of M, and the resulting program must
    pass use-before-def analysis.
    """
    from ctac.analysis import analyze_use_before_def, extract_def_use

    tac = parse_string(_TCSE_HOIST_FIXTURE, path="<s>")
    res = rewrite_program(
        tac.program, (CSE, CP_ALIAS), symbol_sorts=tac.symbol_sorts
    )

    # CSE should fire on the duplicates (Z and Q both alias to a TCSE
    # that captures Y's RHS, or all three alias to a fresh TCSE).
    assert res.hits_by_rule.get("CSE", 0) >= 2, (
        f"CSE should fire on at least 2 of the 3 duplicate sites; "
        f"hits={dict(res.hits_by_rule)}"
    )

    # Locate the hoisted TCSE.
    tcse_defs = []
    for b in res.program.blocks:
        for cmd in b.commands:
            if isinstance(cmd, AssignExpCmd) and cmd.lhs.startswith("TCSE"):
                tcse_defs.append((b.id, cmd))

    # If CSE hoists, the TCSE must NOT be in the entry block (W is
    # not defined there). It should land in M, the common dominator
    # of the use sites where W is in scope.
    if tcse_defs:
        for block_id, cmd in tcse_defs:
            assert block_id != "entry", (
                f"TCSE {cmd.lhs} placed in entry but its RHS uses W "
                f"which is defined in M, not entry. Use-before-def!"
            )
            assert block_id == "M", (
                f"expected TCSE in common dominator M, found in {block_id}"
            )

    # Output must pass use-before-def regardless.
    du = extract_def_use(res.program)
    ubd = analyze_use_before_def(res.program, def_use=du)
    assert not ubd.issues, (
        f"CSE hoist produced use-before-def: {ubd.issues}"
    )


# ---------------------------------------------------------------------------
# Mid-iteration canon equivalence: when CP propagates a child arg in the
# same iteration, the host RHS becomes canonically equal to a registered
# canon AFTER the iteration's ``_build_rhs_index`` snapshot. The use_blocks
# field then misses the host's block. The slow-path strict-dominator
# computation must still account for the actual cur_block, otherwise it
# can pick a target that doesn't dominate the use being rewritten —
# producing use-before-def in the rewriter's output.

_TCSE_MID_ITER_FIXTURE = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tt:int
\ts:int
\tc1:bool
\tc2:bool
\tX:int
\tY:int
\tok:bool
}
Program {
\tBlock entry Succ [P_a, P_b] {
\t\tAssignHavocCmd t
\t\tAssignHavocCmd c1
\t\tAssignHavocCmd c2
\t\tAssignExpCmd s t
\t\tJumpiCmd P_a P_b c1
\t}
\tBlock P_a Succ [A, other] {
\t\tJumpiCmd A other c2
\t}
\tBlock A Succ [J] {
\t\tAssignExpCmd X IntAdd(t 0x1(int))
\t\tAssumeExpCmd Eq(X 0x0(int))
\t\tJumpCmd J
\t}
\tBlock other Succ [J] {
\t\tJumpCmd J
\t}
\tBlock P_b Succ [J] {
\t\tAssignExpCmd Y IntAdd(s 0x1(int))
\t\tAssumeExpCmd Eq(Y 0x0(int))
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


def test_cse_slow_path_accounts_for_cur_block_via_mid_iter_canon_eq():
    """Sibling block (P_b) becomes canonically equal to a deeper block's
    static def (A's ``IntAdd(t, 0x1)``) only after CP propagates ``s -> t``
    mid-iteration. The RHS index built at iter-start has use_blocks={A}
    only; the strict-dominator of {A} alone is P_a, which does NOT
    dominate P_b. Without including cur_block in the dominator
    computation, CSE hoists TCSE into P_a and reads it from P_b — a
    use-before-def regression on real Solana TAC.

    The fix: include cur_block when computing the strict common
    dominator so the chosen target dominates the use being rewritten.
    """
    from ctac.analysis import analyze_use_before_def, extract_def_use

    tac = parse_string(_TCSE_MID_ITER_FIXTURE, path="<s>")
    res = rewrite_program(
        tac.program, (CSE, CP_ALIAS), symbol_sorts=tac.symbol_sorts
    )

    du = extract_def_use(res.program)
    ubd = analyze_use_before_def(res.program, def_use=du)
    assert not ubd.issues, (
        f"CSE produced use-before-def at mid-iter canon match: {ubd.issues}"
    )
