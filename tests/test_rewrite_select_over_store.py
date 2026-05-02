"""Tests for SELECT_OVER_STORE: fold Select through Store/Ite chains."""

from __future__ import annotations

from ctac.ast.nodes import ApplyExpr, AssignExpCmd, ConstExpr, SymbolRef
from ctac.parse import parse_string
from ctac.rewrite import rewrite_program
from ctac.rewrite.rules import SELECT_OVER_STORE


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


def _rhs(prog, lhs: str):
    for b in prog.blocks:
        for cmd in b.commands:
            if isinstance(cmd, AssignExpCmd) and cmd.lhs == lhs:
                return cmd.rhs
    raise AssertionError(f"no def for {lhs}")


_BASIC_SYMS = (
    "M0:bytemap\n"
    "\tM1:bytemap\n"
    "\tM2:bytemap\n"
    "\tR0:bv256\n"
    "\tR1:bv256\n"
    "\tR2:bv256\n"
    "\tR3:bv256\n"
    "\tR4:bv256"
)


def test_sos_hit_on_store_key_match():
    """Mn = Store(M_old, c, v); Rj = Select(Mn, c) -> Rj = v."""
    body = (
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd M0\n"
        "\t\tAssignExpCmd M1 Store(M0 0x10 R0)\n"
        "\t\tAssignExpCmd R1 Select(M1 0x10)\n"
        "\t}"
    )
    tac = parse_string(_wrap(body, syms=_BASIC_SYMS), path="<s>")
    res = rewrite_program(
        tac.program, (SELECT_OVER_STORE,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule == {"SelectOverStore": 1}
    assert _rhs(res.program, "R1") == SymbolRef("R0")


def test_sos_constant_disjoint_peel():
    """Mn = Store(M_old, c1, v); Rj = Select(Mn, c2) with c1 != c2
    constants -> Rj = Select(M_old, c2)."""
    body = (
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd M0\n"
        "\t\tAssignExpCmd M1 Store(M0 0x10 R0)\n"
        "\t\tAssignExpCmd R1 Select(M1 0x20)\n"
        "\t}"
    )
    tac = parse_string(_wrap(body, syms=_BASIC_SYMS), path="<s>")
    res = rewrite_program(
        tac.program, (SELECT_OVER_STORE,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule == {"SelectOverStore": 1}
    # R1's RHS becomes Select(M0, 0x20).
    assert _rhs(res.program, "R1") == ApplyExpr(
        "Select", (SymbolRef("M0"), ConstExpr("0x20"))
    )


def test_sos_multistep_chain_to_deeper_hit():
    """M1 = Store(M0, c1, v1); M2 = Store(M1, c2, v2);
    Rj = Select(M2, c1) -> Rj = v1 (peels c2, hits c1)."""
    body = (
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd M0\n"
        "\t\tAssignExpCmd M1 Store(M0 0x10 R0)\n"
        "\t\tAssignExpCmd M2 Store(M1 0x20 R1)\n"
        "\t\tAssignExpCmd R2 Select(M2 0x10)\n"
        "\t}"
    )
    tac = parse_string(_wrap(body, syms=_BASIC_SYMS), path="<s>")
    res = rewrite_program(
        tac.program, (SELECT_OVER_STORE,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule == {"SelectOverStore": 1}
    assert _rhs(res.program, "R2") == SymbolRef("R0")


def test_sos_multistep_chain_to_peeled_leaf():
    """M1 = Store(M0, c1, v1); M2 = Store(M1, c2, v2);
    Rj = Select(M2, c3) (c3 distinct const) -> Rj = Select(M0, c3)."""
    body = (
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd M0\n"
        "\t\tAssignExpCmd M1 Store(M0 0x10 R0)\n"
        "\t\tAssignExpCmd M2 Store(M1 0x20 R1)\n"
        "\t\tAssignExpCmd R2 Select(M2 0x30)\n"
        "\t}"
    )
    tac = parse_string(_wrap(body, syms=_BASIC_SYMS), path="<s>")
    res = rewrite_program(
        tac.program, (SELECT_OVER_STORE,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule == {"SelectOverStore": 1}
    assert _rhs(res.program, "R2") == ApplyExpr(
        "Select", (SymbolRef("M0"), ConstExpr("0x30"))
    )


def test_sos_symbolic_key_bails():
    """Symbolic store key vs symbolic select key, not syntactically
    equal — rule must bail (no fire). Otherwise the unsound case
    'unknown key relation' would peel past the Store."""
    body = (
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd M0\n"
        "\t\tAssignHavocCmd R0\n"
        "\t\tAssignHavocCmd R1\n"
        "\t\tAssignHavocCmd R2\n"
        "\t\tAssignExpCmd M1 Store(M0 R0 R1)\n"
        "\t\tAssignExpCmd R3 Select(M1 R2)\n"
        "\t}"
    )
    tac = parse_string(_wrap(body, syms=_BASIC_SYMS), path="<s>")
    res = rewrite_program(
        tac.program, (SELECT_OVER_STORE,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule == {}
    # R3's RHS unchanged.
    assert _rhs(res.program, "R3") == ApplyExpr(
        "Select", (SymbolRef("M1"), SymbolRef("R2"))
    )


def test_sos_const_disjoint_peels_above_symbolic_key_store():
    """Multi-step chain where a const-disjoint Store sits above a
    symbolic-key Store. The const-disjoint peel is sound on its own;
    the rule should commit to it instead of bailing all the way back.
    Mirror of the request_elevation_group `R1026 = M1021[0x400000020]`
    pattern where the inner walk hits a symbolic-key Store at M1161
    but the four const-disjoint Stores above it should still peel."""
    syms = (
        "M0:bytemap\n"
        "\tM1:bytemap\n"
        "\tM2:bytemap\n"
        "\tR0:bv256\n"
        "\tR1:bv256\n"
        "\tR_sym:bv256\n"
        "\tR_v:bv256"
    )
    body = (
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd M0\n"
        "\t\tAssignHavocCmd R_sym\n"
        "\t\tAssignHavocCmd R_v\n"
        # Inner: Store with symbolic key — un-resolvable for a const Select index.
        "\t\tAssignExpCmd M1 Store(M0 R_sym R_v)\n"
        # Outer: Store at a constant key disjoint from our query.
        "\t\tAssignExpCmd M2 Store(M1 0x10 R0)\n"
        # Query at a different constant key — disjoint from 0x10, can peel.
        "\t\tAssignExpCmd R1 Select(M2 0x20)\n"
        "\t}"
    )
    tac = parse_string(_wrap(body, syms=syms), path="<s>")
    res = rewrite_program(
        tac.program, (SELECT_OVER_STORE,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule == {"SelectOverStore": 1}
    # R1's RHS becomes Select(M1, 0x20) — peeled past the const-disjoint
    # Store at M2 but committed to M1 (the symbolic-key Store can't
    # peel further without region-aware reasoning).
    assert _rhs(res.program, "R1") == ApplyExpr(
        "Select", (SymbolRef("M1"), ConstExpr("0x20"))
    )


def test_sos_symbolic_key_syntactic_equality_hits():
    """Syntactic equality on symbolic keys still folds: the value at
    that exact symbol IS the stored value, regardless of what the
    symbol's runtime value is. Same `R7` reference on both sides."""
    body = (
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd M0\n"
        "\t\tAssignHavocCmd R0\n"
        "\t\tAssignHavocCmd R1\n"
        "\t\tAssignExpCmd M1 Store(M0 R0 R1)\n"
        "\t\tAssignExpCmd R2 Select(M1 R0)\n"
        "\t}"
    )
    tac = parse_string(_wrap(body, syms=_BASIC_SYMS), path="<s>")
    res = rewrite_program(
        tac.program, (SELECT_OVER_STORE,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule == {"SelectOverStore": 1}
    assert _rhs(res.program, "R2") == SymbolRef("R1")


_ITE_DIAMOND_SYMS = (
    "M0:bytemap\n"
    "\tM_t:bytemap\n"
    "\tM_f:bytemap\n"
    "\tM_j:bytemap\n"
    "\tR_q:bv256\n"
    "\tR_t:bv256\n"
    "\tR_f:bv256\n"
    "\tc:bool"
)


def test_sos_ite_shared_root_collapse():
    """Ite-of-bytemaps where both arms peel to the same root:
    M_t = Store(M0, 0x10, R_t); M_f = Store(M0, 0x20, R_f);
    M_j = Ite(c, M_t, M_f); Rj = Select(M_j, 0x30) ->
    Rj = Select(M0, 0x30) (both arms peel through to M0)."""
    body = (
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd M0\n"
        "\t\tAssignHavocCmd R_t\n"
        "\t\tAssignHavocCmd R_f\n"
        "\t\tAssignHavocCmd c\n"
        "\t\tAssignExpCmd M_t Store(M0 0x10 R_t)\n"
        "\t\tAssignExpCmd M_f Store(M0 0x20 R_f)\n"
        "\t\tAssignExpCmd M_j Ite(c M_t M_f)\n"
        "\t\tAssignExpCmd R_q Select(M_j 0x30)\n"
        "\t}"
    )
    tac = parse_string(_wrap(body, syms=_ITE_DIAMOND_SYMS), path="<s>")
    res = rewrite_program(
        tac.program, (SELECT_OVER_STORE,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule.get("SelectOverStore", 0) == 1
    assert _rhs(res.program, "R_q") == ApplyExpr(
        "Select", (SymbolRef("M0"), ConstExpr("0x30"))
    )


def test_sos_ite_arms_disagree_bails():
    """Ite-of-bytemaps where the two arms produce different clean
    resolutions for the same key — rule must bail to avoid inflating
    one Select to two. M_t writes 0x10 := R_t; query is at 0x10 so
    arm M_t resolves to R_t, but arm M_f peels through to
    Select(M0, 0x10). Different resolutions -> no fire."""
    body = (
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd M0\n"
        "\t\tAssignHavocCmd R_t\n"
        "\t\tAssignHavocCmd R_f\n"
        "\t\tAssignHavocCmd c\n"
        "\t\tAssignExpCmd M_t Store(M0 0x10 R_t)\n"
        "\t\tAssignExpCmd M_f Store(M0 0x20 R_f)\n"
        "\t\tAssignExpCmd M_j Ite(c M_t M_f)\n"
        "\t\tAssignExpCmd R_q Select(M_j 0x10)\n"
        "\t}"
    )
    tac = parse_string(_wrap(body, syms=_ITE_DIAMOND_SYMS), path="<s>")
    res = rewrite_program(
        tac.program, (SELECT_OVER_STORE,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule == {}
    # R_q's RHS unchanged.
    assert _rhs(res.program, "R_q") == ApplyExpr(
        "Select", (SymbolRef("M_j"), ConstExpr("0x10"))
    )


def test_sos_cache_reuse_across_multiple_selects():
    """Two Selects with the same (M, k) pair both fold via the cache.
    Pinning the hit count confirms each Select fires once; the cache
    avoids re-walking M's def chain on the second query."""
    body = (
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd M0\n"
        "\t\tAssignHavocCmd R0\n"
        "\t\tAssignExpCmd M1 Store(M0 0x10 R0)\n"
        "\t\tAssignExpCmd R1 Select(M1 0x10)\n"
        "\t\tAssignExpCmd R2 Select(M1 0x10)\n"
        "\t}"
    )
    tac = parse_string(_wrap(body, syms=_BASIC_SYMS), path="<s>")
    res = rewrite_program(
        tac.program, (SELECT_OVER_STORE,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule == {"SelectOverStore": 2}
    assert _rhs(res.program, "R1") == SymbolRef("R0")
    assert _rhs(res.program, "R2") == SymbolRef("R0")


def test_sos_dsa_valid_and_no_use_before_def():
    """End-to-end: rule output remains DSA-valid and use-before-def
    clean across a multi-step chain + Ite."""
    from ctac.analysis import analyze_dsa, analyze_use_before_def, extract_def_use

    body = (
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd M0\n"
        "\t\tAssignHavocCmd R_t\n"
        "\t\tAssignHavocCmd R_f\n"
        "\t\tAssignHavocCmd c\n"
        "\t\tAssignExpCmd M_t Store(M0 0x10 R_t)\n"
        "\t\tAssignExpCmd M_f Store(M0 0x20 R_f)\n"
        "\t\tAssignExpCmd M_j Ite(c M_t M_f)\n"
        "\t\tAssignExpCmd R_q Select(M_j 0x30)\n"
        "\t}"
    )
    tac = parse_string(_wrap(body, syms=_ITE_DIAMOND_SYMS), path="<s>")
    res = rewrite_program(
        tac.program, (SELECT_OVER_STORE,), symbol_sorts=tac.symbol_sorts
    )
    du = extract_def_use(res.program)
    ubd = analyze_use_before_def(res.program, def_use=du)
    dsa = analyze_dsa(res.program, def_use=du)
    assert not ubd.issues, ubd.issues
    assert not dsa.issues, dsa.issues
