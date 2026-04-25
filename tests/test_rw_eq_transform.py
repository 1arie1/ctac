"""Rule-by-rule unit tests for ctac.rw_eq.emit_equivalence_program."""

from __future__ import annotations

import pytest

from ctac.ast.nodes import (
    AssertCmd,
    AssignExpCmd,
    AssignHavocCmd,
    AssumeExpCmd,
    ConstExpr,
    SymbolRef,
)
from ctac.parse import parse_string
from ctac.rw_eq import EquivContractError, emit_equivalence_program


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


def _block(program, block_id):
    for b in program.blocks:
        if b.id == block_id:
            return b
    raise AssertionError(f"no block {block_id!r}")


# --- Rule 1: identical commands ---

def test_rule_1_identical_emits_once():
    src = _wrap(
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd X\n"
        "\t\tAssignExpCmd Y X\n"
        "\t}",
        syms="X:bv256\n\tY:bv256",
    )
    orig = parse_string(src, path="<o>")
    rw = parse_string(src, path="<r>")
    res = emit_equivalence_program(orig.program, rw.program)
    assert res.rule_hits.get("1_identical", 0) == 2
    assert res.asserts_emitted == 0
    block = _block(res.program, "e")
    assert any(isinstance(c, AssignHavocCmd) and c.lhs == "X" for c in block.commands)
    assert any(isinstance(c, AssignExpCmd) and c.lhs == "Y" for c in block.commands)


# --- Rule 2: same LHS, different RHS ---

def test_rule_2_emits_eq_assert():
    orig = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignExpCmd R Add(0x1 0x2)\n"
            "\t}",
            syms="R:bv256",
        ),
        path="<o>",
    )
    rw = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignExpCmd R 0x3\n"
            "\t}",
            syms="R:bv256",
        ),
        path="<r>",
    )
    res = emit_equivalence_program(orig.program, rw.program)
    assert res.rule_hits.get("2_assignment_diff", 0) == 1
    assert res.asserts_emitted == 1
    block = _block(res.program, "e")
    # CHK<n> bool was added.
    assert any(name == "CHK0" for name, _ in res.extra_symbols)
    # An assertion about CHK0 is emitted.
    assert any(
        isinstance(c, AssertCmd) and c.predicate == SymbolRef("CHK0")
        for c in block.commands
    )


# --- Rule 3: rhs introduces a fresh symbol ---

def test_rule_3_fresh_rhs_symbol_passes_through():
    orig = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd X\n"
            "\t\tAssignExpCmd R X\n"
            "\t}",
            syms="X:bv256\n\tR:bv256",
        ),
        path="<o>",
    )
    rw = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd X\n"
            "\t\tAssignExpCmd T X\n"
            "\t\tAssignExpCmd R T\n"
            "\t}",
            syms="X:bv256\n\tR:bv256\n\tT:bv256",
        ),
        path="<r>",
    )
    res = emit_equivalence_program(orig.program, rw.program)
    # Rule 3 fired once for T = X.
    assert res.rule_hits.get("3_fresh_rhs", 0) == 1
    # Rule 2 closes the chain on R.
    assert res.rule_hits.get("2_assignment_diff", 0) == 1


# --- Rule 4: rhs-only assume ---

def test_rule_4_rhs_only_assume_becomes_assert():
    orig = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd b\n"
            "\t\tAssignExpCmd Y b\n"
            "\t}",
            syms="b:bool\n\tY:bool",
        ),
        path="<o>",
    )
    rw = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd b\n"
            "\t\tAssumeExpCmd b\n"
            "\t\tAssignExpCmd Y b\n"
            "\t}",
            syms="b:bool\n\tY:bool",
        ),
        path="<r>",
    )
    res = emit_equivalence_program(orig.program, rw.program)
    assert res.rule_hits.get("4_rhs_assume", 0) == 1
    assert res.asserts_emitted == 1


# --- Rule 5a: both sides assume ---

def test_rule_5a_both_assumes_pair_with_eq_check():
    # Different conditions on the two sides — rule 5a fires.
    orig = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd a\n"
            "\t\tAssignHavocCmd b\n"
            "\t\tAssumeExpCmd a\n"
            "\t}",
            syms="a:bool\n\tb:bool",
        ),
        path="<o>",
    )
    rw = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd a\n"
            "\t\tAssignHavocCmd b\n"
            "\t\tAssumeExpCmd b\n"
            "\t}",
            syms="a:bool\n\tb:bool",
        ),
        path="<r>",
    )
    res = emit_equivalence_program(orig.program, rw.program)
    assert res.rule_hits.get("5a_assume_pair", 0) == 1
    block = _block(res.program, "e")
    assumes = [c for c in block.commands if isinstance(c, AssumeExpCmd)]
    # Both sides' assumes are kept since their conditions differ.
    assert len(assumes) == 2


def test_rule_5a_identical_assumes_uses_rule_1():
    # Sanity: when conditions are identical, rule 1 (not 5a) handles them.
    src = (
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd b\n"
        "\t\tAssumeExpCmd b\n"
        "\t}"
    )
    orig = parse_string(_wrap(src, syms="b:bool"), path="<o>")
    rw = parse_string(_wrap(src, syms="b:bool"), path="<r>")
    res = emit_equivalence_program(orig.program, rw.program)
    assert res.rule_hits.get("5a_assume_pair", 0) == 0
    assert res.rule_hits.get("1_identical", 0) == 2


# --- Rule 5b: both sides assert ---

def test_rule_5b_both_asserts_become_assumes():
    # Use different predicates so rule 5b fires (rule 1 handles identical).
    orig = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd a\n"
            "\t\tAssignHavocCmd b\n"
            "\t\tAssertCmd a \"check\"\n"
            "\t}",
            syms="a:bool\n\tb:bool",
        ),
        path="<o>",
    )
    rw = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd a\n"
            "\t\tAssignHavocCmd b\n"
            "\t\tAssertCmd b \"check\"\n"
            "\t}",
            syms="a:bool\n\tb:bool",
        ),
        path="<r>",
    )
    res = emit_equivalence_program(orig.program, rw.program)
    assert res.rule_hits.get("5b_assert_pair", 0) == 1
    block = _block(res.program, "e")
    # Original asserts turned into assumes; only the equivalence assert remains.
    asserts = [c for c in block.commands if isinstance(c, AssertCmd)]
    assert len(asserts) == 1
    assert asserts[0].message and asserts[0].message.startswith("rw-eq:")
    # The original `a` and `b` predicates became assumes.
    assume_conds = {c.condition for c in block.commands if isinstance(c, AssumeExpCmd)}
    assert SymbolRef("a") in assume_conds
    assert SymbolRef("b") in assume_conds


# --- Rule 6: rehavoc window (R4A pattern) ---

def test_rule_6_rehavoc_emits_shadow_assert():
    orig = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd A\n"
            "\t\tAssignHavocCmd B\n"
            "\t\tAssumeExpCmd Gt(B 0x0)\n"
            "\t\tAssignExpCmd X Div(A B)\n"
            "\t}",
            syms="A:int\n\tB:int\n\tX:int",
        ),
        path="<o>",
    )
    rw = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd A\n"
            "\t\tAssignHavocCmd B\n"
            "\t\tAssumeExpCmd Gt(B 0x0)\n"
            "\t\tAssignHavocCmd X\n"
            "\t\tAssumeExpCmd Le(Mul(B X) A)\n"
            "\t\tAssumeExpCmd Lt(A Mul(B Add(X 0x1)))\n"
            "\t}",
            syms="A:int\n\tB:int\n\tX:int",
        ),
        path="<r>",
    )
    res = emit_equivalence_program(orig.program, rw.program)
    assert res.rule_hits.get("6_rehavoc", 0) == 1
    assert len(res.rehavoc_sites) == 1
    site = res.rehavoc_sites[0]
    assert site.var_name == "X"
    # Shadow symbol was minted and added to extra_symbols.
    assert any(name.startswith("X__rw_eq") for name, _ in res.extra_symbols)


def test_rule_6_strict_aborts():
    orig = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd A\n"
            "\t\tAssignHavocCmd B\n"
            "\t\tAssignExpCmd X Div(A B)\n"
            "\t}",
            syms="A:int\n\tB:int\n\tX:int",
        ),
        path="<o>",
    )
    rw = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd A\n"
            "\t\tAssignHavocCmd B\n"
            "\t\tAssignHavocCmd X\n"
            "\t\tAssumeExpCmd Le(Mul(B X) A)\n"
            "\t}",
            syms="A:int\n\tB:int\n\tX:int",
        ),
        path="<r>",
    )
    with pytest.raises(EquivContractError, match="rule-6 rehavoc"):
        emit_equivalence_program(orig.program, rw.program, strict=True)


def test_rule_6_check_feasibility_emits_extra_assert_false():
    orig = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd A\n"
            "\t\tAssignHavocCmd B\n"
            "\t\tAssignExpCmd X Div(A B)\n"
            "\t}",
            syms="A:int\n\tB:int\n\tX:int",
        ),
        path="<o>",
    )
    rw = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd A\n"
            "\t\tAssignHavocCmd B\n"
            "\t\tAssignHavocCmd X\n"
            "\t}",
            syms="A:int\n\tB:int\n\tX:int",
        ),
        path="<r>",
    )
    res = emit_equivalence_program(
        orig.program, rw.program, check_feasibility=True
    )
    assert res.feasibility_asserts_emitted == 1
    block = _block(res.program, "e")
    feas = [
        c
        for c in block.commands
        if isinstance(c, AssertCmd)
        and c.predicate == ConstExpr("false")
        and (c.message or "").startswith("rw-eq-feasibility:")
    ]
    assert len(feas) == 1


# --- Rule 7: terminator ---

def test_rule_7_matching_terminator():
    src = (
        "\tBlock e Succ [a] {\n"
        "\t\tJumpCmd a\n"
        "\t}\n"
        "\tBlock a Succ [] {\n"
        "\t}"
    )
    orig = parse_string(_wrap(src, syms="X:bv256"), path="<o>")
    rw = parse_string(_wrap(src, syms="X:bv256"), path="<r>")
    res = emit_equivalence_program(orig.program, rw.program)
    assert res.rule_hits.get("7_terminator", 0) == 1


# --- Rule 10: contract violations ---

def test_rule_10_block_id_mismatch_raises():
    orig = parse_string(
        _wrap(
            "\tBlock entry Succ [] {\n"
            "\t}",
            syms="X:bv256",
        ),
        path="<o>",
    )
    rw = parse_string(
        _wrap(
            "\tBlock different Succ [] {\n"
            "\t}",
            syms="X:bv256",
        ),
        path="<r>",
    )
    with pytest.raises(EquivContractError, match="block-order mismatch"):
        emit_equivalence_program(orig.program, rw.program)


def test_rule_10_successor_mismatch_raises():
    orig = parse_string(
        _wrap(
            "\tBlock entry Succ [a] {\n"
            "\t\tJumpCmd a\n"
            "\t}\n"
            "\tBlock a Succ [] {\n"
            "\t}",
            syms="X:bv256",
        ),
        path="<o>",
    )
    rw = parse_string(
        _wrap(
            "\tBlock entry Succ [b] {\n"
            "\t\tJumpCmd b\n"
            "\t}\n"
            "\tBlock a Succ [] {\n"
            "\t}",
            syms="X:bv256",
        ),
        path="<r>",
    )
    with pytest.raises(EquivContractError):
        emit_equivalence_program(orig.program, rw.program)
