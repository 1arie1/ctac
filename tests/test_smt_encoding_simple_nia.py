from __future__ import annotations

import shutil
import subprocess

import pytest

from ctac.parse import parse_string
from ctac.smt import build_vc, render_smt_script


def _z3_available() -> bool:
    return shutil.which("z3") is not None

TAC_SEA = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\ta:bv256
\tx:bv256
\th:bv256
\tc:bool
\tok:bool
}
Program {
\tBlock entry Succ [left, right] {
\t\tAssignExpCmd a 0x10
\t\tAssignHavocCmd h
\t\tAssignExpCmd c true
\t\tJumpiCmd left right c
\t}
\tBlock left Succ [join] {
\t\tAssignExpCmd x 0x5
\t\tJumpCmd join
\t}
\tBlock right Succ [join] {
\t\tAssignExpCmd x 0x5
\t\tJumpCmd join
\t}
\tBlock join Succ [] {
\t\tAssumeExpCmd LAnd(Le(0x4 x) Le(x 0x8))
\t\tAssignExpCmd ok Ge(x 0x5)
\t\tAssertCmd ok "x must be 5"
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""

TAC_OPS = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tx:bv256
\ty:bv256
\tr:bv256
\tz:bv256
\thm:bv256
\tw:bv256
\tok:bool
}
Program {
\tBlock entry Succ [] {
\t\tAssignExpCmd x 0x1
\t\tAssignExpCmd y Shl(x 0x3)
\t\tAssignExpCmd r ShiftRightLogical(y 0x1)
\t\tAssignExpCmd z BAnd(r 0xff)
\t\tAssignExpCmd hm BAnd(r 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8)
\t\tAssignExpCmd w BXor(z x)
\t\tAssignExpCmd ok Ge(w 0x0)
\t\tAssertCmd ok "ops"
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""

TAC_SHIFTED_BWAND = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tx:bv256
\tsm:bv256
\tok:bool
}
Program {
\tBlock entry Succ [] {
\t\tAssignExpCmd x 0x1
\t\tAssignExpCmd sm BWAnd(x 70368744161280)
\t\tAssignExpCmd ok Ge(sm 0x0)
\t\tAssertCmd ok "shifted"
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""

TAC_MOD_OPS = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tx:bv256
\ty:bv256
\tr:bv256
\ti:int
\tj:int
\tk:int
\tok:bool
}
Program {
\tBlock entry Succ [] {
\t\tAssignExpCmd x 0x11
\t\tAssignExpCmd y 0x3
\t\tAssignExpCmd r Mod(x y)
\t\tAssignExpCmd i 17(int)
\t\tAssignExpCmd j 3(int)
\t\tAssignExpCmd k IntMod(i j)
\t\tAssignExpCmd ok true
\t\tAssertCmd ok "mods"
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""

TAC_BV_ARITH = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tx:bv256
\ty:bv256
\ta:bv256
\ts:bv256
\tm:bv256
\tok:bool
}
Program {
\tBlock entry Succ [] {
\t\tAssignExpCmd x 0x11
\t\tAssignExpCmd y 0x3
\t\tAssignExpCmd a Add(x y)
\t\tAssignExpCmd s Sub(x y)
\t\tAssignExpCmd m Mul(x y)
\t\tAssignExpCmd ok true
\t\tAssertCmd ok "arith"
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""

TAC_BOOL_DYNAMIC = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tc:bool
\tb:bool
\tok:bool
}
Program {
\tBlock entry Succ [left, right] {
\t\tAssignExpCmd c true
\t\tJumpiCmd left right c
\t}
\tBlock left Succ [join] {
\t\tAssignExpCmd b false
\t\tJumpCmd join
\t}
\tBlock right Succ [join] {
\t\tAssignExpCmd b true
\t\tJumpCmd join
\t}
\tBlock join Succ [] {
\t\tAssignExpCmd ok b
\t\tAssertCmd ok "bool dynamic"
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""


TAC_HAVOC_REFINED = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\th1:bv256
\th2:bv256
\th3:bv256
\th4:bv256
\tok:bool
}
Program {
\tBlock entry Succ [] {
\t\tAssignHavocCmd h1
\t\tAssumeExpCmd LAnd(Le(0x8 h1) Le(h1 0x800000))
\t\tAssignHavocCmd h2
\t\tAssumeExpCmd Ge(h2 0x1)
\t\tAssignHavocCmd h3
\t\tAssumeExpCmd Le(h3 0xffffffffffffffff)
\t\tAssignHavocCmd h4
\t\tAssignExpCmd ok true
\t\tAssertCmd ok "havoc refine"
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""


TAC_HAVOC_OR_GUARD = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\th:bv256
\tok:bool
}
Program {
\tBlock entry Succ [] {
\t\tAssignHavocCmd h
\t\tAssumeExpCmd LOr(Ge(h 0x1) Eq(h 0x0))
\t\tAssignExpCmd ok true
\t\tAssertCmd ok "havoc or guard"
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""


TAC_ASSUME_SPACING = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tc:bool
\tok:bool
}
Program {
\tBlock entry Succ [b1] {
\t\tAssignExpCmd c true
\t\tJumpCmd b1
\t}
\tBlock b1 Succ [b2] {
\t\tAssumeExpCmd c
\t\tJumpCmd b2
\t}
\tBlock b2 Succ [] {
\t\tAssumeExpCmd Not(c)
\t\tAssignExpCmd ok true
\t\tAssertCmd ok "assume spacing"
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""


TAC_UF_JOIN = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tc:bool
\tx:bv256
\tw:bv256
\tok:bool
}
Program {
\tBlock entry Succ [left, right] {
\t\tAssignExpCmd c true
\t\tAssignHavocCmd x
\t\tAssignExpCmd w BXor(x x)
\t\tJumpiCmd left right c
\t}
\tBlock left Succ [join] {
\t\tJumpCmd join
\t}
\tBlock right Succ [join] {
\t\tJumpCmd join
\t}
\tBlock join Succ [] {
\t\tAssignExpCmd ok true
\t\tAssertCmd ok "uf join"
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""


def test_sea_vc_logic_and_named_constants() -> None:
    tac = parse_string(TAC_SEA, path="<string>")
    rendered = render_smt_script(build_vc(tac, encoding="sea_vc"))
    # Default is QF_UFNIA regardless of whether this VC actually uses UF.
    assert "(set-logic QF_UFNIA)" in rendered
    assert "(define-fun BV256_MOD () Int " in rendered
    assert "(define-fun BV256_MAX () Int (- BV256_MOD 1))" in rendered


def test_sea_vc_tight_logic_narrows_to_qf_nia_when_no_uf() -> None:
    tac = parse_string(TAC_SEA, path="<string>")
    rendered = render_smt_script(build_vc(tac, encoding="sea_vc", tight_logic=True))
    # With `tight_logic=True` and no UF declarations emitted, narrow to QF_NIA.
    assert "(set-logic QF_NIA)" in rendered


def test_sea_vc_tight_logic_still_uses_qf_ufnia_when_uf_needed() -> None:
    tac = parse_string(TAC_UF_JOIN, path="<string>")
    rendered = render_smt_script(build_vc(tac, encoding="sea_vc", tight_logic=True))
    # Even with `tight_logic=True`, UF-requiring VCs keep QF_UFNIA.
    assert "(set-logic QF_UFNIA)" in rendered


def test_sea_vc_static_dynamic_and_flow_shape() -> None:
    tac = parse_string(TAC_SEA, path="<string>")
    rendered = render_smt_script(build_vc(tac, encoding="sea_vc"))
    assert "Static Assignments and Havoc Domain" in rendered
    assert "Assumptions" in rendered
    assert "Dynamic Assignments" in rendered
    assert "CFG Reachability" in rendered
    assert "Exit and Assert-Failure Objective" in rendered
    assert "(assert (= a 16))" in rendered
    # x is dynamic with same RHS in both branches; compacted to plain equality.
    assert "(assert (= x 5))" in rendered
    assert "(ite BLK_" not in rendered
    assert "(assert (=> BLK_left c))" in rendered
    assert "(assert (=> BLK_right (not c)))" in rendered
    assert "(assert (=> BLK_join (or BLK_left BLK_right)))" in rendered
    assert "(assert (=> BLK_join (or (not BLK_left) (not BLK_right))))" in rendered


def test_sea_vc_cfg_at_most_falls_back_with_ufs() -> None:
    tac = parse_string(TAC_UF_JOIN, path="<string>")
    rendered = render_smt_script(build_vc(tac, encoding="sea_vc"))
    assert "(set-logic QF_UFNIA)" in rendered
    assert "((_ at-most 1) BLK_left BLK_right)" not in rendered
    assert "(assert (=> BLK_join (or (not BLK_left) (not BLK_right))))" in rendered


def test_sea_vc_assume_and_exit_assert_failure() -> None:
    tac = parse_string(TAC_SEA, path="<string>")
    rendered = render_smt_script(build_vc(tac, encoding="sea_vc"))
    assert "(assert (=> BLK_join (<= 4 x 8)))" in rendered
    assert "(assert (=> BLK_EXIT (and (not ok) BLK_join)))" in rendered
    assert "(assert BLK_EXIT)" in rendered


def test_sea_vc_havoc_range_assumptions() -> None:
    tac = parse_string(TAC_SEA, path="<string>")
    rendered = render_smt_script(build_vc(tac, encoding="sea_vc"))
    assert "(assert (<= 0 h BV256_MAX))" in rendered


def test_sea_vc_havoc_immediate_refine_skips_default_range() -> None:
    tac = parse_string(TAC_HAVOC_REFINED, path="<string>")
    rendered = render_smt_script(build_vc(tac, encoding="sea_vc"))
    assert "(assert (<= 0 h1 BV256_MAX))" not in rendered
    assert "(assert (<= h2 BV256_MAX))" not in rendered
    assert "(assert (<= 0 h3))" not in rendered
    assert "(assert (<= 1 h2 BV256_MAX))" in rendered
    assert "(assert (<= 0 h3 MASK_LOW_64))" in rendered
    assert "(assert (<= 0 h4 BV256_MAX))" in rendered


def test_sea_vc_havoc_or_guard_keeps_default_range() -> None:
    tac = parse_string(TAC_HAVOC_OR_GUARD, path="<string>")
    rendered = render_smt_script(build_vc(tac, encoding="sea_vc"))
    assert "(assert (<= 0 h BV256_MAX))" in rendered


def test_sea_vc_blank_line_between_assume_blocks() -> None:
    tac = parse_string(TAC_ASSUME_SPACING, path="<string>")
    rendered = render_smt_script(build_vc(tac, encoding="sea_vc"))
    assert "(assert (=> BLK_b1 c))\n\n(assert (=> BLK_b2 (not c)))" in rendered


def test_sea_vc_bwand_shifted_contiguous_mask_rewrite() -> None:
    tac = parse_string(TAC_SHIFTED_BWAND, path="<string>")
    rendered = render_smt_script(build_vc(tac, encoding="sea_vc"))
    assert "(assert (= sm (* (mod (div x" in rendered
    assert "16384" in rendered
    assert "4294967296" in rendered or "POW2_32" in rendered
    assert "bv256_and" not in rendered


def test_sea_vc_shift_mask_rewrites_and_uf_fallback() -> None:
    tac = parse_string(TAC_OPS, path="<string>")
    rendered = render_smt_script(build_vc(tac, encoding="sea_vc"))
    assert "(set-logic QF_UFNIA)" in rendered
    assert "(assert (= y (* x 8)))" in rendered
    assert "(assert (= r (div y 2)))" in rendered
    assert "(assert (= z (mod r 256)))" in rendered
    assert "(assert (= hm (* (div r 8) 8)))" in rendered
    assert "(declare-fun bv256_xor (Int Int) Int)" in rendered
    assert "Axiom Instantiations" in rendered
    assert "(define-fun bv256_xor_axiom ((x Int) (y Int)) Bool" in rendered
    assert "; instantiate bv256_xor_axiom for each bv256_xor application" in rendered
    assert "(assert (bv256_xor_axiom z x))" in rendered
    assert "(assert (= w (bv256_xor z x)))" in rendered


def test_sea_vc_define_order_places_pow2_before_mask() -> None:
    tac = parse_string(TAC_OPS, path="<string>")
    rendered = render_smt_script(build_vc(tac, encoding="sea_vc"))
    i_pow2 = rendered.index("(define-fun POW2_3 () Int 8)")
    i_mask = rendered.index("(define-fun MASK_CLEAR_LOW_3 () Int (- BV256_MOD POW2_3))")
    assert i_pow2 < i_mask


def test_sea_vc_no_uf_no_instantiated_axioms() -> None:
    tac = parse_string(TAC_SEA, path="<string>")
    rendered = render_smt_script(build_vc(tac, encoding="sea_vc"))
    assert "(declare-fun bv256_xor (Int Int) Int)" not in rendered
    assert "(ite (= z x) 0 1)" not in rendered


def test_sea_vc_mod_and_intmod_are_plain_int_mod() -> None:
    tac = parse_string(TAC_MOD_OPS, path="<string>")
    rendered = render_smt_script(build_vc(tac, encoding="sea_vc"))
    assert "(assert (= r (mod x y)))" in rendered
    assert "(assert (= k (mod i j)))" in rendered


def test_sea_vc_add_sub_mul_are_bv256_modulo() -> None:
    tac = parse_string(TAC_BV_ARITH, path="<string>")
    rendered = render_smt_script(build_vc(tac, encoding="sea_vc"))
    assert "(assert (= a (mod (+ x y) BV256_MOD)))" in rendered
    assert "(assert (= s (mod (- x y) BV256_MOD)))" in rendered
    assert "(assert (= m (mod (* x y) BV256_MOD)))" in rendered


def test_sea_vc_simplifies_dynamic_bool_ite_leafs() -> None:
    tac = parse_string(TAC_BOOL_DYNAMIC, path="<string>")
    rendered = render_smt_script(build_vc(tac, encoding="sea_vc"))
    # was: (ite BLK_left false true)
    assert "(assert (= b (not BLK_left)))" in rendered


# ---------------------------------------------------------------------------
# IntCeilDiv concept: UF + partial axiom (gated on b > 0). Mirrors the
# bv256_xor axiom infrastructure.

TAC_INT_CEIL_DIV = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\ta:bv256
\tb:bv256
\tx:bv256
\tok:bool
}
Program {
\tBlock entry Succ [] {
\t\tAssignHavocCmd a
\t\tAssignHavocCmd b
\t\tAssumeExpCmd Gt(b 0x0)
\t\tAssignExpCmd x IntCeilDiv(a b)
\t\tAssignExpCmd ok Ge(IntMul(b x) a)
\t\tAssertCmd ok "ceil-div lower bound"
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""


def test_sea_vc_int_ceil_div_emits_uf_and_axiom() -> None:
    """IntCeilDiv lowers to a UF call ``(int_ceil_div a b)``; sea_vc
    declares the UF, emits the partial axiom's ``define-fun`` once, and
    asserts the axiom for each unique application — same shape as the
    existing bv256_xor handling."""
    tac = parse_string(TAC_INT_CEIL_DIV, path="<string>")
    rendered = render_smt_script(build_vc(tac, encoding="sea_vc"))
    assert "(declare-fun int_ceil_div (Int Int) Int)" in rendered
    assert "Axiom Instantiations" in rendered
    assert "(define-fun int_ceil_div_axiom ((a Int) (b Int)) Bool" in rendered
    assert "; instantiate int_ceil_div_axiom for each int_ceil_div application" in rendered
    # The application itself appears as a UF call wrapping the operands.
    assert "(int_ceil_div a b)" in rendered
    # And the per-application axiom is asserted exactly once for (a, b).
    assert "(assert (int_ceil_div_axiom a b))" in rendered


# Discharge VC for a property the axiom should make universally true.
# sea_vc encodes "SAT iff assertion-fail is reachable", so we assert
# ``b*x >= a`` (always true under ``b > 0`` thanks to the axiom) and
# expect ``unsat`` (no state can violate the assertion). If the axiom
# weren't being emitted / weren't being used, z3 could pick any free
# value for the UF and return ``sat`` for the negation.
TAC_INT_CEIL_DIV_DISCHARGE = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\ta:bv256
\tb:bv256
\tx:bv256
\tok:bool
}
Program {
\tBlock entry Succ [] {
\t\tAssignHavocCmd a
\t\tAssignHavocCmd b
\t\tAssumeExpCmd Gt(b 0x0)
\t\tAssignExpCmd x IntCeilDiv(a b)
\t\tAssignExpCmd ok Ge(IntMul(b x) a)
\t\tAssertCmd ok "ceil-div lower bound: b*x >= a holds under b > 0"
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""


@pytest.mark.skipif(not _z3_available(), reason="z3 not on PATH")
def test_sea_vc_int_ceil_div_axiom_discharges_via_z3() -> None:
    """Z3 actually uses the IntCeilDiv axiom: assert the axiom's lower
    bound ``b*x >= a`` and expect ``unsat`` (the assertion can never
    fail). Without the axiom, the UF is free and z3 would pick a value
    violating the bound."""
    tac = parse_string(TAC_INT_CEIL_DIV_DISCHARGE, path="<string>")
    rendered = render_smt_script(build_vc(tac, encoding="sea_vc"))
    proc = subprocess.run(
        ["z3", "-smt2", "-T:10", "-in"],
        input=rendered,
        capture_output=True,
        text=True,
        timeout=30,
    )
    verdict = proc.stdout.strip().splitlines()[0] if proc.stdout else ""
    assert verdict == "unsat", (
        f"expected unsat, got {verdict!r}; z3 stdout: {proc.stdout!r}, "
        f"stderr: {proc.stderr!r}"
    )


# ---------------------------------------------------------------------------
# IntMulDiv concept: floor((a*b)/c) — UF + partial axiom (gated on c > 0).
# Mirrors the IntCeilDiv shape with a 3-arg signature.

TAC_INT_MUL_DIV = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\ta:bv256
\tb:bv256
\tc:bv256
\tq:bv256
\tok:bool
}
Program {
\tBlock entry Succ [] {
\t\tAssignHavocCmd a
\t\tAssignHavocCmd b
\t\tAssignHavocCmd c
\t\tAssumeExpCmd Gt(c 0x0)
\t\tAssignExpCmd q IntMulDiv(a b c)
\t\tAssignExpCmd ok Le(IntMul(c q) IntMul(a b))
\t\tAssertCmd ok "muldiv lower bound"
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""


def test_sea_vc_int_mul_div_emits_uf_and_axiom() -> None:
    """IntMulDiv lowers to a UF call ``(int_mul_div a b c)``; sea_vc
    declares the UF (Int Int Int → Int), emits the partial axiom's
    ``define-fun`` once, and asserts the axiom for each unique
    application — same shape as the existing int_ceil_div handling
    extended to three arguments."""
    tac = parse_string(TAC_INT_MUL_DIV, path="<string>")
    rendered = render_smt_script(build_vc(tac, encoding="sea_vc"))
    assert "(declare-fun int_mul_div (Int Int Int) Int)" in rendered
    assert "Axiom Instantiations" in rendered
    assert "(define-fun int_mul_div_axiom ((a Int) (b Int) (c Int)) Bool" in rendered
    assert (
        "; instantiate int_mul_div_axiom for each int_mul_div application"
        in rendered
    )
    # The application itself appears as a UF call wrapping the operands.
    assert "(int_mul_div a b c)" in rendered
    # And the per-application axiom is asserted exactly once for (a, b, c).
    assert "(assert (int_mul_div_axiom a b c))" in rendered


@pytest.mark.skipif(not _z3_available(), reason="z3 not on PATH")
def test_sea_vc_int_mul_div_axiom_discharges_via_z3() -> None:
    """Z3 actually uses the IntMulDiv axiom: assert the floor lower
    bound ``c*q ≤ a*b`` (always true under ``c > 0``) and expect
    ``unsat``. Without the axiom, the UF would be free and z3 could
    pick a value violating the bound."""
    tac = parse_string(TAC_INT_MUL_DIV, path="<string>")
    rendered = render_smt_script(build_vc(tac, encoding="sea_vc"))
    proc = subprocess.run(
        ["z3", "-smt2", "-T:10", "-in"],
        input=rendered,
        capture_output=True,
        text=True,
        timeout=30,
    )
    verdict = proc.stdout.strip().splitlines()[0] if proc.stdout else ""
    assert verdict == "unsat", (
        f"expected unsat, got {verdict!r}; z3 stdout: {proc.stdout!r}, "
        f"stderr: {proc.stderr!r}"
    )


def test_sea_vc_int_mul_div_arity_mismatch_errors() -> None:
    """Wrong-arity IntMulDiv rejected by the encoder."""
    bad_tac = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\ta:bv256
\tb:bv256
\tq:bv256
\tok:bool
}
Program {
\tBlock entry Succ [] {
\t\tAssignHavocCmd a
\t\tAssignHavocCmd b
\t\tAssignExpCmd q IntMulDiv(a b)
\t\tAssignExpCmd ok Eq(q 0x0)
\t\tAssertCmd ok "wrong arity"
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""
    tac = parse_string(bad_tac, path="<string>")
    with pytest.raises(Exception, match="IntMulDiv expects three args"):
        render_smt_script(build_vc(tac, encoding="sea_vc"))


