"""Tests for ``SIGN_EXTEND_UNWRAP`` and ``NEG_S64_ZERO_TEST``."""

from __future__ import annotations

import shutil
import subprocess

import pytest

from ctac.ast.nodes import ApplyExpr, ConstExpr, SymbolRef
from ctac.parse import parse_string
from ctac.rewrite.rules.common import const_to_int
from ctac.rewrite.framework import rewrite_program
from ctac.rewrite.rules import (
    NEG_S64_DOUBLE,
    SIGN_EXT_CMP_LIFT,
    SIGN_EXT_SIGN_TEST,
    NEG_S64_LOW_CHUNK,
    NEG_S64_SIGN_TEST,
    NEG_S64_ZERO_TEST,
    SIGN_EXTEND_UNWRAP,
    WRAP_COMPARE_LIFT,
    default_pipeline,
)


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


def test_rule_fires_with_range_tightening():
    """When ``Mod(X, 2^64)`` pins ``x`` to ``[0, 2^64)``, the emitted
    Ite uses ``x`` directly (no inner Mod)."""
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd R\n"
            "\t\tAssignExpCmd X Mod(R 0x10000000000000000)\n"
            "\t\tAssignExpCmd I Apply(unwrap_twos_complement_256:bif SignExtend(0x7 X))\n"
            "\t\tAssertCmd Le(I 0x100)\n"
            "\t}\n",
            syms="R:bv256\n\tX:bv256\n\tI:int",
        ),
        path="<s>",
    )
    res = rewrite_program(tac.program, (SIGN_EXTEND_UNWRAP,), symbol_sorts=tac.symbol_sorts)
    assert res.hits_by_rule.get("SignExtendUnwrap") == 1

    # Locate the rewritten I-def and check shape.
    i_cmd = next(
        c for b in res.program.blocks for c in b.commands
        if getattr(c, "lhs", None) == "I"
    )
    rhs = i_cmd.rhs
    assert isinstance(rhs, ApplyExpr) and rhs.op == "Ite"
    cond, then_arm, else_arm = rhs.args
    # Cond: Lt(X, 2^63). Range proved 0 <= X < 2^64, so the operand is
    # X directly, not Mod(X, 2^64).
    assert isinstance(cond, ApplyExpr) and cond.op == "Lt"
    assert cond.args[0] == SymbolRef("X")
    # then arm = X; else arm = IntSub(X, 2^64).
    assert then_arm == SymbolRef("X")
    assert isinstance(else_arm, ApplyExpr) and else_arm.op == "IntSub"
    assert else_arm.args[0] == SymbolRef("X")


def test_rule_uses_mod_when_range_unknown():
    """Without a range-pinning def, the rule still fires but wraps
    the operand in ``Mod(_, 2^w)`` for soundness."""
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd R\n"  # range = bv256, not <= 2^64
            "\t\tAssignExpCmd I Apply(unwrap_twos_complement_256:bif SignExtend(0x7 R))\n"
            "\t\tAssertCmd Le(I 0x100)\n"
            "\t}\n",
            syms="R:bv256\n\tI:int",
        ),
        path="<s>",
    )
    res = rewrite_program(tac.program, (SIGN_EXTEND_UNWRAP,), symbol_sorts=tac.symbol_sorts)
    assert res.hits_by_rule.get("SignExtendUnwrap") == 1

    i_cmd = next(
        c for b in res.program.blocks for c in b.commands
        if getattr(c, "lhs", None) == "I"
    )
    rhs = i_cmd.rhs
    assert isinstance(rhs, ApplyExpr) and rhs.op == "Ite"
    cond, then_arm, _else = rhs.args
    # Cond's left operand is Mod(R, 2^64).
    assert isinstance(cond, ApplyExpr) and cond.op == "Lt"
    inner = cond.args[0]
    assert isinstance(inner, ApplyExpr) and inner.op == "Mod"
    assert inner.args[0] == SymbolRef("R")
    # then arm reuses the same Mod.
    assert then_arm == inner


def test_rule_handles_various_byte_indices():
    """``b`` ranges over [0, 31]; each emits a width-correct Ite."""
    for b in (0, 1, 3, 7, 15, 31):
        tac = parse_string(
            _wrap(
                "\tBlock e Succ [] {\n"
                "\t\tAssignHavocCmd X\n"
                f"\t\tAssignExpCmd I Apply(unwrap_twos_complement_256:bif SignExtend(0x{b:x} X))\n"
                "\t\tAssertCmd Le(I 0x100)\n"
                "\t}\n",
                syms="X:bv256\n\tI:int",
            ),
            path="<s>",
        )
        res = rewrite_program(
            tac.program, (SIGN_EXTEND_UNWRAP,), symbol_sorts=tac.symbol_sorts
        )
        assert res.hits_by_rule.get("SignExtendUnwrap") == 1, f"b={b}"


def test_rule_does_not_fire_on_bare_signextend():
    """Without the ``unwrap_twos_complement_256:bif`` wrapper the rule
    declines — the bare ``SignExtend`` use isn't safe to fold to the
    Int form (the result is bv256, not Int)."""
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd X\n"
            "\t\tAssignExpCmd R SignExtend(0x7 X)\n"
            "\t}\n",
            syms="X:bv256\n\tR:bv256",
        ),
        path="<s>",
    )
    res = rewrite_program(tac.program, (SIGN_EXTEND_UNWRAP,), symbol_sorts=tac.symbol_sorts)
    assert res.hits_by_rule.get("SignExtendUnwrap", 0) == 0


def test_rule_in_default_pipeline_eliminates_signextend():
    """End-to-end: running the default pipeline removes every
    ``SignExtend`` use that's wrapped by the canonical unwrap idiom."""
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd R\n"
            "\t\tAssignExpCmd X Mod(R 0x10000000000000000)\n"
            "\t\tAssignExpCmd I IntMul(0x-1(int) Apply(unwrap_twos_complement_256:bif SignExtend(0x7 X)))\n"
            "\t\tAssertCmd Le(I 0x100)\n"
            "\t}\n",
            syms="R:bv256\n\tX:bv256\n\tI:int",
        ),
        path="<s>",
    )
    res = rewrite_program(tac.program, default_pipeline, symbol_sorts=tac.symbol_sorts)

    def _has_op(expr, op):
        if isinstance(expr, ApplyExpr):
            if expr.op == op:
                return True
            return any(_has_op(a, op) for a in expr.args)
        return False

    for b in res.program.blocks:
        for cmd in b.commands:
            rhs = getattr(cmd, "rhs", None) or getattr(cmd, "predicate", None)
            if rhs is not None:
                assert not _has_op(rhs, "SignExtend"), f"SignExtend remains in {cmd!r}"


# ---------------------------------------------------------------------------
# NEG_S64_ZERO_TEST
# ---------------------------------------------------------------------------

_NEG_SYMS = "X:bv256\n\tY:bv256\n\tTBC:bool\n\tI:int\n\tTBG:bool\n\tRZ:bv256\n\tTB:bool"


def _rhs_of(res, lhs):
    for b in res.program.blocks:
        for cmd in b.commands:
            if getattr(cmd, "lhs", None) == lhs:
                return cmd.rhs
    raise AssertionError(f"no def of {lhs!r}")


def test_neg_s64_zero_test_fires_symbol_form():
    """The lopu 207_1 shape: every component behind a named symbol
    (post purify-ite). Collapses the zero-test to Eq(Y, 0)."""
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd X\n"
            "\t\tAssignExpCmd Y Mod(X 0x10000000000000000)\n"
            "\t\tAssignExpCmd TBC Lt(Y 0x8000000000000000)\n"
            "\t\tAssignExpCmd I IntMul(0x-1(int) Ite(TBC Y IntSub(Y 0x10000000000000000(int))))\n"
            "\t\tAssignExpCmd TBG Eq(Y 0x8000000000000000)\n"
            "\t\tAssignExpCmd RZ Ite(TBG X Apply(wrap_twos_complement_256:bif I))\n"
            "\t\tAssignExpCmd TB Eq(RZ 0x0)\n"
            "\t}\n",
            syms=_NEG_SYMS,
        ),
        path="<s>",
    )
    res = rewrite_program(
        tac.program, (NEG_S64_ZERO_TEST,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule.get("NegS64ZeroTest") == 1
    assert _rhs_of(res, "TB") == ApplyExpr(
        "Eq", (SymbolRef("Y"), ConstExpr("0x0"))
    )


def test_neg_s64_zero_test_fires_inline_form():
    """The lopu 201_1 shape: Eq nested inside LAnd, from_s64 inline,
    guard Eq const-first."""
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd X\n"
            "\t\tAssignHavocCmd RZ\n"
            "\t\tAssignExpCmd Y Mod(X 0x10000000000000000)\n"
            "\t\tAssignExpCmd I IntMul(0x-1(int) Ite(Lt(Y 0x8000000000000000) Y IntSub(Y 0x10000000000000000(int))))\n"
            "\t\tAssignExpCmd TB LAnd(Eq(Ite(Eq(0x8000000000000000 Y) X Apply(wrap_twos_complement_256:bif I)) 0x0) Lt(RZ 0x5))\n"
            "\t}\n",
            syms=_NEG_SYMS,
        ),
        path="<s>",
    )
    res = rewrite_program(
        tac.program, (NEG_S64_ZERO_TEST,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule.get("NegS64ZeroTest") == 1
    rhs = _rhs_of(res, "TB")
    assert isinstance(rhs, ApplyExpr) and rhs.op == "LAnd"
    assert rhs.args[0] == ApplyExpr("Eq", (SymbolRef("Y"), ConstExpr("0x0")))


def test_neg_s64_zero_test_fires_when_value_is_its_own_chunk():
    """The TB96 shape: the negated value is already a low chunk
    (x == y, no separate Mod); range proves y < 2^64."""
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd X\n"
            "\t\tAssignExpCmd Y Mod(X 0x10000000000000000)\n"
            "\t\tAssignExpCmd TBC Lt(Y 0x8000000000000000)\n"
            "\t\tAssignExpCmd I IntMul(0x-1(int) Ite(TBC Y IntSub(Y 0x10000000000000000(int))))\n"
            "\t\tAssignExpCmd TBG Eq(Y 0x8000000000000000)\n"
            "\t\tAssignExpCmd TB Eq(Ite(TBG Y Apply(wrap_twos_complement_256:bif I)) 0x0)\n"
            "\t}\n",
            syms=_NEG_SYMS,
        ),
        path="<s>",
    )
    res = rewrite_program(
        tac.program, (NEG_S64_ZERO_TEST,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule.get("NegS64ZeroTest") == 1
    assert _rhs_of(res, "TB") == ApplyExpr(
        "Eq", (SymbolRef("Y"), ConstExpr("0x0"))
    )


def test_neg_s64_zero_test_own_chunk_requires_range():
    """x == y but y not provably < 2^64 (bare bv256 havoc): no fire —
    y = y mod 2^64 doesn't hold and the guard arm tests a different
    value."""
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd Y\n"
            "\t\tAssignExpCmd TBC Lt(Y 0x8000000000000000)\n"
            "\t\tAssignExpCmd I IntMul(0x-1(int) Ite(TBC Y IntSub(Y 0x10000000000000000(int))))\n"
            "\t\tAssignExpCmd TBG Eq(Y 0x8000000000000000)\n"
            "\t\tAssignExpCmd TB Eq(Ite(TBG Y Apply(wrap_twos_complement_256:bif I)) 0x0)\n"
            "\t}\n",
            syms=_NEG_SYMS,
        ),
        path="<s>",
    )
    res = rewrite_program(
        tac.program, (NEG_S64_ZERO_TEST,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule.get("NegS64ZeroTest", 0) == 0


def test_neg_s64_zero_test_requires_chunk_relation():
    """Y extracted from a different wide source than the guard arm:
    the y == 2^63 case would test the wrong symbol — no fire."""
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd X\n"
            "\t\tAssignHavocCmd RZ\n"
            "\t\tAssignExpCmd Y Mod(RZ 0x10000000000000000)\n"
            "\t\tAssignExpCmd TBC Lt(Y 0x8000000000000000)\n"
            "\t\tAssignExpCmd I IntMul(0x-1(int) Ite(TBC Y IntSub(Y 0x10000000000000000(int))))\n"
            "\t\tAssignExpCmd TBG Eq(Y 0x8000000000000000)\n"
            "\t\tAssignExpCmd TB Eq(Ite(TBG X Apply(wrap_twos_complement_256:bif I)) 0x0)\n"
            "\t}\n",
            syms=_NEG_SYMS,
        ),
        path="<s>",
    )
    res = rewrite_program(
        tac.program, (NEG_S64_ZERO_TEST,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule.get("NegS64ZeroTest", 0) == 0


def test_neg_s64_zero_test_requires_neg_one_factor():
    """IntMul by -2 is not the negation idiom the rule certifies —
    no fire."""
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd X\n"
            "\t\tAssignExpCmd Y Mod(X 0x10000000000000000)\n"
            "\t\tAssignExpCmd TBC Lt(Y 0x8000000000000000)\n"
            "\t\tAssignExpCmd I IntMul(0x-2(int) Ite(TBC Y IntSub(Y 0x10000000000000000(int))))\n"
            "\t\tAssignExpCmd TBG Eq(Y 0x8000000000000000)\n"
            "\t\tAssignExpCmd TB Eq(Ite(TBG X Apply(wrap_twos_complement_256:bif I)) 0x0)\n"
            "\t}\n",
            syms=_NEG_SYMS,
        ),
        path="<s>",
    )
    res = rewrite_program(
        tac.program, (NEG_S64_ZERO_TEST,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule.get("NegS64ZeroTest", 0) == 0


@pytest.mark.skipif(shutil.which("z3") is None, reason="z3 not on PATH")
@pytest.mark.parametrize("w", [64, 128, 256])
def test_neg_s64_zero_test_lemma_via_z3(w):
    """The closed-form lemma behind the rule, at every supported
    width: for x in [0, 2^256) and y = x mod 2^w, the round-tripped
    zero test equals Eq(y, 0)."""
    two_h = 1 << (w - 1)
    two_w = 1 << w
    two_256 = 1 << 256
    script = f"""(set-logic QF_NIA)
(declare-const x Int)
(define-fun y () Int (mod x {two_w}))
(define-fun f () Int (ite (< y {two_h}) y (- y {two_w})))
(define-fun w () Int (mod (- 0 f) {two_256}))
(define-fun lhs () Int (ite (= y {two_h}) x w))
(assert (and (<= 0 x) (< x {two_256})))
(assert (not (= (= lhs 0) (= y 0))))
(check-sat)
"""
    proc = subprocess.run(
        ["z3", "-smt2", "-T:10", "-in"],
        input=script, capture_output=True, text=True, timeout=30,
    )
    assert proc.stdout.strip() == "unsat", proc.stdout


# ---------------------------------------------------------------------------
# WRAP_COMPARE_LIFT
# ---------------------------------------------------------------------------

_WRAP_SYMS = "X:bv256\n\tY:bv256\n\tI:int\n\tTB:bool"


def test_wrap_compare_lift_lt_with_sign_guard():
    """The B2595 shape: Lt(wrap_256(-from_s64(y)), 10) lifts to
    0 <= v && v < 10 (v may be negative, so the guard stays)."""
    body = (
        "\t\tAssignHavocCmd X\n"
        "\t\tAssignExpCmd Y Mod(X 0x10000000000000000)\n"
        "\t\tAssignExpCmd I IntMul(0x-1(int) Ite(Lt(Y 0x8000000000000000) Y IntSub(Y 0x10000000000000000(int))))\n"
        "\t\tAssignExpCmd TB Lt(Apply(wrap_twos_complement_256:bif I) 0xa)\n"
    )
    tac = parse_string(
        _wrap(f"\tBlock e Succ [] {{\n{body}\t}}\n", syms=_WRAP_SYMS),
        path="<s>",
    )
    res = rewrite_program(
        tac.program, (WRAP_COMPARE_LIFT,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule.get("WrapCompareLift") == 1
    tb = next(
        c.rhs for b in res.program.blocks for c in b.commands
        if getattr(c, "lhs", None) == "TB"
    )
    assert isinstance(tb, ApplyExpr) and tb.op == "LAnd"
    guard, cmp = tb.args
    assert isinstance(guard, ApplyExpr) and guard.op == "Le"
    assert isinstance(cmp, ApplyExpr) and cmp.op == "Lt"
    assert cmp.args[0] == SymbolRef("I")


def test_wrap_compare_lift_nonneg_drops_guard():
    """range(v) >= 0: wrap is the identity, bare comparison emitted."""
    body = (
        "\t\tAssignHavocCmd X\n"
        "\t\tAssignExpCmd Y Mod(X 0x10000000000000000)\n"
        "\t\tAssignExpCmd TB Lt(Apply(wrap_twos_complement_256:bif Y) 0xa)\n"
    )
    tac = parse_string(
        _wrap(f"\tBlock e Succ [] {{\n{body}\t}}\n", syms=_WRAP_SYMS),
        path="<s>",
    )
    res = rewrite_program(
        tac.program, (WRAP_COMPARE_LIFT,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule.get("WrapCompareLift") == 1
    tb = next(
        c.rhs for b in res.program.blocks for c in b.commands
        if getattr(c, "lhs", None) == "TB"
    )
    assert tb == ApplyExpr("Lt", (SymbolRef("Y"), ConstExpr("0xa")))


def test_wrap_compare_lift_eq_flipped_orientation():
    """Eq(c, wrap(v)) matches via the flip path."""
    body = (
        "\t\tAssignHavocCmd X\n"
        "\t\tAssignExpCmd Y Mod(X 0x10000000000000000)\n"
        "\t\tAssignExpCmd I IntMul(0x-1(int) Ite(Lt(Y 0x8000000000000000) Y IntSub(Y 0x10000000000000000(int))))\n"
        "\t\tAssignExpCmd TB Eq(0x0 Apply(wrap_twos_complement_256:bif I))\n"
    )
    tac = parse_string(
        _wrap(f"\tBlock e Succ [] {{\n{body}\t}}\n", syms=_WRAP_SYMS),
        path="<s>",
    )
    res = rewrite_program(
        tac.program, (WRAP_COMPARE_LIFT,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule.get("WrapCompareLift") == 1
    tb = next(
        c.rhs for b in res.program.blocks for c in b.commands
        if getattr(c, "lhs", None) == "TB"
    )
    assert tb == ApplyExpr("Eq", (SymbolRef("I"), ConstExpr("0x0")))


def test_wrap_compare_lift_no_fire_without_range():
    """Unbounded int argument: the wrap can alias across the modulus,
    the gate holds the rewrite back."""
    body = (
        "\t\tAssignHavocCmd I\n"
        "\t\tAssignExpCmd TB Lt(Apply(wrap_twos_complement_256:bif I) 0xa)\n"
    )
    tac = parse_string(
        _wrap(f"\tBlock e Succ [] {{\n{body}\t}}\n", syms=_WRAP_SYMS),
        path="<s>",
    )
    res = rewrite_program(
        tac.program, (WRAP_COMPARE_LIFT,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule.get("WrapCompareLift", 0) == 0


@pytest.mark.skipif(shutil.which("z3") is None, reason="z3 not on PATH")
def test_wrap_compare_lift_lemma_via_z3():
    """Closed-form lemma: for v in (c - 2^256, 2^256), each lifted
    predicate equals its wrap form. Checked for Lt, Le, Gt, Ge, Eq."""
    two_256 = 1 << 256
    c = 10
    script = f"""(set-logic QF_NIA)
(declare-const v Int)
(define-fun w () Int (mod v {two_256}))
(assert (and (> v (- {c} {two_256})) (< v {two_256})))
(assert (not (and
  (= (= w {c}) (= v {c}))
  (= (< w {c}) (and (<= 0 v) (< v {c})))
  (= (<= w {c}) (and (<= 0 v) (<= v {c})))
  (= (> w {c}) (or (> v {c}) (< v 0)))
  (= (>= w {c}) (or (>= v {c}) (< v 0))))))
(check-sat)
"""
    proc = subprocess.run(
        ["z3", "-smt2", "-T:10", "-in"],
        input=script, capture_output=True, text=True, timeout=30,
    )
    assert proc.stdout.strip() == "unsat", proc.stdout


def test_wrap_compare_lift_distributes_over_ite():
    """The B2595 shape: the wrap sits in an Ite arm. The comparison
    distributes (gated on the arm lifting) and the wrap arm lifts."""
    body = (
        "\t\tAssignHavocCmd X\n"
        "\t\tAssignHavocCmd G\n"
        "\t\tAssignExpCmd Y Mod(X 0x10000000000000000)\n"
        "\t\tAssignExpCmd I IntMul(0x-1(int) Ite(Lt(Y 0x8000000000000000) Y IntSub(Y 0x10000000000000000(int))))\n"
        "\t\tAssignExpCmd TB Lt(Ite(G Apply(wrap_twos_complement_256:bif I) X) 0xa)\n"
    )
    tac = parse_string(
        _wrap(
            f"\tBlock e Succ [] {{\n{body}\t}}\n",
            syms=_WRAP_SYMS + "\n\tG:bool",
        ),
        path="<s>",
    )
    res = rewrite_program(
        tac.program, (WRAP_COMPARE_LIFT,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule.get("WrapCompareLift") == 1
    tb = next(
        c.rhs for b in res.program.blocks for c in b.commands
        if getattr(c, "lhs", None) == "TB"
    )
    assert isinstance(tb, ApplyExpr) and tb.op == "Ite"
    then_arm, else_arm = tb.args[1], tb.args[2]
    # Wrap arm lifted to the guarded Int predicate.
    assert isinstance(then_arm, ApplyExpr) and then_arm.op == "LAnd"
    # Non-wrap arm keeps the plain comparison.
    assert else_arm == ApplyExpr("Lt", (SymbolRef("X"), ConstExpr("0xa")))


def test_wrap_compare_lift_no_distribution_without_liftable_arm():
    """Neither Ite arm lifts: no distribution (cost gate)."""
    body = (
        "\t\tAssignHavocCmd X\n"
        "\t\tAssignHavocCmd Y\n"
        "\t\tAssignHavocCmd G\n"
        "\t\tAssignExpCmd TB Lt(Ite(G X Y) 0xa)\n"
    )
    tac = parse_string(
        _wrap(
            f"\tBlock e Succ [] {{\n{body}\t}}\n",
            syms=_WRAP_SYMS + "\n\tG:bool",
        ),
        path="<s>",
    )
    res = rewrite_program(
        tac.program, (WRAP_COMPARE_LIFT,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule.get("WrapCompareLift", 0) == 0


# ---------------------------------------------------------------------------
# NEG_S64_LOW_CHUNK / NEG_S64_SIGN_TEST
# ---------------------------------------------------------------------------

_GADGET_BODY = (
    "\t\tAssignHavocCmd X\n"
    "\t\tAssignExpCmd Y Mod(X 0x10000000000000000)\n"
    "\t\tAssignExpCmd TBC Lt(Y 0x8000000000000000)\n"
    "\t\tAssignExpCmd I IntMul(0x-1(int) Ite(TBC Y IntSub(Y 0x10000000000000000(int))))\n"
    "\t\tAssignExpCmd TBG Eq(Y 0x8000000000000000)\n"
    "\t\tAssignExpCmd RZ Ite(TBG X Apply(wrap_twos_complement_256:bif I))\n"
)


def _gadget_tac(consumer: str, *, body: str = _GADGET_BODY):
    return parse_string(
        _wrap(
            f"\tBlock e Succ [] {{\n{body}{consumer}\t}}\n",
            syms=_NEG_SYMS + "\n\tR2:bv256",
        ),
        path="<s>",
    )


def test_neg_s64_low_chunk_fires():
    """Mod(gadget, 2^64) -> Ite(Eq(Y, 0), 0, Sub(2^64, Y)). The wide
    source X is unbounded here -- no x gate is needed."""
    tac = _gadget_tac("\t\tAssignExpCmd R2 Mod(RZ 0x10000000000000000)\n")
    res = rewrite_program(
        tac.program, (NEG_S64_LOW_CHUNK,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule.get("NegS64LowChunk") == 1
    rhs = _rhs_of(res, "R2")
    assert isinstance(rhs, ApplyExpr) and rhs.op == "Ite"
    cond, zero, sub = rhs.args
    assert cond == ApplyExpr("Eq", (SymbolRef("Y"), ConstExpr("0x0")))
    assert zero == ConstExpr("0x0")
    assert isinstance(sub, ApplyExpr) and sub.op == "Sub"
    assert sub.args[1] == SymbolRef("Y")


def test_neg_s64_low_chunk_other_modulus_no_fire():
    """Mod by a different constant: not the chunk extract."""
    tac = _gadget_tac("\t\tAssignExpCmd R2 Mod(RZ 0x100000000)\n")
    res = rewrite_program(
        tac.program, (NEG_S64_LOW_CHUNK,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule.get("NegS64LowChunk", 0) == 0


_GADGET_BODY_BOUNDED = (
    "\t\tAssignHavocCmd X\n"
    "\t\tAssumeExpCmd Le(X 0x10000000000000000)\n"
    "\t\tAssignExpCmd Y Mod(X 0x10000000000000000)\n"
    "\t\tAssignExpCmd TBC Lt(Y 0x8000000000000000)\n"
    "\t\tAssignExpCmd I IntMul(0x-1(int) Ite(TBC Y IntSub(Y 0x10000000000000000(int))))\n"
    "\t\tAssignExpCmd TBG Eq(Y 0x8000000000000000)\n"
    "\t\tAssignExpCmd RZ Ite(TBG X Apply(wrap_twos_complement_256:bif I))\n"
)


def test_neg_s64_sign_test_slt_fires_with_bounded_source():
    """Slt(gadget, 0) -> 0 < Y && Y < 2^63, gated on range(X) < 2^255
    (here X <= 2^64 by assume)."""
    tac = _gadget_tac(
        "\t\tAssignExpCmd TB Slt(RZ 0x0)\n", body=_GADGET_BODY_BOUNDED
    )
    res = rewrite_program(
        tac.program, (NEG_S64_SIGN_TEST,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule.get("NegS64SignTest") == 1
    rhs = _rhs_of(res, "TB")
    assert isinstance(rhs, ApplyExpr) and rhs.op == "LAnd"
    low, high = rhs.args
    assert low == ApplyExpr("Lt", (ConstExpr("0x0"), SymbolRef("Y")))
    assert isinstance(high, ApplyExpr) and high.op == "Lt"


def test_neg_s64_sign_test_sle_dual():
    """Sle(0, gadget) -> Y == 0 || Y >= 2^63."""
    tac = _gadget_tac(
        "\t\tAssignExpCmd TB Sle(0x0 RZ)\n", body=_GADGET_BODY_BOUNDED
    )
    res = rewrite_program(
        tac.program, (NEG_S64_SIGN_TEST,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule.get("NegS64SignTest") == 1
    rhs = _rhs_of(res, "TB")
    assert isinstance(rhs, ApplyExpr) and rhs.op == "LOr"


def test_neg_s64_sign_test_unbounded_source_no_fire():
    """X unbounded bv256: the edge arm could be signed-negative, the
    gate holds the rewrite back."""
    tac = _gadget_tac("\t\tAssignExpCmd TB Slt(RZ 0x0)\n")
    res = rewrite_program(
        tac.program, (NEG_S64_SIGN_TEST,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule.get("NegS64SignTest", 0) == 0


@pytest.mark.skipif(shutil.which("z3") is None, reason="z3 not on PATH")
@pytest.mark.parametrize("w", [64, 128, 256])
def test_neg_s64_consumers_lemma_via_z3(w):
    """Closed-form lemmas for the low-chunk and sign-test rewrites
    over the full gadget at every supported width, x in [0, 2^255),
    y = x mod 2^w."""
    two_h = 1 << (w - 1)
    two_w = 1 << w
    two_255 = 1 << 255
    two_256 = 1 << 256
    script = f"""(set-logic QF_NIA)
(declare-const x Int)
(define-fun y () Int (mod x {two_w}))
(define-fun f () Int (ite (< y {two_h}) y (- y {two_w})))
(define-fun w () Int (mod (- 0 f) {two_256}))
(define-fun n () Int (ite (= y {two_h}) x w))
(assert (and (<= 0 x) (< x {two_255})))
(assert (not (and
  (= (mod n {two_w}) (ite (= y 0) 0 (- {two_w} y)))
  (= (>= n {two_255}) (and (< 0 y) (< y {two_h}))))))
(check-sat)
"""
    proc = subprocess.run(
        ["z3", "-smt2", "-T:10", "-in"],
        input=script, capture_output=True, text=True, timeout=30,
    )
    assert proc.stdout.strip() == "unsat", proc.stdout


# ---------------------------------------------------------------------------
# NEG_S64_LOW_CHUNK carry shapes + NEG_S64_DOUBLE
# ---------------------------------------------------------------------------


def test_neg_s64_low_chunk_carry_select():
    """The R2599 shape: Mod(Ite(B0, n, n + 1), 2^64) with n the
    gadget — both arms reduce, the Ite distributes."""
    body = (
        _GADGET_BODY
        + "\t\tAssignHavocCmd G\n"
        + "\t\tAssignExpCmd R3 Ite(G RZ Add(RZ 0x1))\n"
        + "\t\tAssignExpCmd R2 Mod(R3 0x10000000000000000)\n"
    )
    tac = parse_string(
        _wrap(
            f"\tBlock e Succ [] {{\n{body}\t}}\n",
            syms=_NEG_SYMS + "\n\tR2:bv256\n\tR3:bv256\n\tG:bool",
        ),
        path="<s>",
    )
    res = rewrite_program(
        tac.program, (NEG_S64_LOW_CHUNK,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule.get("NegS64LowChunk") == 1
    rhs = _rhs_of(res, "R2")
    assert isinstance(rhs, ApplyExpr) and rhs.op == "Ite"
    assert rhs.args[0] == SymbolRef("G")
    plain, carry = rhs.args[1], rhs.args[2]
    # Plain arm: Ite(Eq(Y, 0), 0, Sub(2^64, Y)).
    assert isinstance(plain, ApplyExpr) and plain.op == "Ite"
    assert plain.args[0] == ApplyExpr("Eq", (SymbolRef("Y"), ConstExpr("0x0")))
    # Carry arm: Ite(Le(Y, 1), Sub(1, Y), Sub(2^64 + 1, Y)).
    assert isinstance(carry, ApplyExpr) and carry.op == "Ite"
    assert carry.args[0] == ApplyExpr("Le", (SymbolRef("Y"), ConstExpr("0x1")))


def test_neg_s64_low_chunk_ite_one_arm_unreducible_no_fire():
    """One Ite arm isn't gadget-built: cost gate, no distribution."""
    body = (
        _GADGET_BODY
        + "\t\tAssignHavocCmd G\n"
        + "\t\tAssignExpCmd R3 Ite(G RZ X)\n"
        + "\t\tAssignExpCmd R2 Mod(R3 0x10000000000000000)\n"
    )
    tac = parse_string(
        _wrap(
            f"\tBlock e Succ [] {{\n{body}\t}}\n",
            syms=_NEG_SYMS + "\n\tR2:bv256\n\tR3:bv256\n\tG:bool",
        ),
        path="<s>",
    )
    res = rewrite_program(
        tac.program, (NEG_S64_LOW_CHUNK,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule.get("NegS64LowChunk", 0) == 0


_DOUBLE_BODY = (
    "\t\tAssignHavocCmd X\n"
    "\t\tAssignExpCmd Y Mod(X 0x10000000000000000)\n"
    "\t\tAssignExpCmd TBC Lt(Y 0x8000000000000000)\n"
    "\t\tAssignExpCmd I IntMul(0x-1(int) Ite(TBC Y IntSub(Y 0x10000000000000000(int))))\n"
    "\t\tAssignExpCmd TBG Eq(Y 0x8000000000000000)\n"
    "\t\tAssignExpCmd RZ Ite(TBG Y Apply(wrap_twos_complement_256:bif I))\n"
    "\t\tAssignExpCmd Y2 Mod(RZ 0x10000000000000000)\n"
    "\t\tAssignExpCmd TBC2 Lt(Y2 0x8000000000000000)\n"
    "\t\tAssignExpCmd I2 IntMul(0x-1(int) Ite(TBC2 Y2 IntSub(Y2 0x10000000000000000(int))))\n"
    "\t\tAssignExpCmd TBG2 Eq(Y2 0x8000000000000000)\n"
    "\t\tAssignExpCmd R2 Ite(TBG2 RZ Apply(wrap_twos_complement_256:bif I2))\n"
)

_DOUBLE_SYMS = (
    _NEG_SYMS + "\n\tY2:bv256\n\tTBC2:bool\n\tI2:int\n\tTBG2:bool\n\tR2:bv256"
)


def test_neg_s64_double_fires():
    """Gadget-of-gadget (the abs low limb) collapses to the 64->256
    sign extension Ite over the original chunk."""
    tac = parse_string(
        _wrap(f"\tBlock e Succ [] {{\n{_DOUBLE_BODY}\t}}\n", syms=_DOUBLE_SYMS),
        path="<s>",
    )
    res = rewrite_program(
        tac.program, (NEG_S64_DOUBLE,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule.get("NegS64Double") == 1
    rhs = _rhs_of(res, "R2")
    assert isinstance(rhs, ApplyExpr) and rhs.op == "Ite"
    cond, ident, ext = rhs.args
    assert isinstance(cond, ApplyExpr) and cond.op == "Le"
    assert cond.args[0] == SymbolRef("Y")
    assert ident == SymbolRef("Y")
    assert isinstance(ext, ApplyExpr) and ext.op == "Add"


def test_neg_s64_double_fires_after_low_chunk_rewrote_link():
    """When NEG_S64_LOW_CHUNK already rewrote Y2's def to its Ite
    emit shape, the alternate evidence path still ties the outer
    gadget to Y."""
    tac = parse_string(
        _wrap(f"\tBlock e Succ [] {{\n{_DOUBLE_BODY}\t}}\n", syms=_DOUBLE_SYMS),
        path="<s>",
    )
    pre = rewrite_program(
        tac.program, (NEG_S64_LOW_CHUNK,), symbol_sorts=tac.symbol_sorts
    )
    assert pre.hits_by_rule.get("NegS64LowChunk") == 1  # Y2's def
    res = rewrite_program(
        pre.program, (NEG_S64_DOUBLE,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule.get("NegS64Double") == 1
    rhs = _rhs_of(res, "R2")
    assert isinstance(rhs, ApplyExpr) and rhs.op == "Ite"
    assert rhs.args[1] == SymbolRef("Y")


@pytest.mark.skipif(shutil.which("z3") is None, reason="z3 not on PATH")
@pytest.mark.parametrize("w", [64, 128])
def test_neg_s64_carry_and_double_lemma_via_z3(w):
    """Closed-form lemmas: the carry chunk (c = 1) and the double
    negation, over the full gadget with x in [0, 2^w) (the x == y
    chunk-evidence regime both rules accept)."""
    two_h = 1 << (w - 1)
    two_w = 1 << w
    two_256 = 1 << 256
    sign_ext = two_256 - two_w
    script = f"""(set-logic QF_NIA)
(declare-const L Int)
(define-fun f () Int (ite (< L {two_h}) L (- L {two_w})))
(define-fun n () Int (ite (= L {two_h}) L (mod (- 0 f) {two_256})))
(define-fun yp () Int (mod n {two_w}))
(define-fun f2 () Int (ite (< yp {two_h}) yp (- yp {two_w})))
(define-fun n2 () Int (ite (= yp {two_h}) n (mod (- 0 f2) {two_256})))
(assert (and (<= 0 L) (< L {two_w})))
(assert (not (and
  (= (mod (+ n 1) {two_w}) (ite (<= L 1) (- 1 L) (- {two_w + 1} L)))
  (= n2 (ite (<= L {two_h}) L (+ L {sign_ext}))))))
(check-sat)
"""
    proc = subprocess.run(
        ["z3", "-smt2", "-T:10", "-in"],
        input=script, capture_output=True, text=True, timeout=30,
    )
    assert proc.stdout.strip() == "unsat", proc.stdout


# ---------------------------------------------------------------------------
# SIGNED_CMP_NEG_ONE
# ---------------------------------------------------------------------------

_M1 = "0x" + "f" * 64


def test_signed_cmp_neg_one_all_orientations():
    """x <=s -1, -1 >=s x normalize to x <s 0; x >s -1, -1 <s x to
    0 <=s x."""
    from ctac.rewrite.rules import SIGNED_CMP_NEG_ONE
    cases = [
        (f"Sle(X {_M1})", "Slt"),
        (f"Sge({_M1} X)", "Slt"),
        (f"Sgt(X {_M1})", "Sle"),
        (f"Slt({_M1} X)", "Sle"),
    ]
    for cond, want_op in cases:
        tac = parse_string(
            _wrap(
                f"\tBlock e Succ [] {{\n\t\tAssignHavocCmd X\n"
                f"\t\tAssignExpCmd TB {cond}\n\t}}\n",
                syms="X:bv256\n\tTB:bool",
            ),
            path="<s>",
        )
        res = rewrite_program(
            tac.program, (SIGNED_CMP_NEG_ONE,), symbol_sorts=tac.symbol_sorts
        )
        assert res.hits_by_rule.get("SignedCmpNegOne") == 1, cond
        rhs = _rhs_of(res, "TB")
        assert isinstance(rhs, ApplyExpr) and rhs.op == want_op, cond


def test_signed_cmp_neg_one_unlocks_sign_test():
    """Sle(gadget, -1) -> Slt(gadget, 0) -> the chunk-interval
    predicate, end to end."""
    from ctac.rewrite.rules import SIGNED_CMP_NEG_ONE
    tac = _gadget_tac(
        f"\t\tAssignExpCmd TB Sle(RZ {_M1})\n", body=_GADGET_BODY_BOUNDED
    )
    res = rewrite_program(
        tac.program,
        (SIGNED_CMP_NEG_ONE, NEG_S64_SIGN_TEST),
        symbol_sorts=tac.symbol_sorts,
    )
    assert res.hits_by_rule.get("SignedCmpNegOne") == 1
    assert res.hits_by_rule.get("NegS64SignTest") == 1
    rhs = _rhs_of(res, "TB")
    assert isinstance(rhs, ApplyExpr) and rhs.op == "LAnd"


# ---------------------------------------------------------------------------
# FROM_S64_ZERO_TEST
# ---------------------------------------------------------------------------


def test_from_s64_zero_test_fires():
    """Eq(from_s64(Y), 0) with Y a chunk -> Eq(Y, 0)."""
    from ctac.rewrite.rules import FROM_S64_ZERO_TEST
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd X\n"
            "\t\tAssignExpCmd Y Mod(X 0x10000000000000000)\n"
            "\t\tAssignExpCmd TBC Lt(Y 0x8000000000000000)\n"
            "\t\tAssignExpCmd TB Eq(Ite(TBC Y IntSub(Y 0x10000000000000000(int))) 0x0)\n"
            "\t}\n",
            syms=_NEG_SYMS,
        ),
        path="<s>",
    )
    res = rewrite_program(
        tac.program, (FROM_S64_ZERO_TEST,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule.get("FromS64ZeroTest") == 1
    assert _rhs_of(res, "TB") == ApplyExpr(
        "Eq", (SymbolRef("Y"), ConstExpr("0x0"))
    )


def test_from_s64_zero_test_requires_chunk_range():
    """Y unbounded bv256: y == 2^64 would also zero the else arm,
    the gate holds the rewrite back."""
    from ctac.rewrite.rules import FROM_S64_ZERO_TEST
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd Y\n"
            "\t\tAssignExpCmd TBC Lt(Y 0x8000000000000000)\n"
            "\t\tAssignExpCmd TB Eq(Ite(TBC Y IntSub(Y 0x10000000000000000(int))) 0x0)\n"
            "\t}\n",
            syms=_NEG_SYMS,
        ),
        path="<s>",
    )
    res = rewrite_program(
        tac.program, (FROM_S64_ZERO_TEST,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule.get("FromS64ZeroTest", 0) == 0


@pytest.mark.skipif(shutil.which("z3") is None, reason="z3 not on PATH")
@pytest.mark.parametrize("w", [64, 128, 256])
def test_from_s64_zero_test_lemma_via_z3(w):
    """For y in [0, 2^w): from_s<w>(y) == 0 iff y == 0."""
    two_h = 1 << (w - 1)
    two_w = 1 << w
    script = f"""(set-logic QF_NIA)
(declare-const y Int)
(define-fun f () Int (ite (< y {two_h}) y (- y {two_w})))
(assert (and (<= 0 y) (< y {two_w})))
(assert (not (= (= f 0) (= y 0))))
(check-sat)
"""
    proc = subprocess.run(
        ["z3", "-smt2", "-T:10", "-in"],
        input=script, capture_output=True, text=True, timeout=30,
    )
    assert proc.stdout.strip() == "unsat", proc.stdout


# ---------------------------------------------------------------------------
# NEG_S64_DOUBLE carry composition (the high-limb un-borrow)
# ---------------------------------------------------------------------------

_CARRY_SYMS = (
    "X1:bv256\n\tY1:bv256\n\tTBC:bool\n\tI1:int\n\tTBG:bool\n\tN1:bv256\n"
    "\tG:bool\n\tX2:bv256\n\tY2:bv256\n\tTBC2:bool\n\tI2:int\n"
    "\tTBG2:bool\n\tR:bv256"
)

_CARRY_BODY = (
    "\t\tAssignHavocCmd X1\n"
    "\t\tAssumeExpCmd Le(X1 0xffffffffffffffff)\n"
    "\t\tAssignExpCmd Y1 Mod(X1 0x10000000000000000)\n"
    "\t\tAssignExpCmd TBC Lt(Y1 0x8000000000000000)\n"
    "\t\tAssignExpCmd I1 IntMul(0x-1(int) Ite(TBC Y1 IntSub(Y1 0x10000000000000000(int))))\n"
    "\t\tAssignExpCmd TBG Eq(Y1 0x8000000000000000)\n"
    "\t\tAssignExpCmd N1 Ite(TBG X1 Apply(wrap_twos_complement_256:bif I1))\n"
    "\t\tAssignHavocCmd G\n"
    "\t\tAssignExpCmd X2 Ite(G N1 Add(N1 0x1))\n"
    "\t\tAssignExpCmd Y2 Mod(X2 0x10000000000000000)\n"
    "\t\tAssignExpCmd TBC2 Lt(Y2 0x8000000000000000)\n"
    "\t\tAssignExpCmd I2 IntMul(0x-1(int) Ite(TBC2 Y2 IntSub(Y2 0x10000000000000000(int))))\n"
    "\t\tAssignExpCmd TBG2 Eq(Y2 0x8000000000000000)\n"
    "\t\tAssignExpCmd R Ite(TBG2 X2 Apply(wrap_twos_complement_256:bif I2))\n"
)


def test_neg_s64_double_carry_composition():
    """The high-limb shape: outer gadget over x' = Ite(g, n1, n1+1)
    with n1 the inner gadget. Value = sign extension of
    z = (-y') mod 2^64."""
    tac = parse_string(
        _wrap(f"\tBlock e Succ [] {{\n{_CARRY_BODY}\t}}\n", syms=_CARRY_SYMS),
        path="<s>",
    )
    res = rewrite_program(
        tac.program, (NEG_S64_DOUBLE,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule.get("NegS64Double") == 1
    rhs = _rhs_of(res, "R")
    # Nested y'-form: Ite(Eq(Y2, 0), 0, Ite(Ge(Y2, 2^63),
    # Sub(2^64, Y2), Add(Sub, C))).
    assert isinstance(rhs, ApplyExpr) and rhs.op == "Ite"
    cond, zero, bands = rhs.args
    assert isinstance(cond, ApplyExpr) and cond.op == "Eq"
    assert const_to_int(zero) == 0
    assert isinstance(bands, ApplyExpr) and bands.op == "Ite"
    assert "Y2" in str(bands)


def test_neg_s64_double_carry_wrong_const_no_fire():
    """Carry of 2 is not the un-borrow composition: no fire."""
    body = _CARRY_BODY.replace("Add(N1 0x1)", "Add(N1 0x2)")
    tac = parse_string(
        _wrap(f"\tBlock e Succ [] {{\n{body}\t}}\n", syms=_CARRY_SYMS),
        path="<s>",
    )
    res = rewrite_program(
        tac.program, (NEG_S64_DOUBLE,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule.get("NegS64Double", 0) == 0


@pytest.mark.skipif(shutil.which("z3") is None, reason="z3 not on PATH")
@pytest.mark.parametrize("w", [64, 128])
def test_neg_s64_double_carry_lemma_via_z3(w):
    """Full-domain lemma for the carry composition: x1 in [0, 2^w),
    carry g in {0, 1} -- the doubled gadget with un-borrow equals the
    sign extension of z = (-y2) mod 2^w."""
    two_h = 1 << (w - 1)
    two_w = 1 << w
    two_256 = 1 << 256
    sign_ext = two_256 - two_w
    script = f"""(set-logic QF_NIA)
(declare-const x1 Int)
(declare-const g Int)
(assert (and (<= 0 x1) (< x1 {two_w})))
(assert (or (= g 0) (= g 1)))
(define-fun y1 () Int (mod x1 {two_w}))
(define-fun f1 () Int (ite (< y1 {two_h}) y1 (- y1 {two_w})))
(define-fun n1 () Int (ite (= y1 {two_h}) x1 (mod (- 0 f1) {two_256})))
(define-fun x2 () Int (mod (+ n1 g) {two_256}))
(define-fun y2 () Int (mod x2 {two_w}))
(define-fun f2 () Int (ite (< y2 {two_h}) y2 (- y2 {two_w})))
(define-fun r () Int (ite (= y2 {two_h}) x2 (mod (- 0 f2) {two_256})))
(define-fun z () Int (mod (- 0 y2) {two_w}))
(assert (not (= r (ite (<= z {two_h}) z (+ z {sign_ext})))))
(check-sat)
"""
    proc = subprocess.run(
        ["z3", "-smt2", "-T:20", "-in"],
        input=script, capture_output=True, text=True, timeout=40,
    )
    assert proc.stdout.strip() == "unsat", proc.stdout


# ---------------------------------------------------------------------------
# SIGN_EXT_SIGN_TEST / SIGN_EXT_CMP_LIFT
# ---------------------------------------------------------------------------

_SE_SYMS = _CARRY_SYMS + "\n\tTB:bool"
_FEE_BOUND = "0x67d1c49674ffe"  # floor(2^64 / 10100)


def _signext_consumer_tac(consumer: str):
    return parse_string(
        _wrap(
            f"\tBlock e Succ [] {{\n{_CARRY_BODY}{consumer}\t}}\n",
            syms=_SE_SYMS,
        ),
        path="<s>",
    )


def test_sign_ext_sign_test_after_double():
    """0 <s R over the carry-composed double: lifts to the chunk-band
    predicate Eq(Y2, 0) || Ge(Y2, 2^63)."""
    tac = _signext_consumer_tac("\t\tAssignExpCmd TB Sle(0x0 R)\n")
    res = rewrite_program(
        tac.program,
        (NEG_S64_DOUBLE, SIGN_EXT_SIGN_TEST),
        symbol_sorts=tac.symbol_sorts,
    )
    assert res.hits_by_rule.get("NegS64Double") == 1
    assert res.hits_by_rule.get("SignExtSignTest") == 1
    rhs = _rhs_of(res, "TB")
    assert isinstance(rhs, ApplyExpr) and rhs.op == "LOr"
    assert rhs.args[0].op == "Eq" and rhs.args[1].op == "Ge"


def test_sign_ext_cmp_lift_low_band():
    """Le(signext(z), c) with c = floor(2^64/10100) < 2^63: the fee
    no-overflow guard lifts to Le(z, c)."""
    tac = _signext_consumer_tac(
        f"\t\tAssignExpCmd TB Le(R {_FEE_BOUND})\n"
    )
    res = rewrite_program(
        tac.program,
        (NEG_S64_DOUBLE, SIGN_EXT_CMP_LIFT),
        symbol_sorts=tac.symbol_sorts,
    )
    assert res.hits_by_rule.get("SignExtCmpLift") == 1
    rhs = _rhs_of(res, "TB")
    # negchunk band form: Eq(Y2, 0) || Ge(Y2, 2^64 - c).
    assert isinstance(rhs, ApplyExpr) and rhs.op == "LOr"
    ge = rhs.args[1]
    assert isinstance(ge, ApplyExpr) and ge.op == "Ge"
    assert const_to_int(ge.args[1]) == 2**64 - 2**64 // 10100


def test_sign_ext_cmp_lift_mid_band():
    """c = 2^64 + 1 (> 2^63, below the negative band): the cap
    conjunct stays."""
    tac = _signext_consumer_tac(
        "\t\tAssignExpCmd TB Le(R 0x10000000000000001)\n"
    )
    res = rewrite_program(
        tac.program,
        (NEG_S64_DOUBLE, SIGN_EXT_CMP_LIFT),
        symbol_sorts=tac.symbol_sorts,
    )
    assert res.hits_by_rule.get("SignExtCmpLift") == 1
    rhs = _rhs_of(res, "TB")
    # Mid band over the negchunk form: Eq(Y2, 0) || Ge(Y2, 2^63).
    assert isinstance(rhs, ApplyExpr) and rhs.op == "LOr"
    assert const_to_int(rhs.args[1].args[1]) == 1 << 63


@pytest.mark.skipif(shutil.which("z3") is None, reason="z3 not on PATH")
@pytest.mark.parametrize("w", [64, 128])
def test_sign_ext_consumers_lemma_via_z3(w):
    """Both emit forms, all consumer bands: for z in [0, 2^w) the
    plain form's predicates over z, and for y in [0, 2^w) the
    negchunk form's band predicates over y."""
    two_h = 1 << (w - 1)
    two_w = 1 << w
    two_255 = 1 << 255
    sign_ext = (1 << 256) - two_w
    c_low = two_w // 10100
    c_mid = two_w + 1
    two_w_minus_c_low = two_w - c_low
    script = f"""(set-logic QF_NIA)
(declare-const z Int)
(declare-const y Int)
(assert (and (<= 0 z) (< z {two_w})))
(assert (and (<= 0 y) (< y {two_w})))
(define-fun v () Int (ite (<= z {two_h}) z (+ z {sign_ext})))
(define-fun w () Int
  (ite (= y 0) 0
    (ite (>= y {two_h}) (- {two_w} y) (+ (- {two_w} y) {sign_ext}))))
(assert (not (and
  (= (>= v {two_255}) (> z {two_h}))
  (= (<= v {c_low}) (<= z {c_low}))
  (= (<= v {c_mid}) (and (<= z {two_h}) (<= z {c_mid})))
  (= (>= v {c_mid}) (> z {two_h}))
  (= (>= w {two_255}) (and (< 0 y) (< y {two_h})))
  (= (<= w {c_low}) (or (= y 0) (>= y {two_w_minus_c_low})))
  (= (<= w {c_mid}) (or (= y 0) (>= y {two_h})))
  (= (= w 5) (= y {two_w - 5})))))
(check-sat)
"""
    proc = subprocess.run(
        ["z3", "-smt2", "-T:10", "-in"],
        input=script, capture_output=True, text=True, timeout=30,
    )
    assert proc.stdout.strip() == "unsat", proc.stdout


def test_neg_s64_sign_test_strictly_positive():
    """0 <s gadget (the strict orientation): positive iff y >= 2^63."""
    tac = _gadget_tac(
        "\t\tAssignExpCmd TB Slt(0x0 RZ)\n", body=_GADGET_BODY_BOUNDED
    )
    res = rewrite_program(
        tac.program, (NEG_S64_SIGN_TEST,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule.get("NegS64SignTest") == 1
    rhs = _rhs_of(res, "TB")
    assert isinstance(rhs, ApplyExpr) and rhs.op == "Ge"


# ---------------------------------------------------------------------------
# Width-128 instantiation (the gadget family is width-generic)
# ---------------------------------------------------------------------------

_H128 = f"0x{1 << 127:x}"
_F128 = f"0x{1 << 128:x}"

_GADGET_BODY_128 = (
    "\t\tAssignHavocCmd X\n"
    f"\t\tAssignExpCmd Y Mod(X {_F128})\n"
    f"\t\tAssignExpCmd TBC Lt(Y {_H128})\n"
    f"\t\tAssignExpCmd I IntMul(0x-1(int) Ite(TBC Y IntSub(Y {_F128}(int))))\n"
    f"\t\tAssignExpCmd TBG Eq(Y {_H128})\n"
    "\t\tAssignExpCmd RZ Ite(TBG X Apply(wrap_twos_complement_256:bif I))\n"
)

_GADGET_BODY_128_BOUNDED = _GADGET_BODY_128.replace(
    "\t\tAssignExpCmd Y", f"\t\tAssumeExpCmd Le(X {_F128})\n\t\tAssignExpCmd Y", 1
)


def test_neg_s128_zero_test_fires():
    """The block-236_1 family: the i128 negation's zero test collapses
    to Eq(Y, 0) exactly like the 64-bit instance."""
    tac = parse_string(
        _wrap(
            f"\tBlock e Succ [] {{\n{_GADGET_BODY_128}"
            "\t\tAssignExpCmd TB Eq(RZ 0x0)\n\t}\n",
            syms=_NEG_SYMS,
        ),
        path="<s>",
    )
    res = rewrite_program(
        tac.program, (NEG_S64_ZERO_TEST,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule.get("NegS64ZeroTest") == 1
    assert _rhs_of(res, "TB") == ApplyExpr(
        "Eq", (SymbolRef("Y"), ConstExpr("0x0"))
    )


def test_neg_s128_low_chunk_fires():
    """Mod(gadget128, 2^128) -> Ite(Eq(Y, 0), 0, Sub(2^128, Y))."""
    tac = parse_string(
        _wrap(
            f"\tBlock e Succ [] {{\n{_GADGET_BODY_128}"
            f"\t\tAssignExpCmd R2 Mod(RZ {_F128})\n\t}}\n",
            syms=_NEG_SYMS + "\n\tR2:bv256",
        ),
        path="<s>",
    )
    res = rewrite_program(
        tac.program, (NEG_S64_LOW_CHUNK,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule.get("NegS64LowChunk") == 1
    rhs = _rhs_of(res, "R2")
    assert isinstance(rhs, ApplyExpr) and rhs.op == "Ite"
    sub = rhs.args[2]
    assert isinstance(sub, ApplyExpr) and sub.op == "Sub"
    assert const_to_int(sub.args[0]) == 1 << 128


def test_neg_s128_cross_width_chunk_no_fire():
    """Mod(gadget128, 2^64) reads the LOW LIMB of the 128-bit value --
    not the same-width chunk identity. The rule must abstain (limb
    fusion is a separate, future composition)."""
    tac = parse_string(
        _wrap(
            f"\tBlock e Succ [] {{\n{_GADGET_BODY_128}"
            "\t\tAssignExpCmd R2 Mod(RZ 0x10000000000000000)\n\t}\n",
            syms=_NEG_SYMS + "\n\tR2:bv256",
        ),
        path="<s>",
    )
    res = rewrite_program(
        tac.program, (NEG_S64_LOW_CHUNK,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule.get("NegS64LowChunk", 0) == 0


def test_neg_s128_cross_width_gadget_no_fire():
    """A 2^127 edge guard over a from_s64 body is not a gadget at
    either width: the width consistency check must reject it."""
    body = (
        "\t\tAssignHavocCmd X\n"
        f"\t\tAssignExpCmd Y Mod(X {_F128})\n"
        "\t\tAssignExpCmd TBC Lt(Y 0x8000000000000000)\n"
        "\t\tAssignExpCmd I IntMul(0x-1(int) Ite(TBC Y IntSub(Y 0x10000000000000000(int))))\n"
        f"\t\tAssignExpCmd TBG Eq(Y {_H128})\n"
        "\t\tAssignExpCmd RZ Ite(TBG X Apply(wrap_twos_complement_256:bif I))\n"
    )
    tac = parse_string(
        _wrap(
            f"\tBlock e Succ [] {{\n{body}"
            "\t\tAssignExpCmd TB Eq(RZ 0x0)\n\t}\n",
            syms=_NEG_SYMS,
        ),
        path="<s>",
    )
    res = rewrite_program(
        tac.program, (NEG_S64_ZERO_TEST,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule.get("NegS64ZeroTest", 0) == 0


def test_neg_s128_sign_test_fires():
    """Slt(gadget128, 0) -> 0 < Y && Y < 2^127, same 2^255 gate on
    the pass-through arm."""
    tac = parse_string(
        _wrap(
            f"\tBlock e Succ [] {{\n{_GADGET_BODY_128_BOUNDED}"
            "\t\tAssignExpCmd TB Slt(RZ 0x0)\n\t}\n",
            syms=_NEG_SYMS,
        ),
        path="<s>",
    )
    res = rewrite_program(
        tac.program, (NEG_S64_SIGN_TEST,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule.get("NegS64SignTest") == 1
    rhs = _rhs_of(res, "TB")
    assert isinstance(rhs, ApplyExpr) and rhs.op == "LAnd"
    assert const_to_int(rhs.args[1].args[1]) == 1 << 127


_DOUBLE_BODY_128 = (
    "\t\tAssignHavocCmd X\n"
    f"\t\tAssignExpCmd Y Mod(X {_F128})\n"
    f"\t\tAssignExpCmd TBC Lt(Y {_H128})\n"
    f"\t\tAssignExpCmd I IntMul(0x-1(int) Ite(TBC Y IntSub(Y {_F128}(int))))\n"
    f"\t\tAssignExpCmd TBG Eq(Y {_H128})\n"
    "\t\tAssignExpCmd RZ Ite(TBG Y Apply(wrap_twos_complement_256:bif I))\n"
    f"\t\tAssignExpCmd Y2 Mod(RZ {_F128})\n"
    f"\t\tAssignExpCmd TBC2 Lt(Y2 {_H128})\n"
    f"\t\tAssignExpCmd I2 IntMul(0x-1(int) Ite(TBC2 Y2 IntSub(Y2 {_F128}(int))))\n"
    f"\t\tAssignExpCmd TBG2 Eq(Y2 {_H128})\n"
    "\t\tAssignExpCmd R2 Ite(TBG2 RZ Apply(wrap_twos_complement_256:bif I2))\n"
)


def test_neg_s128_double_fires():
    """Gadget-of-gadget at 128 collapses to the 128->256 sign
    extension Ite with offset 2^256 - 2^128."""
    tac = parse_string(
        _wrap(
            f"\tBlock e Succ [] {{\n{_DOUBLE_BODY_128}\t}}\n",
            syms=_DOUBLE_SYMS,
        ),
        path="<s>",
    )
    res = rewrite_program(
        tac.program, (NEG_S64_DOUBLE,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule.get("NegS64Double") == 1
    rhs = _rhs_of(res, "R2")
    assert isinstance(rhs, ApplyExpr) and rhs.op == "Ite"
    cond, ident, ext = rhs.args
    assert const_to_int(cond.args[1]) == 1 << 127
    assert ident == SymbolRef("Y")
    assert isinstance(ext, ApplyExpr) and ext.op == "Add"
    assert const_to_int(ext.args[1]) == (1 << 256) - (1 << 128)


def test_sign_ext_consumers_128():
    """The sign-ext consumers track the 128 width: sign test bands at
    2^127, low-band cmp lifts to the bare predicate on the chunk."""
    base = _wrap(
        f"\tBlock e Succ [] {{\n{_DOUBLE_BODY_128}"
        "\t\tAssignExpCmd TB Slt(R2 0x0)\n\t}\n",
        syms=_DOUBLE_SYMS + "\n\tTB:bool",
    )
    tac = parse_string(base, path="<s>")
    res = rewrite_program(
        tac.program,
        (NEG_S64_DOUBLE, SIGN_EXT_SIGN_TEST),
        symbol_sorts=tac.symbol_sorts,
    )
    assert res.hits_by_rule.get("SignExtSignTest") == 1
    rhs = _rhs_of(res, "TB")
    assert isinstance(rhs, ApplyExpr) and rhs.op == "Gt"
    assert const_to_int(rhs.args[1]) == 1 << 127

    tac = parse_string(base.replace("Slt(R2 0x0)", "Le(R2 0xa)"), path="<s>")
    res = rewrite_program(
        tac.program,
        (NEG_S64_DOUBLE, SIGN_EXT_CMP_LIFT),
        symbol_sorts=tac.symbol_sorts,
    )
    assert res.hits_by_rule.get("SignExtCmpLift") == 1
    rhs = _rhs_of(res, "TB")
    assert rhs == ApplyExpr("Le", (SymbolRef("Y"), ConstExpr("0xa")))
