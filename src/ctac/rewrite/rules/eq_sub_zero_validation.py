"""Soundness spec for EQ_SUB_ZERO (``src/ctac/rewrite/rules/ite.py``).

``Eq(Sub(a, b), 0) -> Eq(a, b)``, for both ``IntSub`` (linear over
Int) and the wrapping bv256 ``Sub`` (``(a - b) mod 2^256 == 0`` iff
``a ≡ b (mod 2^256)``, an equality on bv256-domain operands). Two
cases: the Int form (unbounded) and the bv form (operands in
``[0, 2^256)``).
"""

from __future__ import annotations

from ctac.rewrite.validation import ValidationCase, emit_flat_script


def _int_case() -> ValidationCase:
    smt2 = emit_flat_script(
        logic="QF_NIA",
        decls=(("a", "Int"), ("b", "Int"), ("LHS", "Bool"), ("RHS", "Bool")),
        preconditions=(),
        definitions=(("LHS", "(= (- a b) 0)"), ("RHS", "(= a b)")),
        goal_not_eq=("LHS", "RHS"),
        comments=(
            "EqSubZero (IntSub): Eq(IntSub(a, b), 0) == Eq(a, b).",
            "Int domain, unbounded. Expect: unsat.",
        ),
    )
    return ValidationCase(
        name="EqSubZero", case="int",
        description="Eq(IntSub(a, b), 0) == Eq(a, b) over Int.",
        smt2_text=smt2,
    )


def _bv_case() -> ValidationCase:
    m = 1 << 256
    smt2 = emit_flat_script(
        logic="QF_NIA",
        decls=(("a", "Int"), ("b", "Int"), ("LHS", "Bool"), ("RHS", "Bool")),
        preconditions=(
            f"(and (<= 0 a) (< a {m}))",
            f"(and (<= 0 b) (< b {m}))",
        ),
        definitions=(
            ("LHS", f"(= (mod (- a b) {m}) 0)"),
            ("RHS", "(= a b)"),
        ),
        goal_not_eq=("LHS", "RHS"),
        comments=(
            "EqSubZero (bv256 Sub): Eq((a - b) mod 2^256, 0) == Eq(a, b)",
            "for a, b in [0, 2^256) (the wrap bijection). Expect: unsat.",
        ),
    )
    return ValidationCase(
        name="EqSubZero", case="bv",
        description="Eq((a-b) mod 2^256, 0) == Eq(a, b) on bv256 operands.",
        smt2_text=smt2,
    )


EQ_SUB_ZERO_CASES: tuple[ValidationCase, ...] = (_int_case(), _bv_case())
