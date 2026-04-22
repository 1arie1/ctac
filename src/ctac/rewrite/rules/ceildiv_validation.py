"""Soundness spec for R6 (ceildiv chain collapse).

The rule (src/ctac/rewrite/rules/ceildiv.py, ``_rewrite_r6``) recognizes
Solana's 256-bit ceiling-division idiom and replaces the entire chain
with a single havoc ``T`` constrained by:

  assume B*T >= A
  assume B*T < A+B
  assume T >= 0        ; only when A is known non-negative

Soundness claim: those bounds uniquely pin ``NT = ceil(A/B) =
(A + B - 1) div B`` in the gated domain (``B > 0``, and ``A >= 0`` for
the signed case). One case per gate shape; z3 should return ``unsat``
on each.
"""

from __future__ import annotations

from ctac.rewrite.validation import ValidationCase, emit_flat_script

_BASE_PRECONDITIONS: tuple[str, ...] = (
    "(> B 0)",                       # R6 gate: denominator has positive range
    "(>= (* B NT) A)",               # emitted assume #1
    "(< (* B NT) (+ A B))",          # emitted assume #2
)

_SIGNED_PRECONDITIONS: tuple[str, ...] = _BASE_PRECONDITIONS + (
    "(>= A 0)",                       # R6's num_non_negative gate
    "(>= NT 0)",                      # emitted assume #3 (only when A >= 0)
)


def _case(case: str, description: str, preconditions: tuple[str, ...]) -> ValidationCase:
    smt2 = emit_flat_script(
        logic="QF_NIA",
        decls=(("A", "Int"), ("B", "Int"), ("T", "Int"), ("NT", "Int")),
        preconditions=preconditions,
        definitions=(
            # ``T`` is the original program's value — ceil(A/B) computed
            # via the standard Euclidean identity.
            ("T", "(div (+ A (- B 1)) B)"),
        ),
        goal_not_eq=("T", "NT"),
        comments=(
            f"R6 ({case}): {description}",
            "After the rewrite, NT is havoc'd and constrained by the bounds",
            "above. Soundness requires those bounds to force NT = ceil(A/B).",
            "Expect: unsat.",
        ),
    )
    return ValidationCase(
        name="R6",
        case=case,
        description=description,
        smt2_text=smt2,
    )


R6_CASES: tuple[ValidationCase, ...] = (
    _case(
        "",
        "B*NT >= A and B*NT < A+B with B > 0 forces NT = ceil(A/B)",
        _BASE_PRECONDITIONS,
    ),
    _case(
        "signed",
        "... plus A>=0 and NT>=0 (the extra assume R6 emits in that case)",
        _SIGNED_PRECONDITIONS,
    ),
)
