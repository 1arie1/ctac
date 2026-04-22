"""Soundness spec for R4A (div purification).

The rule (src/ctac/rewrite/rules/div_purify.py, ``_rewrite_r4a``)
replaces ``X = Div(A, B)`` with ``havoc X; assume B*X <= A; assume A <
B*(X+1)`` when ``B`` has a positive lower bound. When ``A`` is also
known non-negative, R4A adds ``assume X >= 0``.

Soundness claim: the emitted Euclidean bounds uniquely pin the havoc'd
``NX`` to the original Euclidean quotient ``A div B``. One case for the
base rewrite and one for the ``A >= 0``-refined rewrite; both should
return ``unsat`` when run through z3.
"""

from __future__ import annotations

from ctac.rewrite.validation import ValidationCase, emit_flat_script

_BASE_PRECONDITIONS: tuple[str, ...] = (
    "(> B 0)",                       # R4A gate: B has positive lower bound
    "(<= (* B NX) A)",               # emitted assume #1
    "(< A (* B (+ NX 1)))",          # emitted assume #2
)

_SIGNED_PRECONDITIONS: tuple[str, ...] = _BASE_PRECONDITIONS + (
    "(>= A 0)",                       # known from the surrounding range facts
    "(>= NX 0)",                      # emitted assume #3 (only when A >= 0)
)


def _case(case: str, description: str, preconditions: tuple[str, ...]) -> ValidationCase:
    smt2 = emit_flat_script(
        logic="QF_NIA",
        decls=(("A", "Int"), ("B", "Int"), ("X", "Int"), ("NX", "Int")),
        preconditions=preconditions,
        definitions=(
            # ``X`` is the original program's value of the LHS —
            # the Euclidean quotient computed by SMT-LIB's ``div``.
            ("X", "(div A B)"),
        ),
        goal_not_eq=("X", "NX"),
        comments=(
            f"R4a ({case}): {description}",
            "After the rewrite, NX is havoc'd and constrained by the bounds",
            "above. Soundness requires those bounds to force NX = A div B.",
            "Expect: unsat.",
        ),
    )
    return ValidationCase(
        name="R4a",
        case=case,
        description=description,
        smt2_text=smt2,
    )


R4A_CASES: tuple[ValidationCase, ...] = (
    _case(
        "",
        "B*NX <= A < B*(NX+1) with B > 0 forces NX = A div B",
        _BASE_PRECONDITIONS,
    ),
    _case(
        "signed",
        "... plus A>=0 and NX>=0 (the extra assume R4A emits in that case)",
        _SIGNED_PRECONDITIONS,
    ),
)
