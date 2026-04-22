"""Soundness specs for R4 (eliminate Div from comparisons).

The rule (src/ctac/rewrite/rules/div.py, ``_rewrite_r4``) fires on a
comparison ``<op>(Div(A, B), C)`` where ``B`` is a positive-integer
constant, rewriting to a ``B*C``/``B*(C+1)``-scaled comparison. One
:class:`ValidationCase` per operator variant encodes the corresponding
Euclidean-division identity as a negated equality; z3 should return
``unsat`` on each.

Preconditions kept to the rule's gate (``B > 0``). A symbolic ``B`` is
fine even though the rule only fires on a constant — the identity
holds for any positive integer ``B``, so covering the symbolic case
covers every concrete instantiation the rule ever produces.
"""

from __future__ import annotations

from ctac.rewrite.validation import ValidationCase, emit_flat_script

_DECLS: tuple[tuple[str, str], ...] = (
    ("A", "Int"),
    ("B", "Int"),
    ("C", "Int"),
    ("Y", "Bool"),
    ("NY", "Bool"),
)

_PRECONDITIONS: tuple[str, ...] = ("(> B 0)",)


def _case(case: str, description: str, before: str, after: str) -> ValidationCase:
    smt2 = emit_flat_script(
        logic="QF_NIA",
        decls=_DECLS,
        preconditions=_PRECONDITIONS,
        definitions=(("Y", before), ("NY", after)),
        goal_not_eq=("Y", "NY"),
        comments=(
            f"R4 ({case}): {description}",
            "Gate: B is a positive-integer constant (symbolic B here — the",
            "identity holds for any positive integer B, which covers every",
            "concrete instantiation the rule produces).",
            "Expect: unsat.",
        ),
    )
    return ValidationCase(
        name="R4",
        case=case,
        description=description,
        smt2_text=smt2,
    )


R4_CASES: tuple[ValidationCase, ...] = (
    _case(
        "Lt",
        "Lt(Div(A,B), C) <-> Lt(A, B*C)  when B > 0",
        before="(< (div A B) C)",
        after="(< A (* B C))",
    ),
    _case(
        "Le",
        "Le(Div(A,B), C) <-> Lt(A, B*(C+1))  when B > 0",
        before="(<= (div A B) C)",
        after="(< A (* B (+ C 1)))",
    ),
    _case(
        "Gt",
        "Gt(Div(A,B), C) <-> Ge(A, B*(C+1))  when B > 0",
        before="(> (div A B) C)",
        after="(>= A (* B (+ C 1)))",
    ),
    _case(
        "Ge",
        "Ge(Div(A,B), C) <-> Ge(A, B*C)  when B > 0",
        before="(>= (div A B) C)",
        after="(>= A (* B C))",
    ),
    _case(
        "Eq",
        "Eq(Div(A,B), C) <-> (B*C <= A < B*(C+1))  when B > 0",
        before="(= (div A B) C)",
        after="(and (>= A (* B C)) (< A (* B (+ C 1))))",
    ),
)
