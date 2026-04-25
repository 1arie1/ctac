"""Soundness spec for R1_BITFIELD_STRIP.

The rule (``src/ctac/rewrite/rules/div.py``, ``_rewrite_r1``) rewrites

    Mul(Mod(Div(X, 2^k), 2^n), 2^k)  ->  X

under two preconditions:

1. **High bits**: ``X < 2^(k+n)`` (range gate).
2. **Low bits**: ``X mod 2^k == 0`` (structural divisibility — checked
   via ``_x_divisible_by_2k``, looking through static defs and narrow
   wrappers).

The wrapper expression keeps bits ``[k, k+n-1]`` of X and zeros all
other bits. For the result to equal X, both halves of the bit-window
condition must hold; the original gate only checked the high half,
which made the rule unsound (e.g. X=1 with k=n=4 satisfies the high
bound but not the low one, and the wrapper evaluates to 0, not 1).

This spec pins the corrected claim. Specialised to k=4, n=4 — the
smallest non-trivial instance — but the algebraic argument is the
same for any (k, n) with k, n >= 1.
"""

from __future__ import annotations

from ctac.rewrite.validation import ValidationCase, emit_flat_script


_PRECONDITIONS: tuple[str, ...] = (
    "(>= X 0)",                      # X non-negative
    "(< X 256)",                     # X < 2^(k+n) for k=n=4
    "(= (mod X 16) 0)",              # X mod 2^k == 0  (the new gate)
)


def _case() -> ValidationCase:
    smt2 = emit_flat_script(
        logic="QF_NIA",
        decls=(
            ("X", "Int"),
            ("LHS", "Int"),
            ("RHS", "Int"),
        ),
        preconditions=_PRECONDITIONS,
        definitions=(
            # LHS: the wrapper expression (extract bit-field [k, k+n-1]).
            ("LHS", "(* (mod (div X 16) 16) 16)"),
            # RHS: what the rule rewrites to.
            ("RHS", "X"),
        ),
        goal_not_eq=("LHS", "RHS"),
        comments=(
            "R1 (k=4, n=4): Mul(Mod(Div(X, 2^k), 2^n), 2^k) == X",
            "  when X < 2^(k+n) AND X mod 2^k == 0.",
            "Without the divisibility gate, X=1 is a counterexample.",
            "Expect: unsat.",
        ),
    )
    return ValidationCase(
        name="R1",
        case="",
        description=(
            "Mul(Mod(Div(X, 2^k), 2^n), 2^k) == X when X < 2^(k+n) "
            "and X is divisible by 2^k. Specialised to k=n=4."
        ),
        smt2_text=smt2,
    )


R1_CASES: tuple[ValidationCase, ...] = (_case(),)
