"""Soundness spec for ADD_BV_MAX_TO_ITE.

The rule (``src/ctac/rewrite/rules/bv_to_int.py``, ``_rewrite_add_bv_max_to_ite``)
rewrites ``Add(BV256_MAX, X)`` unconditionally to
``Ite(X >= 1, IntSub(X, 1), BV256_MAX)`` for any bv256-valued ``X``.

Soundness claim: for all ``X in [0, 2^256)``,

    (BV256_MAX + X) mod 2^256  ==  if X >= 1 then X - 1 else BV256_MAX

- When ``X = 0``: the unwrapped sum is ``BV256_MAX``, no wrap; result
  is ``BV256_MAX``. The else branch matches.
- When ``X >= 1``: the unwrapped sum is in ``[2^256, 2*2^256 - 1]``,
  so it wraps once, giving ``X - 1``. The then branch matches.

Boundary / swap bugs this spec catches:

- Swapping then/else branches (else-branch ``X - 1`` instead of
  ``BV256_MAX``).
- Off-by-one on the condition (``X >= 0`` or ``X > 1``).
- Getting the decrement wrong (``X + 1`` instead of ``X - 1``, or
  ``BV256_MAX + 1`` as the else branch).
"""

from __future__ import annotations

from ctac.rewrite.validation import ValidationCase, emit_flat_script

# 2^256 inlined as a literal — `(^ 2 256)` isn't in QF_NIA, and z3's
# extension parser accepts it but warns. The literal is unambiguous
# and solver-portable.
_BV256_MOD_LITERAL = (
    "115792089237316195423570985008687907853269984665640564039457584007913129639936"
)

_PRECONDITIONS: tuple[str, ...] = (
    f"(= BV256_MOD {_BV256_MOD_LITERAL})",   # anchor the modulus (2^256)
    "(= BV256_MAX (- BV256_MOD 1))",         # and the "-1" constant
    "(>= X 0)",                               # X in bv256 range: lo
    "(< X BV256_MOD)",                        # X in bv256 range: hi
)


def _case() -> ValidationCase:
    smt2 = emit_flat_script(
        logic="QF_NIA",
        decls=(
            ("BV256_MOD", "Int"),
            ("BV256_MAX", "Int"),
            ("X", "Int"),
            ("LHS", "Int"),
            ("RHS", "Int"),
        ),
        preconditions=_PRECONDITIONS,
        definitions=(
            # LHS: the original bv256 expression's value.
            ("LHS", "(mod (+ BV256_MAX X) BV256_MOD)"),
            # RHS: the rewrite's Ite shape.
            ("RHS", "(ite (>= X 1) (- X 1) BV256_MAX)"),
        ),
        goal_not_eq=("LHS", "RHS"),
        comments=(
            "ADD_BV_MAX_TO_ITE: Add(BV256_MAX, X) -> Ite(X>=1, X-1, BV256_MAX)",
            "Claim: for all X in [0, 2^256), the two sides are equal.",
            "Expect: unsat.",
        ),
    )
    return ValidationCase(
        name="ADD_BV_MAX_TO_ITE",
        case="",
        description=(
            "(BV256_MAX + X) mod 2^256 == if X >= 1 then X - 1 else BV256_MAX"
        ),
        smt2_text=smt2,
    )


ADD_BV_MAX_TO_ITE_CASES: tuple[ValidationCase, ...] = (_case(),)
