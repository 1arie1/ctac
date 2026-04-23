"""Canonical TAC operator and command names.

Single source of truth for the operator / command-class identifiers the
Certora TAC dump uses. Consumed by ``ctac search``'s pattern
tab-completion — an agent typing ``ctac search f.tac <TAB>`` should see
exactly the tokens that will match something real.

When adding a new operator to the pipeline, add it here too so it's
discoverable.
"""

from __future__ import annotations

# Expression ops — i.e. the ``op`` field of :class:`ApplyExpr`.
# Organized by role for readability; order within a group is alphabetic
# where that doesn't conflict with semantic pairing.
EXPRESSION_OPS: tuple[str, ...] = (
    # Arithmetic — bv256 (modular) form.
    "Add",
    "Sub",
    "Mul",
    "Div",
    "Mod",
    # Arithmetic — Int (mathematical) form, produced by the rewriter
    # and by the Certora pipeline for DSA-safe unbounded arithmetic.
    "IntAdd",
    "IntSub",
    "IntMul",
    "IntDiv",
    "IntMod",
    # Bitwise / shift.
    "BWAnd",
    "BWOr",
    "BWXOr",
    "BNot",
    "ShiftLeft",
    "ShiftRightLogical",
    "ShiftRightArithmetical",
    # Unsigned comparisons.
    "Eq",
    "Ne",
    "Lt",
    "Le",
    "Gt",
    "Ge",
    # Signed comparisons.
    "Slt",
    "Sle",
    "Sgt",
    "Sge",
    # Boolean.
    "LAnd",
    "LOr",
    "LNot",
    # Selection.
    "Ite",
    # Memory (bytemap / ghostmap).
    "Select",
    "Store",
    # Function application (function symbol is ``args[0]``).
    "Apply",
)

# Command classes — the Python class names that appear in ``raw`` TAC
# dumps (e.g. ``AssignExpCmd R1 BWAnd(R0 0xff)``).
COMMAND_KINDS: tuple[str, ...] = (
    "AnnotationCmd",
    "AssertCmd",
    "AssignExpCmd",
    "AssignHavocCmd",
    "AssumeExpCmd",
    "JumpCmd",
    "JumpiCmd",
    "LabelCmd",
)

# Well-known built-in-function symbols that show up as the callee of
# ``Apply(...)``. Frequent enough in searches to deserve completion.
BUILTIN_FUNCTION_SYMBOLS: tuple[str, ...] = (
    "safe_math_narrow_bv256:bif",
)

# Lowercase keywords that appear in humanized (`ctac pp`) output.
# Useful completion targets when searching without ``--plain`` (which
# keeps the human printer active).
HUMAN_KEYWORDS: tuple[str, ...] = (
    "assert",
    "assume",
    "else",
    "false",
    "goto",
    "havoc",
    "if",
    "stop",
    "true",
)


def all_search_tokens() -> tuple[str, ...]:
    """Flat list of every token surfaced in ``ctac search`` completion.

    Order: expression ops → command kinds → builtin-function symbols →
    humanized keywords. This ordering is intentional — agents typing a
    prefix get the operator matches first.
    """
    return (
        EXPRESSION_OPS
        + COMMAND_KINDS
        + BUILTIN_FUNCTION_SYMBOLS
        + HUMAN_KEYWORDS
    )
