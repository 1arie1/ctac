"""Soundness-spec scaffolding for rewrite rules.

Each rule that opts in contributes one or more :class:`ValidationCase`
instances that encode the rule's soundness claim as a self-contained
SMT-LIB script. Running z3 (or any SMT-LIB 2 compatible solver) on each
script and expecting ``unsat`` is the validation check — ``sat`` means
the rule is wrong; ``unknown`` means "escalate" (custom tactics, Lean).

The spec is **trusted**: it's a human-written statement of what the
rule claims to do, placed next to the rule for easy side-by-side
review. We do not attempt to auto-check that the spec matches the code.

See :func:`emit_flat_script` for the canonical output shape.
"""

from __future__ import annotations

from collections.abc import Iterable
from dataclasses import dataclass


@dataclass(frozen=True)
class ValidationCase:
    """A single soundness claim for (some case of) a rewrite rule.

    ``name`` is the rule name (e.g., ``"R4"``) and ``case`` distinguishes
    variants (e.g., ``"Lt"``, ``"signed"``, empty for single-case rules).
    ``file_stem`` is used for the output ``<stem>.smt2`` filename.
    """

    name: str
    case: str
    description: str
    smt2_text: str
    expected: str = "unsat"

    @property
    def file_stem(self) -> str:
        return self.name if not self.case else f"{self.name}_{self.case}"


def emit_flat_script(
    *,
    logic: str,
    decls: Iterable[tuple[str, str]],
    preconditions: Iterable[str],
    definitions: Iterable[tuple[str, str]],
    goal_not_eq: tuple[str, str],
    comments: Iterable[str] = (),
) -> str:
    """Build the canonical flat-assert SMT-LIB envelope.

    - ``decls``: ``(name, sort)`` pairs rendered as ``(declare-const ...)``.
    - ``preconditions``: SMT-LIB Bool expressions, each wrapped in one
      ``(assert ...)``.
    - ``definitions``: ``(name, rhs_sexpr)`` pairs rendered as
      ``(assert (= <name> <rhs>))`` — binds before/after sides of the
      claim to named constants.
    - ``goal_not_eq``: ``(lhs, rhs)`` rendered as
      ``(assert (not (= lhs rhs)))``. ``unsat`` on the whole script
      means the two sides coincide under the preconditions.
    - ``comments``: free-form header lines (prefixed with ``;``).
    """
    lines: list[str] = []
    for c in comments:
        for sub in c.splitlines() or [""]:
            lines.append(f"; {sub}" if sub else ";")
    if comments:
        lines.append("")
    lines.append(f"(set-logic {logic})")
    lines.append("")
    for name, sort in decls:
        lines.append(f"(declare-const {name} {sort})")
    lines.append("")
    if preconditions:
        lines.append("; preconditions (the rule's gate)")
        for pre in preconditions:
            lines.append(f"(assert {pre})")
        lines.append("")
    if definitions:
        lines.append("; before- and after-rewrite sides")
        for name, rhs in definitions:
            lines.append(f"(assert (= {name} {rhs}))")
        lines.append("")
    lhs, rhs = goal_not_eq
    lines.append("; soundness: no model should make the two sides differ")
    lines.append(f"(assert (not (= {lhs} {rhs})))")
    lines.append("(check-sat)")
    return "\n".join(lines) + "\n"
