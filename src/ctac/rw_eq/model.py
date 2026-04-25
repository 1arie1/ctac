"""Result dataclasses for the rewriter equivalence checker."""

from __future__ import annotations

from dataclasses import dataclass

from ctac.ir.models import TacProgram


@dataclass(frozen=True)
class RehavocSite:
    """One occurrence of rule 6 (rehavoc) firing.

    ``block_id`` and ``cmd_index`` point at the LHS's ``X = e``
    command position; ``var_name`` is X (the rehavoc'd LHS symbol);
    ``shadow_name`` is the fresh ``X_new`` we minted.
    """

    block_id: str
    cmd_index: int
    var_name: str
    shadow_name: str


@dataclass(frozen=True)
class EquivResult:
    """Outcome of :func:`emit_equivalence_program`.

    ``program`` is the merged TAC program. ``rule_hits`` counts each
    rule's firings. ``rehavoc_sites`` lists every rule-6 admission for
    the loud-warning report. ``extra_symbols`` lists all symbols added
    to the merged program's symbol table (CHK<n> bools and X_new
    shadows).
    """

    program: TacProgram
    rule_hits: dict[str, int]
    rehavoc_sites: tuple[RehavocSite, ...] = ()
    extra_symbols: tuple[tuple[str, str], ...] = ()
    asserts_emitted: int = 0
    feasibility_asserts_emitted: int = 0


class EquivContractError(ValueError):
    """Raised when the (orig, rw) pair violates the rw-eq input contract:
    different block ids, different successors, terminator mismatch, or
    a lockstep step that none of the matching rules accepts."""
