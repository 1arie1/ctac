"""Rewriter equivalence checker — `ctac rw-eq`.

Exports:

    :func:`emit_equivalence_program` — lockstep walker producing one
        merged TAC program with ``assert`` commands at every site
        where the two inputs disagree.
    :class:`EquivResult` — outcome (program, rule hits, rehavoc sites).
    :class:`RehavocSite` — single rule-6 occurrence.
    :class:`EquivContractError` — raised on input-contract violation.
"""

from ctac.rw_eq.model import EquivContractError, EquivResult, RehavocSite
from ctac.rw_eq.transform import emit_equivalence_program

__all__ = [
    "EquivContractError",
    "EquivResult",
    "RehavocSite",
    "emit_equivalence_program",
]
