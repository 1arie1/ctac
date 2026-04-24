"""Split critical edges in a TAC CFG.

Exports:

    :class:`SplitCritResult` — per-run outcome (program, counts, edges).
    :func:`split_critical_edges` — transform that inserts a single-command
        shim block on each critical edge. Idempotent: a program with no
        critical edges is returned unchanged (``was_noop=True``).
"""

from ctac.splitcrit.model import SplitCritResult
from ctac.splitcrit.split import split_critical_edges

__all__ = [
    "SplitCritResult",
    "split_critical_edges",
]
