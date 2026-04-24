"""Result dataclass for split_critical_edges."""

from __future__ import annotations

from dataclasses import dataclass

from ctac.ir.models import TacProgram


@dataclass(frozen=True)
class SplitCritResult:
    """Outcome of one :func:`ctac.splitcrit.split_critical_edges` run.

    ``was_noop`` is True iff the input had no critical edges, in which
    case ``program`` is the input unchanged and ``shims_added == 0``.
    ``edges_split`` lists the original ``(source, target)`` pairs that
    were broken by a shim, in discovery order.
    """

    program: TacProgram
    shims_added: int
    edges_split: tuple[tuple[str, str], ...] = ()
    was_noop: bool = False
