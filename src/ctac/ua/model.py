"""Result dataclass for the uniquify-asserts transforms."""

from __future__ import annotations

from dataclasses import dataclass

from ctac.ir.models import TacProgram


@dataclass(frozen=True)
class UnifyAssertsResult:
    """Outcome of a single run of :func:`ctac.ua.merge_asserts` or
    :func:`ctac.ua.uniquify_asserts`.

    ``was_noop`` is True iff the strategy had at most one
    :class:`AssertCmd` to redirect, in which case ``program`` is returned
    unchanged and no ``__UA_ERROR`` block is synthesized
    (``error_block_id`` is empty). ``removed_true_asserts`` and
    ``extra_symbols`` are only populated by :func:`uniquify_asserts`; the
    library-level :func:`merge_asserts` leaves them empty.
    """

    program: TacProgram
    asserts_merged: int
    error_block_id: str = ""
    was_noop: bool = False
    removed_true_asserts: int = 0
    extra_symbols: tuple[tuple[str, str], ...] = ()
