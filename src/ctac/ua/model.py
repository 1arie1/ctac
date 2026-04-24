"""Result dataclasses for the uniquify-asserts transforms."""

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


@dataclass(frozen=True)
class SplitAssertOutput:
    """One per-assertion output of :func:`ctac.ua.split_asserts`.

    Each output corresponds to a single live assertion; all other
    assertions in the program are converted to ``AssumeExpCmd`` with
    the same predicate.

    - ``index``: 0-based position in program-order assert traversal.
    - ``block_id`` / ``cmd_index``: location of the live assert in
      the OUTPUT program (same as in the input since split doesn't
      relocate commands, but the containing program may be pruned
      by the COI step).
    - ``message``: the original ``AssertCmd.message`` verbatim.
    - ``program``: the resulting :class:`TacProgram`, already
      cone-of-influence-pruned to the live assert.
    """

    index: int
    block_id: str
    cmd_index: int
    message: str | None
    program: TacProgram


@dataclass(frozen=True)
class SplitAssertsResult:
    """Outcome of a single run of :func:`ctac.ua.split_asserts` or
    :func:`ctac.ua.uniquify_asserts_split`.

    ``was_noop`` is True iff the input had zero asserts. With a single
    assert the result has one output (the program unchanged except for
    the COI prune). ``removed_true_asserts`` and ``extra_symbols`` are
    only populated by the convenience entry point.
    """

    outputs: tuple[SplitAssertOutput, ...]
    asserts_before: int
    was_noop: bool = False
    removed_true_asserts: int = 0
    extra_symbols: tuple[tuple[str, str], ...] = ()
