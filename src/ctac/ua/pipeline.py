"""``uniquify_asserts``: pre-passes + strategy, in one entry point.

Two strategies live here:

- ``merge`` (default) — fold every ``AssertCmd`` into a single
  ``__UA_ERROR`` block. Returns :class:`UnifyAssertsResult` with a
  single program.
- ``split`` — emit one program per assertion with all other asserts
  converted to ``AssumeExpCmd``. Returns :class:`SplitAssertsResult`
  with a tuple of outputs.

The two strategies have genuinely different return shapes, so they
have two entry points: :func:`uniquify_asserts` for merge (preserves
the original API), :func:`uniquify_asserts_split` for split.

Both entry points run the same pre-passes:

1. ``remove_true_asserts`` — drop every ``assert true`` from the program.
2. PURIFY_ASSERT via the rewrite framework — ensure every surviving
   assertion's predicate is a :class:`SymbolRef` (or a :class:`ConstExpr`
   literal that the strategy handles specially).
3. Apply the chosen strategy.

API callers get a turnkey version; CLI callers use the individual steps
directly so they can surface intermediate stats and warnings.
"""

from __future__ import annotations

from ctac.analysis import remove_true_asserts
from ctac.ir.models import TacProgram
from ctac.rewrite import rewrite_program
from ctac.rewrite.rules import PURIFY_ASSERT
from ctac.ua.merge import merge_asserts
from ctac.ua.model import SplitAssertsResult, UnifyAssertsResult
from ctac.ua.split import split_asserts


def uniquify_asserts(
    program: TacProgram, *, strategy: str = "merge"
) -> UnifyAssertsResult:
    """Strip ``assert true``, purify predicates, then merge asserts.

    Only the ``merge`` strategy returns :class:`UnifyAssertsResult`.
    For ``split``, call :func:`uniquify_asserts_split` instead — its
    return type is different.
    """
    if strategy != "merge":
        raise ValueError(
            f"uniquify_asserts handles only 'merge'; got {strategy!r}. "
            f"For 'split' use uniquify_asserts_split."
        )
    program, removed_asserts, extra = _run_prepasses(program)
    result = merge_asserts(program)
    # Thread the pre-pass removal count and the PURIFY_ASSERT-introduced
    # fresh symbols through the result. These belong to uniquify_asserts —
    # the library-level merge_asserts primitive doesn't introduce symbols
    # and shouldn't report removals it didn't perform.
    return UnifyAssertsResult(
        program=result.program,
        asserts_merged=result.asserts_merged,
        error_block_id=result.error_block_id,
        was_noop=result.was_noop,
        removed_true_asserts=len(removed_asserts),
        extra_symbols=extra,
    )


def uniquify_asserts_split(program: TacProgram) -> SplitAssertsResult:
    """Strip ``assert true``, purify predicates, then split asserts.

    Returns :class:`SplitAssertsResult` whose ``outputs`` carry one
    program per assertion — same pre-passes as :func:`uniquify_asserts`,
    just a different terminal step.
    """
    program, removed_asserts, extra = _run_prepasses(program)
    result = split_asserts(program)
    return SplitAssertsResult(
        outputs=result.outputs,
        asserts_before=result.asserts_before,
        was_noop=result.was_noop,
        removed_true_asserts=len(removed_asserts),
        extra_symbols=extra,
    )


def _run_prepasses(
    program: TacProgram,
) -> tuple[TacProgram, tuple, tuple[tuple[str, str], ...]]:
    """Shared pre-pass sequence: remove_true_asserts then PURIFY_ASSERT."""
    program, removed = remove_true_asserts(program)
    rewrite = rewrite_program(program, (PURIFY_ASSERT,))
    return rewrite.program, removed, rewrite.extra_symbols
