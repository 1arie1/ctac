"""``uniquify_asserts``: pre-passes + strategy, in one entry point.

Runs the three steps ``ctac ua`` performs on the CLI:

1. ``remove_true_asserts`` — drop every ``assert true`` from the program.
2. PURIFY_ASSERT via the rewrite framework — ensure every surviving
   assertion's predicate is a :class:`SymbolRef` (or a :class:`ConstExpr`
   literal that the strategy handles specially).
3. Apply the chosen strategy (currently only ``"merge"``).

API callers get a turnkey version; CLI callers use the individual steps
directly so they can surface intermediate stats and warnings.
"""

from __future__ import annotations

from ctac.analysis import remove_true_asserts
from ctac.ir.models import TacProgram
from ctac.rewrite import rewrite_program
from ctac.rewrite.rules import PURIFY_ASSERT
from ctac.ua.merge import merge_asserts
from ctac.ua.model import UnifyAssertsResult


def uniquify_asserts(
    program: TacProgram, *, strategy: str = "merge"
) -> UnifyAssertsResult:
    """Strip ``assert true``, purify predicates, then run the chosen strategy."""
    if strategy != "merge":
        raise ValueError(
            f"unknown uniquify-asserts strategy: {strategy!r} "
            f"(supported: 'merge')"
        )
    program, removed_asserts = remove_true_asserts(program)
    rewrite = rewrite_program(program, (PURIFY_ASSERT,))
    program = rewrite.program
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
        extra_symbols=rewrite.extra_symbols,
    )
