"""Uniquify-asserts (ua) transforms.

Exports:

    :class:`UnifyAssertsResult` — merge outcome (single program + counts).
    :class:`SplitAssertsResult` — split outcome (one program per assert).
    :class:`SplitAssertOutput` — single per-assert entry in the split result.
    :func:`merge_asserts` — redirect every ``AssertCmd`` to a shared
        ``__UA_ERROR`` block so the output program has at most one assertion.
    :func:`split_asserts` — emit one program per assertion (others become
        ``AssumeExpCmd``), each pruned to the live assert's cone of influence.
    :func:`uniquify_asserts` — merge-strategy convenience entry that runs
        the same pre-passes the ``ctac ua`` CLI runs.
    :func:`uniquify_asserts_split` — split-strategy convenience entry.
"""

from ctac.ua.merge import merge_asserts
from ctac.ua.model import (
    SplitAssertOutput,
    SplitAssertsResult,
    UnifyAssertsResult,
)
from ctac.ua.pipeline import uniquify_asserts, uniquify_asserts_split
from ctac.ua.split import split_asserts

__all__ = [
    "SplitAssertOutput",
    "SplitAssertsResult",
    "UnifyAssertsResult",
    "merge_asserts",
    "split_asserts",
    "uniquify_asserts",
    "uniquify_asserts_split",
]
