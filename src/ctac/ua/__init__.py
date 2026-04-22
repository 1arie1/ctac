"""Uniquify-asserts (ua) transforms.

Exports:

    :class:`UnifyAssertsResult` — per-strategy outcome (counts + program).
    :func:`merge_asserts` — redirect every ``AssertCmd`` to a shared
        ``__UA_ERROR`` block so the output program has at most one assertion.
    :func:`uniquify_asserts` — convenience entry that strips ``assert true``,
        purifies remaining assertion predicates, and applies the chosen
        strategy. Matches what ``ctac ua`` runs on the command line.
"""

from ctac.ua.merge import merge_asserts
from ctac.ua.model import UnifyAssertsResult
from ctac.ua.pipeline import uniquify_asserts

__all__ = [
    "UnifyAssertsResult",
    "merge_asserts",
    "uniquify_asserts",
]
