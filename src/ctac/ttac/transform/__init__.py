"""Tiny TAC source-to-source transforms.

Layered, bottom-up:

- :mod:`cfg_slice` - ``restrict_to_block``: prune the CFG to a target
  block and its ancestors, preserving single-entry/single-exit.
- :mod:`single_assert` - ``to_single_assert``: convert a multi-assert
  program into Single-Assert form around one chosen assert.
- :mod:`ua` - the ``ua`` strategies ``merge_asserts`` / ``split_asserts``.
"""

from __future__ import annotations

from .cfg_slice import restrict_to_block
from .desugar import DesugarResult, desugar_refs
from .single_assert import to_single_assert
from .ssa import SsaResult, to_ssa
from .ua import (
    MergeResult,
    SplitOutput,
    SplitResult,
    annotate_havoc_types,
    merge_asserts,
    split_asserts,
)

__all__ = [
    "restrict_to_block",
    "to_single_assert",
    "SsaResult",
    "to_ssa",
    "DesugarResult",
    "desugar_refs",
    "MergeResult",
    "SplitOutput",
    "SplitResult",
    "annotate_havoc_types",
    "merge_asserts",
    "split_asserts",
]
