"""Tiny TAC (``ttac``) - parser, AST, and pretty-printer.

``ttac`` is the small source language for VC generation documented in
``docs/vc/``: a fragment of TAC with infix expressions, label-prefixed
blocks, named terminators, and references/borrowing.
"""

from __future__ import annotations

from . import ast
from .errors import TtacParseError, TtacTypeError
from .parser import parse_program
from .pretty import pretty

# ``parse_string`` is the conventional name elsewhere in the codebase.
parse_string = parse_program

__all__ = [
    "ast",
    "TtacParseError",
    "TtacTypeError",
    "parse_program",
    "parse_string",
    "pretty",
    "extract_def_use",
    "check_dsa",
    "analyze_types",
    "infer_types",
    "merge_asserts",
    "split_asserts",
    "to_single_assert",
    "desugar_refs",
    "collect_stats",
]

_ANALYSIS_EXPORTS = ("extract_def_use", "check_dsa", "analyze_types", "infer_types")
_TRANSFORM_EXPORTS = ("merge_asserts", "split_asserts", "to_single_assert", "desugar_refs")


def __getattr__(name: str):
    # Lazy re-export of the analyses/transforms (defers the networkx import).
    if name in _ANALYSIS_EXPORTS:
        from . import analysis

        return getattr(analysis, name)
    if name in _TRANSFORM_EXPORTS:
        from . import transform

        return getattr(transform, name)
    if name == "collect_stats":
        from .stats import collect_stats

        return collect_stats
    raise AttributeError(f"module {__name__!r} has no attribute {name!r}")
