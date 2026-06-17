"""Tiny TAC (``ttac``) - parser, AST, and pretty-printer.

``ttac`` is the small source language for VC generation documented in
``doc/vc/``: a fragment of TAC with infix expressions, label-prefixed
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
]


def __getattr__(name: str):
    # Lazy re-export of the analyses (avoids importing networkx at parse time).
    if name in ("extract_def_use", "check_dsa", "analyze_types", "infer_types"):
        from . import analysis

        return getattr(analysis, name)
    raise AttributeError(f"module {__name__!r} has no attribute {name!r}")
