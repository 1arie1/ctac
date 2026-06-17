"""Tiny TAC (``ttac``) - parser, AST, and pretty-printer.

``ttac`` is the small source language for VC generation documented in
``doc/vc/``: a fragment of TAC with infix expressions, label-prefixed
blocks, named terminators, and references/borrowing.
"""

from __future__ import annotations

from . import ast
from .errors import TtacParseError
from .parser import parse_program
from .pretty import pretty

# ``parse_string`` is the conventional name elsewhere in the codebase.
parse_string = parse_program

__all__ = [
    "ast",
    "TtacParseError",
    "parse_program",
    "parse_string",
    "pretty",
]
