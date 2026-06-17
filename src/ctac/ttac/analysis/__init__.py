"""Static analyses over the Tiny TAC AST.

Mirrors the strategies of the TAC analyses in ``ctac.analysis`` (def-use,
DSA validation, type inference) over ``ttac``'s own AST, reusing
``networkx`` for the graph plumbing.
"""

from __future__ import annotations

from .defuse import DefUse, extract_def_use
from .dsa import DsaResult, check_dsa
from .typeinfer import TypeResult, analyze_types, infer_types

__all__ = [
    "DefUse",
    "extract_def_use",
    "DsaResult",
    "check_dsa",
    "TypeResult",
    "analyze_types",
    "infer_types",
]
