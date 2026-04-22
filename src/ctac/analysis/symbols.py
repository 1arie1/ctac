"""Helpers for canonical TAC symbol names and sort classification."""

from __future__ import annotations

import re
from enum import Enum

_META_SUFFIX_RE = re.compile(r":\d+$")

# Matches an entry line from the ``TACSymbolTable { ... }`` section:
#     ``name:sort``           (no DSA revision)
#     ``name:sort:revision``  (DSA revision suffix)
# Anchored to both ends so JSON-tagged builtin-function lines and nested
# section markers (``UserDefined {`` etc.) don't accidentally parse.
_SYMBOL_LINE_RE = re.compile(
    r"^([A-Za-z_][A-Za-z0-9_]*):([a-zA-Z][a-zA-Z0-9]*)(?::\d+)?$"
)

# Sort tokens in the pipeline that denote memory (array) symbols.
_MEMORY_SORTS = frozenset({"bytemap", "ghostmap"})


class SymbolKind(str, Enum):
    """Coarse classification of a TAC symbol based on its declared sort.

    Derived purely from the sort text in the symbol table — names are only
    a convention (e.g. ``M<N>`` in Certora output) and not authoritative.
    """

    SCALAR = "scalar"
    MEMORY = "memory"


def canonical_symbol(symbol: str, *, strip_var_suffixes: bool = True) -> str:
    """Return normalized symbol key for analyses."""
    s = symbol.strip()
    if strip_var_suffixes:
        return _META_SUFFIX_RE.sub("", s)
    return s


def classify_sort(sort_text: str) -> SymbolKind:
    """Classify a sort token into :class:`SymbolKind`.

    Unknown sorts fall back to :attr:`SymbolKind.SCALAR`. If and when new
    memory-shaped sorts are introduced they need to be added to
    ``_MEMORY_SORTS`` above — this module is the single source of truth.
    """
    return SymbolKind.MEMORY if sort_text in _MEMORY_SORTS else SymbolKind.SCALAR


def parse_symbol_sorts(symbol_table_text: str) -> dict[str, str]:
    """Parse a ``TACSymbolTable { ... }`` section into ``{name: sort}``.

    Matches only ``name:sort[:revision]`` lines, which skips nested
    ``UserDefined``/``BuiltinFunctions``/``UninterpretedFunctions`` blocks
    (whose entries don't fit the pattern because of JSON annotations and
    different whitespace shapes) without needing to track brace depth.
    """
    sorts: dict[str, str] = {}
    for line in symbol_table_text.split("\n"):
        m = _SYMBOL_LINE_RE.match(line.strip())
        if m is not None:
            sorts[m.group(1)] = m.group(2)
    return sorts
