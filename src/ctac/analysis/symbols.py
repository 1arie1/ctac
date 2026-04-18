"""Helpers for canonical TAC symbol names."""

from __future__ import annotations

import re

_META_SUFFIX_RE = re.compile(r":\d+$")


def canonical_symbol(symbol: str, *, strip_var_suffixes: bool = True) -> str:
    """Return normalized symbol key for analyses."""
    s = symbol.strip()
    if strip_var_suffixes:
        return _META_SUFFIX_RE.sub("", s)
    return s
