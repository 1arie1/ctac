"""Compatibility shim for the legacy `claude/pp_smt.py` API.

The experimental scripts in `claude/` (`collapse_ite.py`, `strip_fresh.py`,
`strip_trivial.py`) used a simple nested-list representation:

  atoms are bare strings
  forms are Python `list[str | list]`

The typed parser in this package produces `Atom`, `List_`, `CommentBlock`
nodes instead. These two helpers convert back to the legacy shape so the
existing scripts can be migrated one-line:

  - from pp_smt import parse_all, compact
  + from ctac.solver.smt2.compat import parse_all, compact

After all callers have migrated, this module can be deleted.
"""
from __future__ import annotations

from ctac.solver.smt2.sexpr import Atom, CommentBlock, List_, SexprNode, parse_sexprs


_Legacy = str | list   # nested: atoms are strings, forms are lists


def _to_legacy(node: SexprNode) -> _Legacy | None:
    """Convert one typed SexprNode to the legacy nested-list shape.

    Comments are dropped (matching the original pp_smt.py behavior)."""
    if isinstance(node, Atom):
        return node.text
    if isinstance(node, CommentBlock):
        return None   # legacy pp_smt drops comments
    if isinstance(node, List_):
        out: list[_Legacy] = []
        for c in node.children:
            r = _to_legacy(c)
            if r is not None:
                out.append(r)
        return out
    return None


def parse_all(src: str) -> list[_Legacy]:
    """Legacy parse_all — nested list output, comments dropped.

    Used as a drop-in replacement for `claude.pp_smt.parse_all`."""
    nodes = parse_sexprs(src)
    out: list[_Legacy] = []
    for n in nodes:
        r = _to_legacy(n)
        if r is not None:
            out.append(r)
    return out


def compact(s: _Legacy) -> str:
    """Legacy compact — flatten a nested-list S-expr to single-line text.

    Used as a drop-in replacement for `claude.pp_smt.compact`."""
    if isinstance(s, str):
        return s
    return '(' + ' '.join(compact(c) for c in s) + ')'
