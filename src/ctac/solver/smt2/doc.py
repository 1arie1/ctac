"""Wadler-style pretty-printing combinators.

A `Doc` describes a printable structure. The rendering algorithm decides
per-`Group` whether to render its contents flat (single line) or with
each `Line` becoming a newline + current indent. Picks flat iff the
flattened result fits in the remaining width budget at the current
column.

Constructors:
  text(s)            verbatim string s (no newlines inside)
  line()             a soft line break — flat: one space; broken: newline + indent
  hardline()         always a newline + indent (never flat)
  nil()              empty
  concat([...])      sequence of docs
  nest(n, d)         add n to the current indent level for d
  group(d)           try to render d flat; if it doesn't fit, broken
  align(d)           set current indent to the current column for d

Reference: Philip Wadler, "A Prettier Printer" (1998).
"""
from __future__ import annotations

from abc import ABC
from dataclasses import dataclass


class Doc(ABC):
    pass


@dataclass(frozen=True)
class _Nil(Doc):
    pass


@dataclass(frozen=True)
class _Text(Doc):
    s: str

    def __post_init__(self) -> None:
        assert '\n' not in self.s, 'use line()/hardline() for newlines'


@dataclass(frozen=True)
class _Line(Doc):
    hard: bool          # always newline if True; soft (group-controlled) if False


@dataclass(frozen=True)
class _Concat(Doc):
    parts: tuple[Doc, ...]


@dataclass(frozen=True)
class _Nest(Doc):
    n: int
    doc: Doc


@dataclass(frozen=True)
class _Group(Doc):
    doc: Doc


@dataclass(frozen=True)
class _Align(Doc):
    doc: Doc


# ---- Smart constructors ----------------------------------------------------


_NIL_SINGLETON = _Nil()


def nil() -> Doc:
    return _NIL_SINGLETON


def text(s: str) -> Doc:
    if not s:
        return nil()
    return _Text(s)


def line() -> Doc:
    return _Line(hard=False)


def hardline() -> Doc:
    return _Line(hard=True)


def concat(parts: list[Doc] | tuple[Doc, ...]) -> Doc:
    parts = tuple(p for p in parts if not isinstance(p, _Nil))
    if not parts:
        return nil()
    if len(parts) == 1:
        return parts[0]
    return _Concat(parts)


def nest(n: int, doc: Doc) -> Doc:
    if n == 0 or isinstance(doc, _Nil):
        return doc
    return _Nest(n, doc)


def group(doc: Doc) -> Doc:
    if isinstance(doc, _Nil):
        return doc
    return _Group(doc)


def align(doc: Doc) -> Doc:
    if isinstance(doc, _Nil):
        return doc
    return _Align(doc)


# ---- Convenience builders --------------------------------------------------


def hsep(parts: list[Doc], sep: Doc | None = None) -> Doc:
    """Horizontal join: docs joined by `sep` (default: single space)."""
    if not parts:
        return nil()
    if sep is None:
        sep = text(' ')
    out: list[Doc] = []
    for i, p in enumerate(parts):
        if i:
            out.append(sep)
        out.append(p)
    return concat(out)


def vsep(parts: list[Doc]) -> Doc:
    """Vertical join: docs separated by `line()` (newline when broken)."""
    if not parts:
        return nil()
    out: list[Doc] = []
    for i, p in enumerate(parts):
        if i:
            out.append(line())
        out.append(p)
    return concat(out)


def parens(inner: Doc) -> Doc:
    return concat([text('('), inner, text(')')])


# ---- Renderer --------------------------------------------------------------


def _fits(remaining: int, items: list[tuple[int, bool, Doc]]) -> bool:
    """Could the prefix of `items` (rendered FLAT) fit in `remaining` columns
    before reaching a Line we'd have to break? Lazy left-to-right walk —
    bails on first not-flattenable break."""
    while items and remaining >= 0:
        indent, flat, doc = items.pop(0)
        if isinstance(doc, _Nil):
            continue
        if isinstance(doc, _Text):
            remaining -= len(doc.s)
            continue
        if isinstance(doc, _Line):
            if doc.hard:
                return False
            if flat:
                remaining -= 1  # flat soft line = single space
                continue
            return True   # broken line — column resets; we fit by definition here
        if isinstance(doc, _Concat):
            items[:0] = [(indent, flat, p) for p in doc.parts]
            continue
        if isinstance(doc, _Nest):
            items.insert(0, (indent + doc.n, flat, doc.doc))
            continue
        if isinstance(doc, _Group):
            # Conservatively assume flat for the fit check
            items.insert(0, (indent, True, doc.doc))
            continue
        if isinstance(doc, _Align):
            items.insert(0, (indent, flat, doc.doc))
            continue
    return remaining >= 0


def render(doc: Doc, width: int = 100) -> str:
    """Render `doc` to a string, breaking groups that don't fit `width`."""
    out: list[str] = []
    col = 0
    # Stack: list of (indent, flat, Doc). Process left-to-right via pop(0).
    stack: list[tuple[int, bool, Doc]] = [(0, False, doc)]
    while stack:
        indent, flat, d = stack.pop(0)
        if isinstance(d, _Nil):
            continue
        if isinstance(d, _Text):
            out.append(d.s)
            col += len(d.s)
            continue
        if isinstance(d, _Line):
            if flat and not d.hard:
                out.append(' ')
                col += 1
            else:
                out.append('\n')
                out.append(' ' * indent)
                col = indent
            continue
        if isinstance(d, _Concat):
            # Inline; preserve order
            stack[:0] = [(indent, flat, p) for p in d.parts]
            continue
        if isinstance(d, _Nest):
            stack.insert(0, (indent + d.n, flat, d.doc))
            continue
        if isinstance(d, _Align):
            stack.insert(0, (col, flat, d.doc))
            continue
        if isinstance(d, _Group):
            # Try flat?
            trial = [(indent, True, d.doc)]
            if _fits(width - col, list(trial)):
                stack.insert(0, (indent, True, d.doc))
            else:
                stack.insert(0, (indent, False, d.doc))
            continue
    return ''.join(out)
