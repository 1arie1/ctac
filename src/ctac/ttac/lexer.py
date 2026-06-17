"""Hand-written scanner for Tiny TAC.

Produces a flat token stream with 1-based ``(line, col)`` on every
token. Whitespace (other than newlines) and ``//`` line comments are
skipped; consecutive and leading newlines collapse to a single
``NEWLINE`` token, and a ``NEWLINE`` is guaranteed before ``EOF`` so the
parser can terminate every command uniformly.

Punctuation tokens use the punctuation text itself as their ``kind``
(e.g. a token for ``:=`` has ``kind == ':='``). Identifiers and
keywords share ``kind == 'NAME'``; the parser distinguishes keywords by
matching ``value`` against its reserved sets.
"""

from __future__ import annotations

from dataclasses import dataclass

from .errors import TtacParseError

# Two-character operators, checked before their single-char prefixes.
_TWO_CHAR = ("==", "<=", ":=")
_ONE_CHAR = frozenset("<+-*/()[]{},:.")


@dataclass(frozen=True)
class Token:
    kind: str
    value: str
    line: int
    col: int


def tokenize(source: str) -> list[Token]:
    """Scan ``source`` into a token list ending in a ``NEWLINE`` and ``EOF``."""
    tokens: list[Token] = []
    i = 0
    n = len(source)
    line = 1
    col = 1

    def emit(kind: str, value: str, tline: int, tcol: int) -> None:
        tokens.append(Token(kind, value, tline, tcol))

    def at_newline() -> bool:
        return tokens and tokens[-1].kind == "NEWLINE"

    while i < n:
        ch = source[i]

        if ch == "\n":
            if tokens and not at_newline():
                emit("NEWLINE", "\n", line, col)
            i += 1
            line += 1
            col = 1
            continue

        if ch in " \t\r":
            i += 1
            col += 1
            continue

        # Line comment: // ... end of line.
        if ch == "/" and i + 1 < n and source[i + 1] == "/":
            while i < n and source[i] != "\n":
                i += 1
                col += 1
            continue

        two = source[i : i + 2]
        if two in _TWO_CHAR:
            emit(two, two, line, col)
            i += 2
            col += 2
            continue

        if ch in _ONE_CHAR:
            emit(ch, ch, line, col)
            i += 1
            col += 1
            continue

        if ch.isdigit():
            start = i
            start_col = col
            while i < n and source[i].isdigit():
                i += 1
                col += 1
            emit("INT", source[start:i], line, start_col)
            continue

        if ch.isalpha() or ch == "_":
            start = i
            start_col = col
            while i < n and (source[i].isalnum() or source[i] == "_"):
                i += 1
                col += 1
            emit("NAME", source[start:i], line, start_col)
            continue

        raise TtacParseError(f"unexpected character {ch!r}", line, col)

    if tokens and not at_newline():
        emit("NEWLINE", "\n", line, col)
    emit("EOF", "", line, col)
    return tokens
