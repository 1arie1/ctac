"""Parse-error type for Tiny TAC."""

from __future__ import annotations


class TtacParseError(Exception):
    """A lexing or parsing failure, carrying 1-based source position.

    ``line`` and ``col`` point at the offending token. When the source
    text is available, ``with_caret`` renders the offending line plus a
    caret under the column.
    """

    def __init__(self, message: str, line: int, col: int) -> None:
        self.message = message
        self.line = line
        self.col = col
        super().__init__(f"{line}:{col}: {message}")

    def with_caret(self, source: str) -> str:
        lines = source.splitlines()
        if 1 <= self.line <= len(lines):
            src_line = lines[self.line - 1]
            caret = " " * (self.col - 1) + "^"
            return f"{self}\n    {src_line}\n    {caret}"
        return str(self)
