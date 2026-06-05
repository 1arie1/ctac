"""SMT-LIB v2 tokenizer.

Produces a stream of typed `Token`s with byte-offset spans. Comments
are preserved as COMMENT tokens; whitespace is skipped silently. Byte-
offset spans on tokens let the parser reconstruct exact source for
round-trip emit.

Reference: SMT-LIB v2 standard, section 3.1 (Lexicon). We don't aim
for full Unicode symbol coverage — the ctac corpus is ASCII, and we
keep the lexer pragmatic.
"""
from __future__ import annotations

from dataclasses import dataclass
from enum import Enum, auto
from typing import Iterator


class TokenKind(Enum):
    LPAREN = auto()
    RPAREN = auto()
    SYMBOL = auto()         # simple symbol: foo, R633, +, narrow.bv256
    QUOTED_SYMBOL = auto()  # |...| form
    KEYWORD = auto()        # :foo
    NUMERAL = auto()        # 0, 42, 12884901912 (non-negative integer)
    DECIMAL = auto()        # 3.14
    HEX = auto()            # #x1A2B
    BINARY = auto()         # #b1010
    STRING = auto()         # "..." (including delimiters in .text)
    COMMENT = auto()        # ; ... \n  (newline NOT included in .text)
    EOF = auto()


@dataclass(frozen=True)
class Token:
    kind: TokenKind
    text: str            # exact source text (including delimiters for strings)
    start: int           # byte offset
    end: int             # exclusive byte offset (so src[start:end] == text)


class Smt2LexError(Exception):
    """Raised when the lexer encounters malformed input."""

    def __init__(self, msg: str, pos: int, line: int, col: int) -> None:
        super().__init__(f'{msg} at line {line}, column {col} (offset {pos})')
        self.pos = pos
        self.line = line
        self.col = col


# Per SMT-LIB v2, simple-symbol chars: letters, digits, and ~!@$%^&*_-+=<>.?/
# We accept those plus '.', ':' inside symbols (z3 allows narrow.bv256, etc.).
# Note ':' starts a keyword only when at the FRONT; mid-symbol ':' is allowed
# (z3 emits names like `lemma_int_mul_div_bounds` and `narrow.bv256`).
_SYMBOL_CHARS = set('abcdefghijklmnopqrstuvwxyz'
                     'ABCDEFGHIJKLMNOPQRSTUVWXYZ'
                     '0123456789'
                     '~!@$%^&*_-+=<>.?/')


def line_col(src: str, pos: int) -> tuple[int, int]:
    """1-based line and column for a byte offset (linear scan; only used
    on errors so cost doesn't matter)."""
    line = src.count('\n', 0, pos) + 1
    last_nl = src.rfind('\n', 0, pos)
    col = pos - last_nl if last_nl >= 0 else pos + 1
    return line, col


def tokenize(src: str) -> Iterator[Token]:
    """Yield Tokens for the source string.

    Whitespace is skipped silently (not emitted as tokens). Comments are
    emitted as COMMENT tokens whose text excludes the trailing newline.
    """
    i = 0
    n = len(src)
    while i < n:
        c = src[i]
        # Whitespace
        if c.isspace():
            i += 1
            continue
        # Comment
        if c == ';':
            start = i
            j = src.find('\n', i)
            if j < 0:
                j = n
            yield Token(TokenKind.COMMENT, src[start:j], start, j)
            i = j
            continue
        # Parens
        if c == '(':
            yield Token(TokenKind.LPAREN, '(', i, i + 1)
            i += 1
            continue
        if c == ')':
            yield Token(TokenKind.RPAREN, ')', i, i + 1)
            i += 1
            continue
        # Quoted symbol
        if c == '|':
            start = i
            j = src.find('|', i + 1)
            if j < 0:
                line, col = line_col(src, i)
                raise Smt2LexError('unterminated |...| quoted symbol', i, line, col)
            yield Token(TokenKind.QUOTED_SYMBOL, src[start:j + 1], start, j + 1)
            i = j + 1
            continue
        # String literal
        if c == '"':
            start = i
            j = i + 1
            while j < n:
                if src[j] == '"':
                    # SMT-LIB escape: "" inside string is a literal "
                    if j + 1 < n and src[j + 1] == '"':
                        j += 2
                        continue
                    break
                j += 1
            if j >= n:
                line, col = line_col(src, i)
                raise Smt2LexError('unterminated string literal', i, line, col)
            yield Token(TokenKind.STRING, src[start:j + 1], start, j + 1)
            i = j + 1
            continue
        # Hex / binary literal
        if c == '#' and i + 1 < n and src[i + 1] in 'xX':
            start = i
            j = i + 2
            while j < n and src[j] in '0123456789abcdefABCDEF':
                j += 1
            if j == start + 2:
                line, col = line_col(src, i)
                raise Smt2LexError('empty hex literal', i, line, col)
            yield Token(TokenKind.HEX, src[start:j], start, j)
            i = j
            continue
        if c == '#' and i + 1 < n and src[i + 1] in 'bB':
            start = i
            j = i + 2
            while j < n and src[j] in '01':
                j += 1
            if j == start + 2:
                line, col = line_col(src, i)
                raise Smt2LexError('empty binary literal', i, line, col)
            yield Token(TokenKind.BINARY, src[start:j], start, j)
            i = j
            continue
        # Keyword: :foo
        if c == ':':
            start = i
            j = i + 1
            while j < n and src[j] in _SYMBOL_CHARS:
                j += 1
            if j == start + 1:
                line, col = line_col(src, i)
                raise Smt2LexError('empty keyword', i, line, col)
            yield Token(TokenKind.KEYWORD, src[start:j], start, j)
            i = j
            continue
        # Numeral / decimal
        if c.isdigit():
            start = i
            j = i
            while j < n and src[j].isdigit():
                j += 1
            if j < n and src[j] == '.':
                j += 1
                while j < n and src[j].isdigit():
                    j += 1
                yield Token(TokenKind.DECIMAL, src[start:j], start, j)
            else:
                yield Token(TokenKind.NUMERAL, src[start:j], start, j)
            i = j
            continue
        # Simple symbol
        if c in _SYMBOL_CHARS:
            start = i
            j = i
            while j < n and src[j] in _SYMBOL_CHARS:
                j += 1
            yield Token(TokenKind.SYMBOL, src[start:j], start, j)
            i = j
            continue
        # Unknown character
        line, col = line_col(src, i)
        raise Smt2LexError(f'unexpected character {c!r}', i, line, col)

    yield Token(TokenKind.EOF, '', n, n)
