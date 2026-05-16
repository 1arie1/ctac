"""S-expression parser over the lexer's token stream.

Produces a list of `SexprNode`s — typed atoms, lists, or comment blocks
— each carrying source spans (byte offsets) so unchanged forms can be
emitted byte-identical via source slicing.

Comments at the top level of the file (between forms) are grouped into
`CommentBlock`s. Comments INSIDE a form are kept as Atom-like nodes
within the form's children, preserving their position; this isn't
typical in our corpus but the lexer doesn't forbid it.
"""
from __future__ import annotations

from abc import ABC
from dataclasses import dataclass, field

from ctac.solver.smt2.lexer import Token, TokenKind, tokenize


class SexprNode(ABC):
    """Abstract base; concrete nodes carry `.span = (start, end)`."""
    span: tuple[int, int]


@dataclass
class Atom(SexprNode):
    text: str
    kind: TokenKind
    span: tuple[int, int] = (-1, -1)


@dataclass
class List_(SexprNode):
    """A `( ... )` form. Children are SexprNodes in source order."""
    children: list[SexprNode] = field(default_factory=list)
    span: tuple[int, int] = (-1, -1)

    @property
    def head(self) -> SexprNode | None:
        """First child, if any. Convenient for command dispatch."""
        return self.children[0] if self.children else None

    @property
    def head_text(self) -> str | None:
        """`.text` of the first child if it's an Atom; else None."""
        h = self.head
        if isinstance(h, Atom):
            return h.text
        return None


@dataclass
class CommentBlock(SexprNode):
    """Run of one or more contiguous `;` comment lines at the top level.

    Adjacent comments (no blank line between) coalesce into one block.
    Each `lines[i]` is the comment text WITHOUT the trailing newline,
    including the leading `;`."""
    lines: list[str] = field(default_factory=list)
    span: tuple[int, int] = (-1, -1)


class Smt2ParseError(Exception):
    def __init__(self, msg: str, pos: int) -> None:
        super().__init__(f'{msg} at offset {pos}')
        self.pos = pos


def parse_sexprs(src: str) -> list[SexprNode]:
    """Top-level: tokenize + parse into a flat list of SexprNodes.

    Top-level comments are coalesced into `CommentBlock`s. Forms are
    `List_`s. Bare atoms at the top level (rare in SMT-LIB but legal)
    become `Atom` nodes.
    """
    tokens = list(tokenize(src))
    p = _Parser(tokens, src)
    return p.parse_top_level()


class _Parser:
    """Recursive-descent parser. State held in instance attributes
    rather than closure-captured mutable lists (cleaner than pp_smt.py
    style)."""

    def __init__(self, tokens: list[Token], src: str) -> None:
        self.tokens = tokens
        self.pos = 0
        self.src = src

    def _peek(self) -> Token:
        return self.tokens[self.pos]

    def _advance(self) -> Token:
        t = self.tokens[self.pos]
        self.pos += 1
        return t

    def parse_top_level(self) -> list[SexprNode]:
        out: list[SexprNode] = []
        while self._peek().kind is not TokenKind.EOF:
            t = self._peek()
            if t.kind is TokenKind.COMMENT:
                out.append(self._consume_comment_block())
                continue
            out.append(self._parse_one())
        return out

    def _consume_comment_block(self) -> CommentBlock:
        """Coalesce one or more contiguous COMMENT tokens (separated only
        by single newlines / whitespace lacking blank lines) into a block.
        Conservative: stop at any non-comment intervening token."""
        first = self._advance()
        assert first.kind is TokenKind.COMMENT
        lines = [first.text]
        start = first.start
        end = first.end
        while self._peek().kind is TokenKind.COMMENT:
            # Adjacent only if at most one newline of separation between
            # end of previous comment and start of this one.
            cur = self._peek()
            gap = self.src[end:cur.start]
            # Count newlines in the gap; if >1, treat as new block.
            if gap.count('\n') > 1:
                break
            self._advance()
            lines.append(cur.text)
            end = cur.end
        return CommentBlock(lines=lines, span=(start, end))

    def _parse_one(self) -> SexprNode:
        t = self._peek()
        if t.kind is TokenKind.LPAREN:
            return self._parse_list()
        if t.kind is TokenKind.RPAREN:
            raise Smt2ParseError('unexpected )', t.start)
        if t.kind is TokenKind.EOF:
            raise Smt2ParseError('unexpected EOF', t.start)
        if t.kind is TokenKind.COMMENT:
            # Comment inside a form — keep as a single-line CommentBlock
            self._advance()
            return CommentBlock(lines=[t.text], span=(t.start, t.end))
        # Atom
        self._advance()
        return Atom(text=t.text, kind=t.kind, span=(t.start, t.end))

    def _parse_list(self) -> List_:
        lp = self._advance()
        assert lp.kind is TokenKind.LPAREN
        children: list[SexprNode] = []
        while True:
            t = self._peek()
            if t.kind is TokenKind.RPAREN:
                rp = self._advance()
                return List_(children=children, span=(lp.start, rp.end))
            if t.kind is TokenKind.EOF:
                raise Smt2ParseError('unterminated list (missing `)`)', lp.start)
            children.append(self._parse_one())
