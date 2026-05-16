"""Tests for ctac.solver.smt2.lexer.

Token-level edge cases: parens, simple symbols, keywords, numerals
(including very large bv256-size integers), decimals, hex/binary
literals, quoted symbols, strings (with SMT-LIB `""` escape), comments
(including comment-at-EOF without trailing newline). Position tracking
on the resulting tokens.
"""
from __future__ import annotations

import pytest

from ctac.solver.smt2.lexer import (
    Smt2LexError,
    Token,
    TokenKind,
    tokenize,
)


def _tokens(src: str) -> list[Token]:
    return list(tokenize(src))


def _kinds(src: str) -> list[TokenKind]:
    """Token kinds, dropping the trailing EOF for brevity."""
    return [t.kind for t in _tokens(src)][:-1]


# ---- Parens, simple symbols ------------------------------------------------


def test_empty_input_yields_only_eof() -> None:
    toks = _tokens('')
    assert len(toks) == 1
    assert toks[0].kind is TokenKind.EOF


def test_whitespace_skipped() -> None:
    toks = _tokens('   \n\t  ')
    assert len(toks) == 1
    assert toks[0].kind is TokenKind.EOF


def test_parens_balanced() -> None:
    assert _kinds('()') == [TokenKind.LPAREN, TokenKind.RPAREN]
    assert _kinds('((  ))') == [
        TokenKind.LPAREN, TokenKind.LPAREN,
        TokenKind.RPAREN, TokenKind.RPAREN,
    ]


def test_simple_symbol() -> None:
    toks = _tokens('foo')
    assert toks[0].kind is TokenKind.SYMBOL
    assert toks[0].text == 'foo'
    assert toks[0].start == 0
    assert toks[0].end == 3


def test_symbol_with_dots_and_special_chars() -> None:
    # SMT-LIB simple-symbol charset + dots are valid in our lexer
    toks = _tokens('narrow.bv256 ~!@$%^&*_-+=<>?/')
    assert toks[0].text == 'narrow.bv256'
    assert toks[0].kind is TokenKind.SYMBOL
    assert toks[1].text == '~!@$%^&*_-+=<>?/'
    assert toks[1].kind is TokenKind.SYMBOL


# ---- Keywords --------------------------------------------------------------


def test_keyword() -> None:
    toks = _tokens(':named')
    assert toks[0].kind is TokenKind.KEYWORD
    assert toks[0].text == ':named'


def test_keyword_followed_by_value() -> None:
    kinds = _kinds(':produce-unsat-cores true')
    assert kinds == [TokenKind.KEYWORD, TokenKind.SYMBOL]


def test_empty_keyword_errors() -> None:
    # Just `:` with nothing after is invalid
    with pytest.raises(Smt2LexError):
        _tokens(':')


# ---- Numerals, decimals ----------------------------------------------------


def test_numeral() -> None:
    toks = _tokens('42')
    assert toks[0].kind is TokenKind.NUMERAL
    assert toks[0].text == '42'


def test_large_bv256_size_numeral() -> None:
    # Real value from p9_orig.smt2
    src = '12884901912'
    toks = _tokens(src)
    assert toks[0].kind is TokenKind.NUMERAL
    assert toks[0].text == '12884901912'


def test_decimal() -> None:
    toks = _tokens('3.14')
    assert toks[0].kind is TokenKind.DECIMAL
    assert toks[0].text == '3.14'


# ---- Hex / binary literals -------------------------------------------------


def test_hex_literal() -> None:
    toks = _tokens('#x1A2B3c')
    assert toks[0].kind is TokenKind.HEX
    assert toks[0].text == '#x1A2B3c'


def test_binary_literal() -> None:
    toks = _tokens('#b10101')
    assert toks[0].kind is TokenKind.BINARY
    assert toks[0].text == '#b10101'


def test_empty_hex_errors() -> None:
    with pytest.raises(Smt2LexError):
        _tokens('#x')


def test_empty_binary_errors() -> None:
    with pytest.raises(Smt2LexError):
        _tokens('#b')


# ---- Quoted symbols --------------------------------------------------------


def test_quoted_symbol() -> None:
    toks = _tokens('|hello world|')
    assert toks[0].kind is TokenKind.QUOTED_SYMBOL
    assert toks[0].text == '|hello world|'


def test_quoted_symbol_with_parens_inside() -> None:
    # Parens inside |...| are part of the symbol, not structural
    toks = _tokens('|foo (bar) baz|')
    assert toks[0].kind is TokenKind.QUOTED_SYMBOL
    assert toks[0].text == '|foo (bar) baz|'


def test_unterminated_quoted_symbol_errors() -> None:
    with pytest.raises(Smt2LexError):
        _tokens('|never closed')


# ---- String literals -------------------------------------------------------


def test_simple_string() -> None:
    toks = _tokens('"hello"')
    assert toks[0].kind is TokenKind.STRING
    assert toks[0].text == '"hello"'


def test_string_with_escaped_quote() -> None:
    # SMT-LIB: "" inside a string is a literal "
    src = '"he said ""hi"" friend"'
    toks = _tokens(src)
    assert toks[0].kind is TokenKind.STRING
    assert toks[0].text == src


def test_unterminated_string_errors() -> None:
    with pytest.raises(Smt2LexError):
        _tokens('"never closed')


# ---- Comments --------------------------------------------------------------


def test_comment() -> None:
    toks = _tokens('; a comment\n42')
    assert toks[0].kind is TokenKind.COMMENT
    assert toks[0].text == '; a comment'
    assert toks[1].kind is TokenKind.NUMERAL


def test_comment_at_eof_without_newline() -> None:
    toks = _tokens('; comment at end')
    # First token is the comment; second is EOF
    assert toks[0].kind is TokenKind.COMMENT
    assert toks[0].text == '; comment at end'
    assert toks[1].kind is TokenKind.EOF


def test_comment_inside_form_is_a_token() -> None:
    # The lexer doesn't strip comments — that's the parser's job
    kinds = _kinds('(and ; mid-form\n x y)')
    assert TokenKind.COMMENT in kinds


def test_multiple_comments() -> None:
    src = '; line 1\n; line 2\n42'
    toks = _tokens(src)
    assert toks[0].kind is TokenKind.COMMENT
    assert toks[0].text == '; line 1'
    assert toks[1].kind is TokenKind.COMMENT
    assert toks[1].text == '; line 2'
    assert toks[2].kind is TokenKind.NUMERAL


# ---- Position tracking -----------------------------------------------------


def test_positions_are_byte_offsets() -> None:
    src = '(foo 42)'
    toks = _tokens(src)
    # ( at 0, foo at 1-3, 42 at 5-6, ) at 7
    assert toks[0].kind is TokenKind.LPAREN
    assert (toks[0].start, toks[0].end) == (0, 1)
    assert toks[1].text == 'foo'
    assert (toks[1].start, toks[1].end) == (1, 4)
    assert toks[2].text == '42'
    assert (toks[2].start, toks[2].end) == (5, 7)
    assert toks[3].kind is TokenKind.RPAREN
    assert (toks[3].start, toks[3].end) == (7, 8)


def test_positions_survive_newlines_and_comments() -> None:
    src = ';c\n(x)'
    toks = _tokens(src)
    # ;c at 0-2 (text includes ;c but NOT the newline)
    assert toks[0].kind is TokenKind.COMMENT
    assert toks[0].text == ';c'
    assert (toks[0].start, toks[0].end) == (0, 2)
    # newline is skipped (whitespace)
    assert toks[1].kind is TokenKind.LPAREN
    assert toks[1].start == 3   # after ;c\n
    assert toks[2].text == 'x'
    assert toks[2].start == 4


# ---- Combined realistic line -----------------------------------------------


def test_realistic_assert_with_named() -> None:
    src = '(assert (! (= R633 R777) :named alias_R633))'
    toks = [t for t in _tokens(src) if t.kind is not TokenKind.EOF]
    text_seq = [t.text for t in toks]
    assert text_seq == [
        '(', 'assert', '(', '!', '(', '=', 'R633', 'R777', ')',
        ':named', 'alias_R633', ')', ')',
    ]
    # The :named token is correctly classified
    named_tok = next(t for t in toks if t.text == ':named')
    assert named_tok.kind is TokenKind.KEYWORD


def test_unexpected_char_raises() -> None:
    # Backtick is not in the symbol charset and not a structural char
    with pytest.raises(Smt2LexError) as exc_info:
        _tokens('foo `bar')
    assert exc_info.value.pos == 4   # position of `
