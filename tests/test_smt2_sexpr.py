"""Tests for ctac.solver.smt2.sexpr (raw S-expression parser).

Covers nested forms, error handling for unterminated lists and stray
right-parens, comment block coalescing at the top level, and source
span preservation."""
from __future__ import annotations

import pytest

from ctac.solver.smt2.lexer import TokenKind
from ctac.solver.smt2.sexpr import (
    Atom,
    CommentBlock,
    List_,
    Smt2ParseError,
    parse_sexprs,
)


# ---- Atoms -----------------------------------------------------------------


def test_single_atom() -> None:
    nodes = parse_sexprs('foo')
    assert len(nodes) == 1
    assert isinstance(nodes[0], Atom)
    assert nodes[0].text == 'foo'
    assert nodes[0].kind is TokenKind.SYMBOL
    assert nodes[0].span == (0, 3)


def test_multiple_atoms_at_top_level() -> None:
    nodes = parse_sexprs('foo bar 42')
    assert [type(n).__name__ for n in nodes] == ['Atom', 'Atom', 'Atom']
    assert [n.text for n in nodes] == ['foo', 'bar', '42']


# ---- Lists -----------------------------------------------------------------


def test_empty_list() -> None:
    nodes = parse_sexprs('()')
    assert len(nodes) == 1
    assert isinstance(nodes[0], List_)
    assert nodes[0].children == []
    assert nodes[0].span == (0, 2)


def test_flat_list() -> None:
    nodes = parse_sexprs('(a b c)')
    assert len(nodes) == 1
    lst = nodes[0]
    assert isinstance(lst, List_)
    assert [c.text for c in lst.children] == ['a', 'b', 'c']
    assert lst.head_text == 'a'


def test_nested_list() -> None:
    nodes = parse_sexprs('(and (= x 1) (= y 2))')
    assert len(nodes) == 1
    outer = nodes[0]
    assert isinstance(outer, List_)
    assert outer.head_text == 'and'
    inner1 = outer.children[1]
    inner2 = outer.children[2]
    assert isinstance(inner1, List_)
    assert inner1.head_text == '='
    assert [c.text for c in inner1.children] == ['=', 'x', '1']
    assert isinstance(inner2, List_)
    assert inner2.head_text == '='


def test_list_with_keyword_arg() -> None:
    nodes = parse_sexprs('(! body :named foo)')
    lst = nodes[0]
    assert isinstance(lst, List_)
    assert lst.head_text == '!'
    kw = lst.children[2]
    assert isinstance(kw, Atom)
    assert kw.kind is TokenKind.KEYWORD


# ---- Comment blocks --------------------------------------------------------


def test_single_comment_at_top_level() -> None:
    nodes = parse_sexprs('; a comment\n')
    assert len(nodes) == 1
    cb = nodes[0]
    assert isinstance(cb, CommentBlock)
    assert cb.lines == ['; a comment']


def test_adjacent_comments_coalesce() -> None:
    nodes = parse_sexprs('; line 1\n; line 2\n; line 3\n')
    assert len(nodes) == 1
    cb = nodes[0]
    assert isinstance(cb, CommentBlock)
    assert cb.lines == ['; line 1', '; line 2', '; line 3']


def test_blank_line_splits_comment_blocks() -> None:
    nodes = parse_sexprs('; first\n\n; second\n')
    # A blank line (>1 newline gap) creates a new block
    assert len(nodes) == 2
    assert all(isinstance(n, CommentBlock) for n in nodes)
    assert nodes[0].lines == ['; first']
    assert nodes[1].lines == ['; second']


def test_comment_then_form() -> None:
    nodes = parse_sexprs('; header\n(check-sat)')
    assert len(nodes) == 2
    assert isinstance(nodes[0], CommentBlock)
    assert isinstance(nodes[1], List_)
    assert nodes[1].head_text == 'check-sat'


def test_form_then_comment() -> None:
    nodes = parse_sexprs('(check-sat)\n; trailing\n')
    assert len(nodes) == 2
    assert isinstance(nodes[0], List_)
    assert isinstance(nodes[1], CommentBlock)


# ---- Source spans ----------------------------------------------------------


def test_atom_span_matches_substring() -> None:
    src = '   foo  bar'
    nodes = parse_sexprs(src)
    a = nodes[0]
    assert isinstance(a, Atom)
    assert src[a.span[0]:a.span[1]] == 'foo'
    b = nodes[1]
    assert isinstance(b, Atom)
    assert src[b.span[0]:b.span[1]] == 'bar'


def test_list_span_includes_parens() -> None:
    src = '  (and x y)  '
    nodes = parse_sexprs(src)
    lst = nodes[0]
    assert isinstance(lst, List_)
    assert src[lst.span[0]:lst.span[1]] == '(and x y)'


def test_nested_list_spans() -> None:
    src = '(or (and a b) c)'
    nodes = parse_sexprs(src)
    outer = nodes[0]
    inner = outer.children[1]
    assert isinstance(inner, List_)
    assert src[inner.span[0]:inner.span[1]] == '(and a b)'


# ---- Error cases -----------------------------------------------------------


def test_stray_rparen_errors() -> None:
    with pytest.raises(Smt2ParseError) as exc_info:
        parse_sexprs(')')
    assert exc_info.value.pos == 0


def test_unterminated_list_errors() -> None:
    with pytest.raises(Smt2ParseError) as exc_info:
        parse_sexprs('(and x y')
    # The error should reference the position of the unclosed `(`
    assert exc_info.value.pos == 0


def test_unterminated_nested_list_errors() -> None:
    with pytest.raises(Smt2ParseError):
        parse_sexprs('(a (b c)')


# ---- head_text convenience -------------------------------------------------


def test_head_text_for_atom_head() -> None:
    nodes = parse_sexprs('(foo a b)')
    assert nodes[0].head_text == 'foo'


def test_head_text_none_for_list_head() -> None:
    # First child is a list, not an atom — head_text returns None
    nodes = parse_sexprs('((foo) a)')
    assert nodes[0].head_text is None


def test_head_text_none_for_empty_list() -> None:
    nodes = parse_sexprs('()')
    assert nodes[0].head_text is None
