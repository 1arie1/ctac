"""Tests for ctac.solver.smt2.pp (pretty-printer + Doc algebra)."""
from __future__ import annotations

from ctac.solver.smt2 import parse, pp, PpPolicy
from ctac.solver.smt2.doc import (
    concat,
    group,
    line,
    nest,
    render,
    text,
)
from ctac.solver.smt2.pp import pp_sexpr
from ctac.solver.smt2.sexpr import parse_sexprs


# ---- Doc algebra primitives ------------------------------------------------


def test_doc_text_renders_verbatim() -> None:
    assert render(text('hello'), width=80) == 'hello'


def test_doc_concat() -> None:
    d = concat([text('foo'), text(' '), text('bar')])
    assert render(d, width=80) == 'foo bar'


def test_doc_group_flat_when_fits() -> None:
    d = group(concat([text('('), text('and'), line(), text('x'),
                       line(), text('y'), text(')')]))
    out = render(d, width=80)
    assert out == '(and x y)'


def test_doc_group_breaks_when_too_wide() -> None:
    d = group(concat([text('('), text('and'), line(), text('x'),
                       line(), text('y'), text(')')]))
    out = render(d, width=5)
    # When broken, soft lines become newlines + indent
    assert '\n' in out


def test_doc_nest_indents_after_break() -> None:
    d = group(concat([text('head'),
                       nest(4, concat([line(), text('arg')]))]))
    flat = render(d, width=80)
    assert flat == 'head arg'
    broken = render(d, width=2)
    # Broken: newline + 4 spaces indent before 'arg'
    assert broken == 'head\n    arg'


# ---- pp_sexpr on simple S-exprs -------------------------------------------


def test_pp_atom() -> None:
    nodes = parse_sexprs('foo')
    out = render(pp_sexpr(nodes[0]), width=80)
    assert out == 'foo'


def test_pp_short_form_stays_flat() -> None:
    nodes = parse_sexprs('(and x y)')
    out = render(pp_sexpr(nodes[0]), width=80)
    assert out == '(and x y)'


def test_pp_long_form_breaks() -> None:
    nodes = parse_sexprs('(and aaaaaaaaaaaa bbbbbbbbbbbb cccccccccccc)')
    out = render(pp_sexpr(nodes[0]), width=20)
    assert '\n' in out
    # All three args should appear, one per line in broken form
    assert 'aaaaaaaaaaaa' in out
    assert 'bbbbbbbbbbbb' in out
    assert 'cccccccccccc' in out


def test_pp_nested_groups() -> None:
    # Inner stays flat, outer breaks
    src = '(and (or short_a short_b) (= ' + 'long_arg_x ' * 5 + 'long_arg_y))'
    nodes = parse_sexprs(src)
    out = render(pp_sexpr(nodes[0]), width=40)
    # Outer must break (way too wide)
    assert '\n' in out


# ---- File-level pp -------------------------------------------------------


def test_pp_file_includes_set_logic_check_sat() -> None:
    src = """(set-logic QF_UFNIA)
(declare-const x Int)
(assert (> x 0))
(check-sat)
"""
    f = parse(src)
    out = pp(f, PpPolicy(width=100))
    assert '(set-logic QF_UFNIA)' in out
    assert '(declare-const x Int)' in out
    assert '(check-sat)' in out


def test_pp_preserves_named_annotation() -> None:
    src = '(assert (! (= x 1) :named my_fact))'
    f = parse(src)
    out = pp(f, PpPolicy(width=100))
    assert ':named my_fact' in out


def test_pp_show_comments_default_true() -> None:
    f = parse('; my comment\n(check-sat)\n')
    out = pp(f, PpPolicy(width=100))
    assert '; my comment' in out


def test_pp_show_comments_false() -> None:
    f = parse('; my comment\n(check-sat)\n')
    out = pp(f, PpPolicy(width=100, show_comments=False))
    assert '; my comment' not in out


def test_pp_width_affects_breaking() -> None:
    src = '(assert (and aaaaaaaaaa bbbbbbbbbb cccccccccc dddddddddd))'
    f = parse(src)
    wide = pp(f, PpPolicy(width=200))
    narrow = pp(f, PpPolicy(width=20))
    # Wide stays mostly on one line; narrow has more newlines
    assert wide.count('\n') < narrow.count('\n')


def test_pp_check_sat_using_with_tactic() -> None:
    f = parse('(check-sat-using (then simplify smt))')
    out = pp(f, PpPolicy(width=100))
    assert '(check-sat-using' in out
    assert 'then' in out


def test_pp_get_info() -> None:
    f = parse('(get-info :reason-unknown)')
    out = pp(f, PpPolicy(width=100))
    assert out.strip() == '(get-info :reason-unknown)'


def test_pp_get_value() -> None:
    f = parse('(get-value (x y))')
    out = pp(f, PpPolicy(width=100))
    assert '(get-value' in out
    assert 'x' in out and 'y' in out


def test_pp_push_pop() -> None:
    f = parse('(push) (pop 3)')
    out = pp(f, PpPolicy(width=100))
    assert '(push)' in out
    assert '(pop 3)' in out


def test_pp_exit() -> None:
    f = parse('(exit)')
    out = pp(f, PpPolicy(width=100))
    assert out.strip() == '(exit)'
