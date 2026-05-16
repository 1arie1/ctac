"""Tests for ctac.solver.smt2.parser (command-level dispatch + emit).

Per-statement-type parsing, malformed inputs, and emit byte-identical
round-trip on hand-written and corpus inputs."""
from __future__ import annotations

from pathlib import Path

import pytest

from ctac.solver.smt2 import (
    Apply,
    Assert,
    CheckSat,
    CheckSatUsing,
    Comment,
    DeclareConst,
    DeclareFun,
    DefineFun,
    Exit,
    GetInfo,
    GetModel,
    GetUnsatCore,
    GetValue,
    Pop,
    Push,
    Raw,
    SetLogic,
    SetOption,
    emit,
    parse,
)
from ctac.solver.smt2.sexpr import Atom, List_, Smt2ParseError


# ---- Per-statement parsing -------------------------------------------------


def test_set_logic() -> None:
    f = parse('(set-logic QF_UFNIA)')
    assert len(f.statements) == 1
    s = f.statements[0]
    assert isinstance(s, SetLogic)
    assert s.logic == 'QF_UFNIA'


def test_set_option_simple_value() -> None:
    f = parse('(set-option :produce-unsat-cores true)')
    s = f.statements[0]
    assert isinstance(s, SetOption)
    assert s.key == ':produce-unsat-cores'
    assert isinstance(s.value_node, Atom)
    assert s.value_node.text == 'true'


def test_set_option_compound_value() -> None:
    f = parse('(set-option :smt.tactic (then simplify smt))')
    s = f.statements[0]
    assert isinstance(s, SetOption)
    assert isinstance(s.value_node, List_)
    assert s.value_node.head_text == 'then'


def test_declare_const() -> None:
    f = parse('(declare-const R633 Int)')
    s = f.statements[0]
    assert isinstance(s, DeclareConst)
    assert s.name == 'R633'
    assert isinstance(s.sort_node, Atom)
    assert s.sort_node.text == 'Int'


def test_declare_const_compound_sort() -> None:
    f = parse('(declare-const M (Array Int Int))')
    s = f.statements[0]
    assert isinstance(s, DeclareConst)
    assert isinstance(s.sort_node, List_)


def test_declare_fun() -> None:
    f = parse('(declare-fun M (Int) Int)')
    s = f.statements[0]
    assert isinstance(s, DeclareFun)
    assert s.name == 'M'
    assert len(s.param_sorts) == 1
    assert isinstance(s.param_sorts[0], Atom)
    assert s.param_sorts[0].text == 'Int'
    assert isinstance(s.ret_sort_node, Atom)
    assert s.ret_sort_node.text == 'Int'


def test_declare_fun_empty_params() -> None:
    f = parse('(declare-fun x () Int)')
    s = f.statements[0]
    assert isinstance(s, DeclareFun)
    assert s.name == 'x'
    assert s.param_sorts == []


def test_define_fun_chain_link() -> None:
    src = '(define-fun M179 ((idx Int)) Int (ite (= idx 42) 1 (M178 idx)))'
    f = parse(src)
    s = f.statements[0]
    assert isinstance(s, DefineFun)
    assert s.name == 'M179'
    assert len(s.params) == 1
    assert s.params[0].name == 'idx'
    assert isinstance(s.params[0].sort_node, Atom)
    assert s.params[0].sort_node.text == 'Int'
    assert isinstance(s.ret_sort_node, Atom)
    assert s.ret_sort_node.text == 'Int'
    assert isinstance(s.body, List_)
    assert s.body.head_text == 'ite'


def test_assert_bare() -> None:
    f = parse('(assert (= x y))')
    s = f.statements[0]
    assert isinstance(s, Assert)
    assert s.named is None
    assert isinstance(s.body, List_)


def test_assert_with_named() -> None:
    f = parse('(assert (! (= x y) :named my_fact))')
    s = f.statements[0]
    assert isinstance(s, Assert)
    assert s.named == 'my_fact'
    # body is the inner expression, NOT the (! ...) wrapper
    assert isinstance(s.body, List_)
    assert s.body.head_text == '='


def test_assert_with_named_and_other_attrs() -> None:
    # Other attributes (like :pattern) are ignored; :named is extracted
    f = parse('(assert (! (= x y) :pattern z :named my_fact))')
    s = f.statements[0]
    assert isinstance(s, Assert)
    assert s.named == 'my_fact'


def test_check_sat() -> None:
    f = parse('(check-sat)')
    assert isinstance(f.statements[0], CheckSat)


def test_check_sat_using() -> None:
    f = parse('(check-sat-using (then simplify smt))')
    s = f.statements[0]
    assert isinstance(s, CheckSatUsing)
    assert isinstance(s.tactic_node, List_)
    assert s.tactic_node.head_text == 'then'


def test_apply_command() -> None:
    f = parse('(apply (then simplify smt))')
    assert isinstance(f.statements[0], Apply)


def test_get_model() -> None:
    f = parse('(get-model)')
    assert isinstance(f.statements[0], GetModel)


def test_get_info() -> None:
    f = parse('(get-info :reason-unknown)')
    s = f.statements[0]
    assert isinstance(s, GetInfo)
    assert s.info_keyword == ':reason-unknown'


def test_get_value() -> None:
    f = parse('(get-value (x y (+ x 1)))')
    s = f.statements[0]
    assert isinstance(s, GetValue)
    assert len(s.args) == 3


def test_get_unsat_core() -> None:
    f = parse('(get-unsat-core)')
    assert isinstance(f.statements[0], GetUnsatCore)


def test_push_pop_default_n() -> None:
    f = parse('(push) (pop)')
    assert isinstance(f.statements[0], Push)
    assert f.statements[0].n == 1
    assert isinstance(f.statements[1], Pop)
    assert f.statements[1].n == 1


def test_push_pop_explicit_n() -> None:
    f = parse('(push 3) (pop 2)')
    assert f.statements[0].n == 3
    assert f.statements[1].n == 2


def test_exit() -> None:
    f = parse('(exit)')
    assert isinstance(f.statements[0], Exit)


def test_comment_block_as_statement() -> None:
    f = parse('; just a comment\n')
    s = f.statements[0]
    assert isinstance(s, Comment)
    assert s.lines == ['; just a comment']


def test_unknown_top_level_falls_through_to_raw() -> None:
    # Not a recognized command, but valid s-expr — wraps as Raw
    f = parse('(some-unknown-cmd a b)')
    s = f.statements[0]
    assert isinstance(s, Raw)


# ---- Error cases -----------------------------------------------------------


def test_set_logic_arity_error() -> None:
    with pytest.raises(Smt2ParseError):
        parse('(set-logic)')


def test_declare_const_arity_error() -> None:
    with pytest.raises(Smt2ParseError):
        parse('(declare-const)')


def test_define_fun_arity_error() -> None:
    with pytest.raises(Smt2ParseError):
        parse('(define-fun)')


def test_define_fun_malformed_param_errors() -> None:
    # A param must be `(name sort)`, not bare name
    with pytest.raises(Smt2ParseError):
        parse('(define-fun M (idx) Int 0)')


def test_get_info_requires_keyword() -> None:
    with pytest.raises(Smt2ParseError):
        parse('(get-info not-a-keyword)')


# ---- Multi-statement files -------------------------------------------------


def test_multi_statement_file() -> None:
    src = """; header
(set-logic QF_UFNIA)
(declare-const x Int)
(assert (> x 0))
(check-sat)
"""
    f = parse(src)
    kinds = [type(s).__name__ for s in f.statements]
    assert kinds == ['Comment', 'SetLogic', 'DeclareConst', 'Assert', 'CheckSat']


# ---- Emit round-trip -------------------------------------------------------


def test_emit_byte_identical_simple() -> None:
    src = """; header
(set-logic QF_UFNIA)
(declare-const x Int)
(assert (> x 0))
(check-sat)
"""
    f = parse(src)
    assert emit(f) == src


@pytest.mark.parametrize('rel_path', [
    'examples/bad_2/auto-split/splits/cover/cluster_02/v.smt2',
    'examples/bad_2/auto-split/artifacts/path9_diagnosis/p9_orig.smt2',
    'examples/bad_2/auto-split/artifacts/path9_diagnosis/p9_abstract.smt2',
])
def test_emit_round_trip_on_corpus(rel_path: str) -> None:
    """Round-trip on real corpus files: emit must be byte-identical."""
    root = Path(__file__).resolve().parents[1]
    p = root / rel_path
    if not p.exists():
        pytest.skip(f'corpus file not present: {rel_path}')
    src = p.read_text()
    f = parse(p)
    assert emit(f) == src, f'round-trip failed for {rel_path}'


def test_emit_preserves_blank_lines_and_comments() -> None:
    src = """; first comment
(set-logic QF_UFNIA)

; second comment after blank line
(declare-const x Int)
(check-sat)
"""
    f = parse(src)
    assert emit(f) == src


def test_emit_after_modification_uses_pp() -> None:
    """Modified statements re-render via pp; unchanged stay source-sliced."""
    src = '(declare-const x Int)\n(assert (> x 0))\n(check-sat)\n'
    f = parse(src)
    # Mark the assert dirty so emit re-renders it (the body stays the same;
    # this just exercises the dirty path)
    f.statements[1].dirty = True
    out = emit(f)
    # Should still contain the same essential content
    assert '(declare-const x Int)' in out
    assert '(assert' in out
    assert '(check-sat)' in out
