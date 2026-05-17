"""Tests for ctac.solver.smt2.ops (file-level transformations)."""
from __future__ import annotations

import re

from ctac.solver.smt2 import (
    Assert,
    DeclareFun,
    DefineFun,
    append_assert,
    emit,
    memory_abstract,
    name_asserts,
    parse,
    scan_uf_arguments,
    strip_check_sat,
)


# ---- memory_abstract -------------------------------------------------------


def test_memory_abstract_basic() -> None:
    src = """(declare-fun M0 (Int) Int)
(define-fun M1 ((idx Int)) Int (ite (= idx 1) 10 (M0 idx)))
(define-fun M2 ((idx Int)) Int (ite (= idx 2) 20 (M1 idx)))
(declare-const x Int)
(assert (= (M2 x) 30))
(check-sat)
"""
    f = parse(src)
    f2 = memory_abstract(f, re.compile(r'^M\w+$'))
    # Two define-fun chain links became declare-fun
    n_declare_M = sum(1 for s in f2.statements
                       if isinstance(s, DeclareFun)
                       and s.name.startswith('M'))
    n_define_M = sum(1 for s in f2.statements
                      if isinstance(s, DefineFun)
                      and s.name.startswith('M'))
    assert n_declare_M == 3   # M0 was already declare-fun + M1 + M2
    assert n_define_M == 0


def test_memory_abstract_skips_non_chain_define_fun() -> None:
    """define-fun with non-Int-to-Int signature should NOT be abstracted."""
    src = """(declare-fun M0 (Int) Int)
(define-fun helper ((x Int) (y Int)) Int (+ x y))
(define-fun M1 ((idx Int)) Int (ite (= idx 1) 10 (M0 idx)))
(check-sat)
"""
    f = parse(src)
    f2 = memory_abstract(f, re.compile(r'^M\w+$'))
    # helper is untouched (wrong signature shape)
    helper_kept = any(isinstance(s, DefineFun) and s.name == 'helper'
                       for s in f2.statements)
    assert helper_kept


def test_memory_abstract_no_op_when_nothing_matches() -> None:
    src = '(declare-const x Int)\n(check-sat)\n'
    f = parse(src)
    f2 = memory_abstract(f, re.compile(r'^M\w+$'))
    # No changes — returned file is the same object
    assert emit(f2) == src


# ---- strip_check_sat -------------------------------------------------------


def test_strip_check_sat_removes_trailing_check_and_after() -> None:
    src = """(declare-const x Int)
(assert (> x 0))
(check-sat)
(get-model)
"""
    f = parse(src)
    f2 = strip_check_sat(f)
    kinds = [type(s).__name__ for s in f2.statements]
    assert 'CheckSat' not in kinds
    # everything before check-sat is preserved
    assert 'DeclareConst' in kinds
    assert 'Assert' in kinds


def test_strip_check_sat_no_check_sat() -> None:
    f = parse('(declare-const x Int)\n')
    f2 = strip_check_sat(f)
    # Nothing changes
    assert len(f2.statements) == 1


# ---- name_asserts ----------------------------------------------------------


def test_name_asserts_wraps_with_named() -> None:
    src = '(assert (> x 0))\n(assert (< x 10))\n'
    f = parse(src)
    f2, index = name_asserts(f, picker=lambda s, i: f'fact_{i}')
    names = [s.named for s in f2.statements if isinstance(s, Assert)]
    assert names == ['fact_0', 'fact_1']
    assert set(index.keys()) == {'fact_0', 'fact_1'}


def test_name_asserts_skips_when_picker_returns_none() -> None:
    src = '(assert a)\n(assert b)\n(assert c)\n'
    f = parse(src)
    # Only name the middle assert
    def picker(stmt: Assert, idx: int) -> str | None:
        return 'middle' if idx == 1 else None

    f2, index = name_asserts(f, picker=picker)
    names = [s.named for s in f2.statements if isinstance(s, Assert)]
    assert names == [None, 'middle', None]
    assert list(index.keys()) == ['middle']


# ---- scan_uf_arguments -----------------------------------------------------


def test_scan_uf_arguments_basic() -> None:
    src = """(declare-const x Int)
(declare-const y Int)
(declare-fun M0 (Int) Int)
(define-fun M1 ((idx Int)) Int (ite (= idx 1) 99 (M0 idx)))
(assert (= (M1 x) (M1 y)))
(check-sat)
"""
    f = parse(src)
    T = scan_uf_arguments(f, re.compile(r'^M\w+$'))
    # M1 is read with args x and y; M0 is read only inside its chain
    # link's body (skipped because that body is chain-internal).
    assert 'M1' in T
    assert sorted(T['M1']) == ['x', 'y']


def test_scan_uf_arguments_filters_undeclared() -> None:
    src = """(declare-const x Int)
(declare-fun M (Int) Int)
(assert (= (M x) (M 42)))
"""
    f = parse(src)
    T = scan_uf_arguments(f, re.compile(r'^M$'))
    # Numeric literal 42 is excluded (symbol_only=True default)
    assert sorted(T['M']) == ['x']


def test_scan_uf_arguments_declared_only_excludes_define_consts() -> None:
    """A symbol introduced via `define-fun NAME () Int <expr>` is NOT
    `declared` and gets filtered out under declared_only=True."""
    src = """(declare-const x Int)
(define-fun POW2 () Int 65536)
(declare-fun M (Int) Int)
(assert (= (M x) (M POW2)))
"""
    f = parse(src)
    T = scan_uf_arguments(f, re.compile(r'^M$'))
    assert sorted(T['M']) == ['x']
    # With declared_only=False, both x and POW2 would appear
    T2 = scan_uf_arguments(f, re.compile(r'^M$'), declared_only=False)
    assert sorted(T2['M']) == ['POW2', 'x']


# ---- append_assert ---------------------------------------------------------


def test_append_assert_before_check_sat() -> None:
    src = '(declare-const x Int)\n(check-sat)\n'
    f = parse(src)
    f2 = append_assert(f, '(> x 0)')
    kinds = [type(s).__name__ for s in f2.statements]
    assert kinds == ['DeclareConst', 'Assert', 'CheckSat']


def test_append_assert_with_named() -> None:
    src = '(check-sat)\n'
    f = parse(src)
    f2 = append_assert(f, '(> x 0)', named='block_0')
    asserts = [s for s in f2.statements if isinstance(s, Assert)]
    assert len(asserts) == 1
    assert asserts[0].named == 'block_0'


def test_append_assert_at_end_when_no_check_sat() -> None:
    src = '(declare-const x Int)\n'
    f = parse(src)
    f2 = append_assert(f, '(> x 0)')
    assert isinstance(f2.statements[-1], Assert)


# ---- Combined: realistic alias-cover flow ---------------------------------


def test_memory_abstract_then_scan_uf() -> None:
    """memory_abstract + scan_uf_arguments composition matches the
    alias-cover prep flow."""
    src = """(declare-const R1 Int)
(declare-const R2 Int)
(declare-fun M0 (Int) Int)
(define-fun M1 ((idx Int)) Int (ite (= idx R1) 1 (M0 idx)))
(define-fun M2 ((idx Int)) Int (ite (= idx R2) 2 (M1 idx)))
(assert (= (M2 R1) (M2 R2)))
(check-sat)
"""
    f = parse(src)
    f2 = memory_abstract(f, re.compile(r'^M\w+$'))
    T = scan_uf_arguments(f2, re.compile(r'^M\w+$'))
    # After abstraction, M2 is uninterpreted; T should include the
    # symbolic indices it's applied to (R1, R2).
    assert sorted(T['M2']) == ['R1', 'R2']
