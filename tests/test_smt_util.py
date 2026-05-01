from __future__ import annotations

from ctac.smt.util import iff, not_term


def test_not_term_simplifies_literals() -> None:
    assert not_term("true") == "false"
    assert not_term("false") == "true"
    assert not_term("P") == "(not P)"


def test_iff_simplifies_bool_literal_cases() -> None:
    assert iff("P", "P") == "true"
    assert iff("true", "P") == "P"
    assert iff("P", "true") == "P"
    assert iff("false", "P") == "(not P)"
    assert iff("P", "false") == "(not P)"
    assert iff("false", "false") == "true"
    assert iff("true", "false") == "false"
    assert iff("false", "true") == "false"


def test_iff_keeps_nontrivial_equivalence_as_equality() -> None:
    assert iff("P", "Q") == "(= P Q)"
