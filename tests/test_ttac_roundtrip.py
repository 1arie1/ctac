import pytest

import ttac_fixtures as fx
from ctac.ttac import parse_program, pretty


@pytest.mark.parametrize("name", sorted(fx.ALL))
def test_pretty_reparses_to_equal_ast(name):
    prog = parse_program(fx.ALL[name])
    assert parse_program(pretty(prog)) == prog


@pytest.mark.parametrize("name", sorted(fx.ALL))
def test_pretty_is_idempotent(name):
    prog = parse_program(fx.ALL[name])
    once = pretty(prog)
    twice = pretty(parse_program(once))
    assert once == twice


def test_precedence_parens_preserved_through_roundtrip():
    src = "entry:\n  z := (a or b) and not (c == d)\n  halt\n"
    prog = parse_program(src)
    assert parse_program(pretty(prog)) == prog
