import pytest

from ctac.ttac import parse_program
from ctac.ttac.errors import TtacParseError
from ctac.ttac.lexer import tokenize


def test_unexpected_character():
    with pytest.raises(TtacParseError) as exc:
        tokenize("x := y @ z")
    assert exc.value.line == 1
    assert "@" in str(exc.value)


def test_missing_assignment_marker():
    with pytest.raises(TtacParseError, match="':='"):
        parse_program("entry:\n  x y\n  halt\n")


def test_unterminated_record():
    with pytest.raises(TtacParseError):
        parse_program("entry:\n  r := { addr: i, value: v }\n  halt\n")


def test_unknown_record_field():
    with pytest.raises(TtacParseError, match="record field"):
        parse_program("entry:\n  r := { addr: i, val: v, promise: p }\n  halt\n")


def test_keyword_in_expression_position():
    with pytest.raises(TtacParseError, match="unexpected keyword"):
        parse_program("entry:\n  x := release + 1\n  halt\n")


def test_error_position_points_at_offending_token():
    with pytest.raises(TtacParseError) as exc:
        parse_program("entry:\n  x := \n  halt\n")
    # The empty RHS error surfaces on line 2.
    assert exc.value.line == 2


def test_with_caret_renders_source_line():
    source = "entry:\n  x := y @ z\n  halt\n"
    try:
        parse_program(source)
    except TtacParseError as exc:
        rendered = exc.with_caret(source)
        assert "^" in rendered
    else:
        raise AssertionError("expected a parse error")
