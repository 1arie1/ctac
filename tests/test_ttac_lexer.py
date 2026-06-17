from ctac.ttac.lexer import tokenize


def _kinds(src):
    return [t.kind for t in tokenize(src)]


def _values(src):
    return [(t.kind, t.value) for t in tokenize(src) if t.kind not in ("NEWLINE", "EOF")]


def test_two_char_operators_maximal_munch():
    vals = _values("x := y == z <= w")
    assert vals == [
        ("NAME", "x"),
        (":=", ":="),
        ("NAME", "y"),
        ("==", "=="),
        ("NAME", "z"),
        ("<=", "<="),
        ("NAME", "w"),
    ]


def test_single_char_punctuation():
    assert _values("M[i := v].value") == [
        ("NAME", "M"),
        ("[", "["),
        ("NAME", "i"),
        (":=", ":="),
        ("NAME", "v"),
        ("]", "]"),
        (".", "."),
        ("NAME", "value"),
    ]


def test_integer_literal():
    assert _values("7 + 100") == [("INT", "7"), ("+", "+"), ("INT", "100")]


def test_newline_collapse_and_terminators():
    kinds = _kinds("a\n\n\nb")
    # leading/internal blank lines collapse; trailing NEWLINE before EOF.
    assert kinds == ["NAME", "NEWLINE", "NAME", "NEWLINE", "EOF"]


def test_line_comment_skipped():
    assert _values("x := 1 // trailing comment\n") == [
        ("NAME", "x"),
        (":=", ":="),
        ("INT", "1"),
    ]


def test_position_tracking():
    toks = tokenize("ab := 3")
    assert (toks[0].line, toks[0].col) == (1, 1)
    assert (toks[1].line, toks[1].col) == (1, 4)
    assert (toks[2].line, toks[2].col) == (1, 7)
