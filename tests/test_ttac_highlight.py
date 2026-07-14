from ctac.ttac.highlight import highlight_line


def _styles(line):
    return {s.style for s in highlight_line(line).spans}


def test_plain_text_preserved():
    line = "  c := y <= limit"
    assert highlight_line(line).plain == line


def test_keyword_and_operators():
    s = _styles("  assume not c")
    assert "ttac.keyword" in s  # assume / not


def test_label_header():
    assert "ttac.label" in _styles("entry:")


def test_if_goto_terminator():
    s = _styles("  if c goto ok else bad")
    assert "ttac.control" in s  # if / else
    assert "ttac.keyword" in s  # goto
    assert "ttac.block" in s  # ok / bad targets


def test_type_annotation_and_number():
    s = _styles("  x: int := havoc")
    assert "ttac.type" in s  # int
    assert "ttac.keyword" in s  # havoc
    s2 = _styles("  r2 := put_ref r, 7")
    assert "ttac.number" in s2  # 7
    assert "ttac.keyword" in s2  # put_ref


def test_borrow_mut_not_split_as_borrow():
    # `borrow_mut` highlights as one keyword token, not `borrow` + `_mut`.
    line = "  r, M2 := borrow_mut M[i]"
    spans = [s for s in highlight_line(line).spans if s.style == "ttac.keyword"]
    matched = {line[s.start:s.end] for s in spans}
    assert "borrow_mut" in matched
