import pytest

import ttac_fixtures as fx
from ctac.ttac import ast, parse_program


@pytest.mark.parametrize("name", sorted(fx.ALL))
def test_doc_examples_parse(name):
    prog = parse_program(fx.ALL[name])
    assert prog.blocks


def test_core_program_structure():
    prog = parse_program(fx.CORE)
    labels = [b.label for b in prog.blocks]
    assert labels == ["entry", "ok", "bad", "exit"]
    assert prog.entry == "entry"
    assert prog.exit == "exit"


def test_entry_terminator_is_if_goto():
    prog = parse_program(fx.CORE)
    entry = prog.blocks[0]
    assert entry.terminator == ast.IfGoto("c", "ok", "bad")


def test_halt_and_goto_terminators():
    prog = parse_program(fx.CORE)
    by_label = {b.label: b for b in prog.blocks}
    assert by_label["ok"].terminator == ast.Goto("exit")
    assert by_label["bad"].terminator == ast.Halt()
    assert by_label["exit"].terminator == ast.Halt()


def test_entry_resolution_falls_back_to_first_block():
    prog = parse_program("start:\n  x := havoc\n  halt\n")
    assert prog.entry == "start"
    assert prog.exit is None


def test_lowered_form_uses_ref_records():
    prog = parse_program(fx.MUT_BORROW_LOWERED)
    entry = prog.blocks[0]
    record_assign = entry.commands[2]
    assert isinstance(record_assign, ast.Assign)
    assert isinstance(record_assign.rhs, ast.Record)
    assert record_assign.rhs.promise == ast.HavocExpr()


def test_missing_terminator_is_error():
    from ctac.ttac.errors import TtacParseError

    with pytest.raises(TtacParseError, match="no terminator"):
        parse_program("entry:\n  x := havoc\n")
