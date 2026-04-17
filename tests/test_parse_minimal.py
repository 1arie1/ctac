from __future__ import annotations

from ctac.parse import parse_string


MINIMAL_TAC = """TACSymbolTable {
	UserDefined {
	}
	BuiltinFunctions {
	}
	UninterpretedFunctions {
	}
	x:bv256
}
Program {
	Block entry Succ [exit, loop] {
		AssignExpCmd x 0x1
		LabelCmd "start"
	}
	Block loop Succ [entry] {
		AssignExpCmd x 0x2
	}
	Block exit Succ [] {
	}
}
Axioms {
}
Metas {
  "0": []
}
"""


def test_parse_minimal_structure() -> None:
    tac = parse_string(MINIMAL_TAC, path="<string>")
    assert "TACSymbolTable" in tac.symbol_table_text
    assert "x:bv256" in tac.symbol_table_text
    assert tac.path == "<string>"

    by = tac.program.block_by_id()
    assert set(by) == {"entry", "loop", "exit"}
    assert by["entry"].successors == ["exit", "loop"]
    assert by["loop"].successors == ["entry"]
    assert by["exit"].successors == []
    assert len(by["entry"].commands) == 2
    assert by["entry"].commands[0].raw == "AssignExpCmd x 0x1"
    assert "Axioms" in tac.axioms_text
    assert tac.metas == {"0": []}
