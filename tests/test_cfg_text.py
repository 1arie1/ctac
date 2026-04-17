from __future__ import annotations

from ctac.graph import iter_cfg_dot, iter_cfg_lines
from ctac.parse import parse_string

from test_parse_minimal import MINIMAL_TAC

TAC_DOT_FEATURES = """TACSymbolTable {
	UserDefined {
	}
	BuiltinFunctions {
	}
	UninterpretedFunctions {
	}
	x:bv256
}
Program {
	Block entry Succ [exit] {
		AnnotationCmd JSON{"key":{"name":"snippet.cmd"},"value":{"#class":"x.CexPrintTag","displayMessage":"m"}}
		AssignExpCmd:77 x 0x1
	}
	Block exit Succ [] {
		AssertCmd:88 true "bad"
	}
}
Axioms {
}
Metas {
  "77": [{"key": {"name": "cvl.range"}, "value": {"specFile": "/path/spec.spec", "start": {"line": 3}}}],
  "88": []
}
"""


def test_cfg_goto_minimal() -> None:
    tac = parse_string(MINIMAL_TAC, path="<string>")
    lines = list(iter_cfg_lines(tac.program, style="goto", check_refs=True))
    text = "\n".join(lines)
    assert "entry:" in text
    assert "goto exit, loop" in text
    assert "loop:" in text
    assert "goto entry" in text
    assert "exit:" in text
    assert "stop" in text


def test_cfg_edges_minimal() -> None:
    tac = parse_string(MINIMAL_TAC, path="<string>")
    lines = list(iter_cfg_lines(tac.program, style="edges"))
    assert "entry -> exit" in lines
    assert "entry -> loop" in lines
    assert "loop -> entry" in lines


def test_cfg_max_blocks_truncation() -> None:
    tac = parse_string(MINIMAL_TAC, path="<string>")
    lines = list(iter_cfg_lines(tac.program, style="goto", max_blocks=1))
    assert any("truncated" in ln for ln in lines)


def test_cfg_dot_shape_and_colors() -> None:
    tac = parse_string(TAC_DOT_FEATURES, path="<string>")
    lines = list(iter_cfg_dot(tac.program, tac.metas))
    text = "\n".join(lines)
    assert "digraph cfg" in text
    assert "entry -> exit" in text
    assert 'fillcolor="#b3e5fc"' in text  # clog (entry)
    assert 'fillcolor="#ffcdd2"' in text  # assert (exit)


def test_cfg_dot_tooltip_source_lines() -> None:
    tac = parse_string(TAC_DOT_FEATURES, path="<string>")
    lines = list(iter_cfg_dot(tac.program, tac.metas))
    text = "\n".join(lines)
    assert "tooltip=" in text
    assert "spec.spec:3" in text


def test_cfg_dot_quotes_leading_digit_block_ids() -> None:
    tac = parse_string(
        """TACSymbolTable {
}
Program {
	Block 0_0 Succ [1_0] {
		JumpCmd 1_0
	}
	Block 1_0 Succ [] {
	}
}
Axioms {
}
Metas {
  "0": []
}
""",
        path="<string>",
    )
    lines = list(iter_cfg_dot(tac.program, tac.metas))
    text = "\n".join(lines)
    assert '"0_0"' in text
    assert '"1_0"' in text
    assert '"0_0" -> "1_0"' in text
