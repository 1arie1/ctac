from __future__ import annotations

from ctac.graph import iter_cfg_lines
from ctac.parse import parse_string

from test_parse_minimal import MINIMAL_TAC


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
