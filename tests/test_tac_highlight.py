from __future__ import annotations

from ctac.tool.highlight import highlight_tac_line


def _styles(line: str) -> set[str]:
    text = highlight_tac_line(line)
    return {span.style for span in text.spans}


def test_highlight_pp_line_tokens() -> None:
    styles = _styles("  assume R10 == 0x2")
    assert "ctac.keyword" in styles
    assert "ctac.symbol" in styles
    assert "ctac.number" in styles
    assert "ctac.operator" in styles


def test_highlight_trace_assignment_tokens() -> None:
    styles = _styles("R1 = narrow(R2 + 10)")
    assert "ctac.symbol" in styles
    assert "ctac.function" in styles
    assert "ctac.number" in styles
    assert "ctac.operator" in styles


def test_highlight_goto_block_ids_not_as_numbers() -> None:
    styles = _styles("  goto 50_1_0_0_0_0, 34_1_0_0_0_0")
    assert "ctac.block" in styles
    assert "ctac.number" not in styles

