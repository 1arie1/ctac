from __future__ import annotations

from ctac.tool.main import _truncate_diff_lines


def test_truncate_diff_lines_no_truncation() -> None:
    lines = ["a", "b", "c"]
    kept, omitted = _truncate_diff_lines(lines, 5)
    assert kept == lines
    assert omitted == 0


def test_truncate_diff_lines_with_truncation() -> None:
    lines = [f"ln-{i}" for i in range(10)]
    kept, omitted = _truncate_diff_lines(lines, 4)
    assert kept == ["ln-0", "ln-1", "ln-2", "ln-3"]
    assert omitted == 6

