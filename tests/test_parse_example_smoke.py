from __future__ import annotations

from pathlib import Path

import pytest

from ctac.parse import parse_path

EXAMPLE = Path(__file__).resolve().parents[1] / "examples/EmvOutput1/outputs/PresolverRule-liquidity_solvency_operate_borrow.tac"


@pytest.mark.skipif(not EXAMPLE.is_file(), reason="example .tac not in tree")
def test_parse_presolver_example() -> None:
    tac = parse_path(EXAMPLE)
    assert tac.path == str(EXAMPLE)
    assert len(tac.program.blocks) > 10
    assert sum(len(b.commands) for b in tac.program.blocks) > 100
    assert len(tac.metas) > 0
    entry = tac.program.blocks[0]
    assert entry.id == "0_0_0_0_0_0"
    assert len(entry.successors) >= 1
