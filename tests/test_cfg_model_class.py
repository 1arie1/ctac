from __future__ import annotations

from ctac.graph import Cfg, CfgFilter
from ctac.parse import parse_string

from test_parse_minimal import MINIMAL_TAC


def test_cfg_class_filter_and_iter_lines() -> None:
    tac = parse_string(MINIMAL_TAC, path='<string>')
    cfg = Cfg(tac.program)
    sub, warnings = cfg.filtered(CfgFilter(from_id='entry', to_id='loop'))
    assert warnings == []
    assert [b.id for b in sub.blocks] == ['entry', 'loop']
    lines = list(sub.iter_lines(style='edges'))
    assert 'entry -> loop' in lines
