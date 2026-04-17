from __future__ import annotations

from ctac.graph import Cfg, CfgFilter
from ctac.parse import parse_string


SHUFFLED_DAG_TAC = """TACSymbolTable {
	UserDefined {
	}
	BuiltinFunctions {
	}
	UninterpretedFunctions {
	}
	x:bv256
}
Program {
	Block C Succ [] {
		AssignExpCmd x 0x3
	}
	Block A Succ [B] {
		AssignExpCmd x 0x1
	}
	Block B Succ [C] {
		AssignExpCmd x 0x2
	}
}
Axioms {
}
Metas {
  "0": []
}
"""


def test_cfg_iter_lines_uses_topological_order_for_dag() -> None:
    tac = parse_string(SHUFFLED_DAG_TAC, path="<dag>")
    cfg = Cfg(tac.program)
    lines = list(cfg.iter_lines(style="goto"))
    labels = [ln[:-1] for ln in lines if ln.endswith(":") and not ln.startswith("#")]
    assert labels == ["A", "B", "C"]


def test_filtered_cfg_keeps_topological_order() -> None:
    tac = parse_string(SHUFFLED_DAG_TAC, path="<dag>")
    cfg = Cfg(tac.program)
    sub, _ = cfg.filtered(CfgFilter(from_id="A", to_id="C"))
    assert [b.id for b in sub.ordered_blocks()] == ["A", "B", "C"]

