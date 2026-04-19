from __future__ import annotations

from pathlib import Path

from ctac.ast.nodes import ApplyExpr, AssignExpCmd, AssignHavocCmd, AssumeExpCmd, JumpCmd, JumpiCmd
from ctac.graph import iter_cfg_lines
from ctac.parse import parse_path, parse_sbf_string


SBF_MINIMAL = """{
  "name": "mini",
  "entry": "B0",
  "exit": "B2",
  "blocks": [
    {
      "label": "B1",
      "predecessors": [],
      "successors": ["B2"],
      "instructions": [
        {"inst": "r1:num(0) = 0 /* 0x10 */", "meta": 1},
        {"inst": "goto B2", "meta": 2}
      ]
    },
    {
      "label": "B0",
      "predecessors": [],
      "successors": ["B1", "B2"],
      "instructions": [
        {"inst": "r3 = havoc()", "meta": 10},
        {"inst": "r2 = select(r3 == 0, r1:num(0), 7) /* comment */", "meta": 11},
        {"inst": "assume(r2 sge -1)", "meta": 12},
        {"inst": "if (r2 == 7) then goto B2 else goto B1", "meta": 13}
      ]
    },
    {
      "label": "B2",
      "predecessors": [],
      "successors": [],
      "instructions": [
        {"inst": "exit", "meta": 20}
      ]
    }
  ],
  "meta": {
    "11": {"sbf_bytecode_address": 16}
  }
}"""


def test_parse_sbf_select_and_basic_shapes() -> None:
    tac = parse_sbf_string(SBF_MINIMAL, path="<sbf>")
    assert tac.path == "<sbf>"
    assert tac.program.blocks[0].id == "B0"  # reordered to declared entry

    by = tac.program.block_by_id()
    b0_cmds = by["B0"].commands
    assert isinstance(b0_cmds[0], AssignHavocCmd)
    assert isinstance(b0_cmds[1], AssignExpCmd)
    assert isinstance(b0_cmds[2], AssumeExpCmd)
    assert isinstance(b0_cmds[3], JumpiCmd)

    select_cmd = b0_cmds[1]
    assert isinstance(select_cmd, AssignExpCmd)
    assert isinstance(select_cmd.rhs, ApplyExpr)
    assert select_cmd.rhs.op == "Ite"

    b1_cmds = by["B1"].commands
    assert isinstance(b1_cmds[1], JumpCmd)


def test_parse_path_autodetects_sbf_json(tmp_path: Path) -> None:
    p = tmp_path / "sample.sbf.json"
    p.write_text(SBF_MINIMAL, encoding="utf-8")
    tac = parse_path(p)
    assert tac.path == str(p)
    assert tac.program.blocks[0].id == "B0"
    assert len(tac.program.blocks) == 3


def test_sbf_program_works_with_cfg_text_views() -> None:
    tac = parse_sbf_string(SBF_MINIMAL)
    lines = list(iter_cfg_lines(tac.program, style="edges"))
    assert "B0 -> B1" in lines
    assert "B0 -> B2" in lines
    assert "B1 -> B2" in lines
