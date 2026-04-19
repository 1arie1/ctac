from __future__ import annotations

from pathlib import Path

from typer.testing import CliRunner

from ctac.tool.main import app

SBF_LEFT = """{
  "name": "left",
  "entry": "A",
  "exit": "B",
  "blocks": [
    {
      "label": "A",
      "predecessors": [],
      "successors": ["B"],
      "instructions": [
        {"inst": "r1 = havoc()", "meta": 1},
        {"inst": "r2 = select(r1 == 0, 1, 2)", "meta": 2},
        {"inst": "goto B", "meta": 3}
      ]
    },
    {
      "label": "B",
      "predecessors": ["A"],
      "successors": [],
      "instructions": [
        {"inst": "assert(r2 == 1)", "meta": 4}
      ]
    }
  ],
  "meta": {
    "1": {"sbf_bytecode_address": 1}
  }
}"""

SBF_RIGHT = """{
  "name": "right",
  "entry": "X",
  "exit": "Y",
  "blocks": [
    {
      "label": "X",
      "predecessors": [],
      "successors": ["Y"],
      "instructions": [
        {"inst": "r1 = havoc()", "meta": 1},
        {"inst": "r2 = select(r1 == 0, 1, 3)", "meta": 2},
        {"inst": "goto Y", "meta": 3}
      ]
    },
    {
      "label": "Y",
      "predecessors": ["X"],
      "successors": [],
      "instructions": [
        {"inst": "assert(r2 == 1)", "meta": 4}
      ]
    }
  ],
  "meta": {
    "1": {"sbf_bytecode_address": 2}
  }
}"""


def _write(path: Path, text: str) -> Path:
    path.write_text(text, encoding="utf-8")
    return path


def test_text_commands_accept_sbf_json(tmp_path: Path) -> None:
    left = _write(tmp_path / "left.sbf.json", SBF_LEFT)
    runner = CliRunner()

    parse_res = runner.invoke(app, ["parse", str(left), "--plain"])
    assert parse_res.exit_code == 0
    assert "blocks: 2" in parse_res.stdout

    stats_res = runner.invoke(app, ["stats", str(left), "--plain"])
    assert stats_res.exit_code == 0
    assert "commands: 4" in stats_res.stdout

    search_res = runner.invoke(app, ["search", str(left), "havoc", "--plain", "--literal"])
    assert search_res.exit_code == 0
    assert "matches: 1" in search_res.stdout

    cfg_res = runner.invoke(app, ["cfg", str(left), "--plain", "--style", "edges"])
    assert cfg_res.exit_code == 0
    assert "A -> B" in cfg_res.stdout


def test_diff_commands_accept_sbf_json(tmp_path: Path) -> None:
    left = _write(tmp_path / "left.sbf.json", SBF_LEFT)
    right = _write(tmp_path / "right.sbf.json", SBF_RIGHT)
    runner = CliRunner()

    match_res = runner.invoke(app, ["cfg-match", str(left), str(right), "--plain"])
    assert match_res.exit_code == 0
    assert "# matched: 2" in match_res.stdout

    diff_res = runner.invoke(app, ["bb-diff", str(left), str(right), "--plain"])
    assert diff_res.exit_code == 0
    assert "# changed matched blocks: 1" in diff_res.stdout
