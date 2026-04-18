from __future__ import annotations

from pathlib import Path

from typer.testing import CliRunner

from ctac.analysis import (
    analyze_control_dependence,
    analyze_dsa,
    analyze_liveness,
    analyze_reaching_definitions,
    analyze_use_before_def,
    eliminate_dead_assignments,
    extract_def_use,
)
from ctac.parse import parse_string
from ctac.tool.main import app


TAC_DCE = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tx:bv256
\ty:bv256
\tz:bv256
}
Program {
\tBlock entry Succ [join] {
\t\tAssignExpCmd x 0x1
\t\tAssignExpCmd y 0x2
\t\tJumpCmd join
\t}
\tBlock join Succ [] {
\t\tAssignExpCmd z Add(x 0x1)
\t\tAssumeExpCmd Eq(z 0x2)
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""

TAC_UBD = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tw:bv256
}
Program {
\tBlock entry Succ [] {
\t\tAssumeExpCmd Eq(w 0x1)
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""

TAC_DSA_VALID = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tx:bv256
}
Program {
\tBlock left Succ [join] {
\t\tAssignExpCmd x 0x1
\t\tJumpCmd join
\t}
\tBlock right Succ [join] {
\t\tAssignExpCmd x 0x2
\t\tJumpCmd join
\t}
\tBlock join Succ [] {
\t\tAssumeExpCmd Eq(x 0x1)
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""

TAC_DSA_INVALID = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tx:bv256
\tc:bool
}
Program {
\tBlock entry Succ [left, right] {
\t\tAssignExpCmd x 0x0
\t\tAssignExpCmd c true
\t\tJumpiCmd left right c
\t}
\tBlock left Succ [join] {
\t\tAssignExpCmd x 0x1
\t\tJumpCmd join
\t}
\tBlock right Succ [join] {
\t\tJumpCmd join
\t}
\tBlock join Succ [] {
\t\tAssumeExpCmd Eq(x 0x1)
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""

TAC_CTRL_DEP = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tb:bool
}
Program {
\tBlock entry Succ [then, else] {
\t\tJumpiCmd then else b
\t}
\tBlock then Succ [join] {
\t\tJumpCmd join
\t}
\tBlock else Succ [join] {
\t\tJumpCmd join
\t}
\tBlock join Succ [] {
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""


def _write_tac(tmp_path: Path, content: str, name: str = "sample.tac") -> Path:
    p = tmp_path / name
    p.write_text(content, encoding="utf-8")
    return p


def test_def_use_and_reaching_defs() -> None:
    tac = parse_string(TAC_DCE, path="<string>")
    du = extract_def_use(tac.program)
    assert set(du.definitions_by_symbol) == {"x", "y", "z"}
    assert set(du.uses_by_symbol) == {"x", "z"}

    rd = analyze_reaching_definitions(tac.program, def_use=du)
    join_cmd0 = rd.in_by_command[next(k for k in rd.in_by_command if k.block_id == "join" and k.cmd_index == 0)]
    assert len(join_cmd0["x"]) == 1


def test_liveness_and_dce() -> None:
    tac = parse_string(TAC_DCE, path="<string>")
    du = extract_def_use(tac.program)
    lv = analyze_liveness(tac.program, def_use=du)
    assert "x" in lv.live_out_by_block["entry"]
    assert "y" not in lv.live_out_by_block["entry"]

    dce = eliminate_dead_assignments(tac.program, liveness=lv)
    removed_raw = {x.raw for x in dce.removed}
    assert "AssignExpCmd y 0x2" in removed_raw
    assert "AssignExpCmd x 0x1" not in removed_raw


def test_use_before_def_issue() -> None:
    tac = parse_string(TAC_UBD, path="<string>")
    result = analyze_use_before_def(tac.program)
    assert len(result.issues) == 1
    assert result.issues[0].symbol == "w"


def test_dsa_valid_and_invalid() -> None:
    valid = parse_string(TAC_DSA_VALID, path="<string>")
    valid_res = analyze_dsa(valid.program)
    assert valid_res.is_valid

    invalid = parse_string(TAC_DSA_INVALID, path="<string>")
    invalid_res = analyze_dsa(invalid.program)
    assert not invalid_res.is_valid
    assert any(i.kind == "ambiguous-use" for i in invalid_res.issues)


def test_control_dependence_edges() -> None:
    tac = parse_string(TAC_CTRL_DEP, path="<string>")
    cd = analyze_control_dependence(tac.program)
    assert ("entry", "then") in cd.edges
    assert ("entry", "else") in cd.edges


def test_df_cli_liveness_plain_golden(tmp_path: Path) -> None:
    p = _write_tac(tmp_path, TAC_DCE, "liveness.tac")
    runner = CliRunner()
    res = runner.invoke(app, ["df", str(p), "--plain", "--show", "liveness"])
    assert res.exit_code == 0
    lines = res.stdout.splitlines()
    assert lines[0].startswith("# path: ")
    assert lines[1:4] == [
        "# show: liveness",
        "# blocks: 2",
        "liveness:",
    ]
    assert lines[4].startswith("  time: ")
    assert lines[5] == "  blocks_with_live_in: 1, max_live_in_size: 1, max_live_out_size: 1"


def test_df_cli_dce_plain_golden(tmp_path: Path) -> None:
    p = _write_tac(tmp_path, TAC_DCE, "dce.tac")
    runner = CliRunner()
    res = runner.invoke(app, ["df", str(p), "--plain", "--show", "dce"])
    assert res.exit_code == 0
    lines = res.stdout.splitlines()
    assert lines[0].startswith("# path: ")
    assert lines[1:4] == [
        "# show: dce",
        "# blocks: 2",
        "dce:",
    ]
    assert lines[4].startswith("  time: ")
    assert lines[5] == "  removed_count: 1, remaining_commands: 4"


def test_df_cli_dce_plain_details_lists_removed(tmp_path: Path) -> None:
    p = _write_tac(tmp_path, TAC_DCE, "dce-details.tac")
    runner = CliRunner()
    res = runner.invoke(app, ["df", str(p), "--plain", "--show", "dce", "--details"])
    assert res.exit_code == 0
    lines = res.stdout.splitlines()
    assert "  remove entry:1 AssignExpCmd y  # AssignExpCmd y 0x2" in lines
