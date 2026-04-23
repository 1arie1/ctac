"""Tests for `ctac op-diff`."""

from __future__ import annotations

import json
from pathlib import Path

import pytest
from typer.testing import CliRunner

from ctac.tool.main import app


def _wrap(body: str, syms: str = "R0:bv256\n\tR1:bv256") -> str:
    return f"""TACSymbolTable {{
\tUserDefined {{
\t}}
\tBuiltinFunctions {{
\t}}
\tUninterpretedFunctions {{
\t}}
\t{syms}
}}
Program {{
{body}
}}
Axioms {{
}}
Metas {{
  "0": []
}}
"""


def test_identical_files_report_no_deltas(tmp_path):
    src = _wrap(
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd R0\n"
        "\t\tAssignExpCmd R1 BWAnd(R0 0xff )\n"
        "\t}"
    )
    p = tmp_path / "a.tac"
    p.write_text(src)
    result = CliRunner().invoke(app, ["op-diff", str(p), str(p), "--plain", "-q"])
    assert result.exit_code == 0, result.output
    assert "(no deltas)" in result.output
    # Section headings should NOT appear when there are no deltas.
    assert "expression_ops:" not in result.output


def test_op_count_delta_is_signed(tmp_path):
    left = _wrap(
        "\tBlock e Succ [] {\n"
        "\t\tAssignExpCmd R1 BWAnd(R0 0xff )\n"
        "\t}"
    )
    right = _wrap(
        "\tBlock e Succ [] {\n"
        "\t\tAssignExpCmd R1 BWAnd(R0 0xff )\n"
        "\t\tAssignExpCmd R1 BWAnd(R0 0xff )\n"
        "\t\tAssignExpCmd R1 BWAnd(R0 0xff )\n"
        "\t}"
    )
    lhs = tmp_path / "l.tac"
    rhs = tmp_path / "r.tac"
    lhs.write_text(left)
    rhs.write_text(right)
    result = CliRunner().invoke(app, ["op-diff", str(lhs), str(rhs), "--plain", "-q"])
    assert result.exit_code == 0, result.output
    # BWAnd went from 1 to 3 → +2.
    assert "BWAnd: 1 -> 3  (+2)" in result.output


def test_missing_on_right_shown_as_zero(tmp_path):
    # Left has Mod, right doesn't → should show "1 -> 0 (-1)", not "1 -> None".
    left = _wrap(
        "\tBlock e Succ [] {\n"
        "\t\tAssignExpCmd R1 Mod(R0 0xff )\n"
        "\t}"
    )
    right = _wrap(
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd R1\n"
        "\t}"
    )
    lhs = tmp_path / "l.tac"
    rhs = tmp_path / "r.tac"
    lhs.write_text(left)
    rhs.write_text(right)
    result = CliRunner().invoke(app, ["op-diff", str(lhs), str(rhs), "--plain", "-q"])
    assert result.exit_code == 0, result.output
    assert "Mod: 1 -> 0  (-1)" in result.output
    assert "None" not in result.output


def test_show_filters_sections(tmp_path):
    left = _wrap(
        "\tBlock e Succ [] {\n"
        "\t\tAssignExpCmd R1 BWAnd(R0 0xff )\n"
        "\t}"
    )
    right = _wrap(
        "\tBlock e Succ [] {\n"
        "\t\tAssignExpCmd R1 BWAnd(R0 0xff )\n"
        "\t\tAssignHavocCmd R0\n"
        "\t}"
    )
    lhs = tmp_path / "l.tac"
    rhs = tmp_path / "r.tac"
    lhs.write_text(left)
    rhs.write_text(right)
    # Restricted to expression_ops: should NOT include command_kinds / overview rows.
    result = CliRunner().invoke(
        app, ["op-diff", str(lhs), str(rhs), "--plain", "-q", "--show", "expression_ops"]
    )
    assert result.exit_code == 0, result.output
    assert "command_kinds:" not in result.output
    assert "overview:" not in result.output


def test_bad_section_name_rejected(tmp_path):
    src = _wrap("\tBlock e Succ [] {\n\t\tAssignHavocCmd R0\n\t}")
    p = tmp_path / "a.tac"
    p.write_text(src)
    result = CliRunner().invoke(
        app, ["op-diff", str(p), str(p), "--plain", "--show", "nonsense"]
    )
    assert result.exit_code != 0
    assert "unknown section" in result.output.lower()


def test_json_output_round_trips(tmp_path):
    left = _wrap(
        "\tBlock e Succ [] {\n"
        "\t\tAssignExpCmd R1 BWAnd(R0 0xff )\n"
        "\t}"
    )
    right = _wrap(
        "\tBlock e Succ [] {\n"
        "\t\tAssignExpCmd R1 BWAnd(R0 0xff )\n"
        "\t\tAssignExpCmd R1 BWAnd(R0 0xff )\n"
        "\t}"
    )
    lhs = tmp_path / "l.tac"
    rhs = tmp_path / "r.tac"
    lhs.write_text(left)
    rhs.write_text(right)
    result = CliRunner().invoke(
        app,
        ["op-diff", str(lhs), str(rhs), "--plain", "--json", "--show", "expression_ops"],
    )
    assert result.exit_code == 0, result.output
    doc = json.loads(result.output)
    assert doc["left"].endswith("l.tac")
    assert doc["right"].endswith("r.tac")
    bwand_row = next(
        r for r in doc["sections"]["expression_ops"]
        if r["key"] == "expression_ops.BWAnd"
    )
    assert bwand_row == {
        "key": "expression_ops.BWAnd",
        "left": 1,
        "right": 2,
        "delta": 1,
        "changed": True,
    }


_KEV_FAST = Path(
    "examples/kev-flaky/Fast/outputs/"
    "PresolverRule-rule_calculate_liquidation_verify_summary.tac"
)
_KEV_SLOW = Path(
    "examples/kev-flaky/Slow/outputs/"
    "PresolverRule-rule_calculate_liquidation_verify_summary.tac"
)


@pytest.mark.skipif(
    not (_KEV_FAST.is_file() and _KEV_SLOW.is_file()),
    reason="kev-flaky targets not present",
)
def test_kev_flaky_surfaces_the_mod_bwand_swap():
    """Real-target pin: op-diff surfaces the investigation finding in one shot."""
    result = CliRunner().invoke(
        app,
        ["op-diff", str(_KEV_FAST), str(_KEV_SLOW), "--plain", "-q"],
    )
    assert result.exit_code == 0, result.output
    # The three headline deltas that identified the splitU128 refactor.
    assert "Mod: 1 -> 0  (-1)" in result.output
    assert "BWAnd: 16 -> 18  (+2)" in result.output
    assert "commands: 911 -> 913  (+2)" in result.output
