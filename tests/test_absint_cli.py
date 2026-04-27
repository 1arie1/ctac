"""Tests for `ctac absint`."""

from __future__ import annotations

import json

from typer.testing import CliRunner

from ctac.tool.main import app


def _wrap(body: str, syms: str = "R0:bv256\n\tR1:bv256\n\tR2:bv256\n\tS:bv256") -> str:
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


def _quadratic_program() -> str:
    return _wrap(
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd R0\n"
        "\t\tAssignExpCmd S Mul(R0 R0 )\n"
        "\t}"
    )


def _div_program() -> str:
    return _wrap(
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd R0\n"
        "\t\tAssignHavocCmd R1\n"
        "\t\tAssignExpCmd S Div(R0 R1 )\n"
        "\t}"
    )


def test_absint_summary_plain(tmp_path):
    p = tmp_path / "q.tac"
    p.write_text(_quadratic_program())
    result = CliRunner().invoke(app, ["absint", str(p), "--plain"])
    assert result.exit_code == 0, result.output
    out = result.output
    assert "degree.max_degree: 2" in out
    assert "degree.symbols_total: 2" in out
    # Distribution: R0 is degree 1 (havoc), S is degree 2 (Mul of R0 with R0).
    assert "degree.distribution.deg_1: 1" in out
    assert "degree.distribution.deg_2: 1" in out
    assert "degree.saw_top: 0" in out


def test_absint_details_lists_top_nonlinear_with_command(tmp_path):
    p = tmp_path / "q.tac"
    p.write_text(_quadratic_program())
    result = CliRunner().invoke(app, ["absint", str(p), "--plain", "--details"])
    assert result.exit_code == 0, result.output
    out = result.output
    # Header for the detail table
    assert "top non-linear" in out
    # The single non-linear def: S = Mul(R0, R0) → degree 2
    # Check for both the lhs and the degree column
    assert " S " in out or " S\t" in out or " S |" in out
    assert "  2 " in out  # degree column for S


def test_absint_min_degree_filter_excludes_low_degree(tmp_path):
    p = tmp_path / "q.tac"
    p.write_text(_quadratic_program())
    # min-degree = 3 should produce an empty top-nonlinear section
    result = CliRunner().invoke(
        app, ["absint", str(p), "--plain", "--details", "--min-degree", "3"]
    )
    assert result.exit_code == 0, result.output
    out = result.output
    # Header is suppressed when there are no rows
    assert "top non-linear" not in out


def test_absint_json_emits_top_nonlinear_array(tmp_path):
    p = tmp_path / "d.tac"
    p.write_text(_div_program())
    result = CliRunner().invoke(app, ["absint", str(p), "--json"])
    assert result.exit_code == 0, result.output
    payload = json.loads(result.output)
    assert "degree" in payload
    deg = payload["degree"]
    # max(deg(R0), deg(R1)) + 1 = 1 + 1 = 2
    assert deg["max_degree"] == 2
    assert deg["nonlinear_count"] == 1
    assert len(deg["top_nonlinear"]) == 1
    row = deg["top_nonlinear"][0]
    assert row["lhs"] == "S"
    assert row["degree"] == 2
    assert "Div" in row["rendered"] or "/" in row["rendered"]


def test_absint_show_unknown_mode_errors(tmp_path):
    p = tmp_path / "q.tac"
    p.write_text(_quadratic_program())
    result = CliRunner().invoke(app, ["absint", str(p), "--plain", "--show", "bogus"])
    assert result.exit_code != 0
    assert "unknown --show mode" in result.output


def test_absint_filter_warning_surfaces(tmp_path):
    p = tmp_path / "q.tac"
    p.write_text(_quadratic_program())
    # --only with a known block id should still run; with an unknown id
    # we expect a filter warning in the input warnings count.
    result = CliRunner().invoke(
        app, ["absint", str(p), "--plain", "--only", "nonexistent"]
    )
    assert result.exit_code == 0, result.output
    # Filtered out everything → 0 blocks.
    assert "input.blocks: 0" in result.output
    assert "input.filter_warnings: 1" in result.output
