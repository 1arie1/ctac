"""CLI smoke tests for `ctac absint --show interval`."""

from __future__ import annotations

import json

from typer.testing import CliRunner

from ctac.tool.main import app


def _wrap(body: str, syms: str = "R0:bv256\n\tR1:bv256\n\tS:bv256") -> str:
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


def _bounded_program() -> str:
    """R0 in [0, 0xff] (via assume); S = Mul(0x10, R0) in [0, 0xff0]."""
    return _wrap(
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd R0\n"
        "\t\tAssumeExpCmd Le(R0 0xff)\n"
        "\t\tAssignExpCmd S IntMul(0x10 R0 )\n"
        "\t}"
    )


def test_absint_interval_summary_plain(tmp_path):
    p = tmp_path / "q.tac"
    p.write_text(_bounded_program())
    result = CliRunner().invoke(
        app, ["absint", str(p), "--plain", "--show", "interval"]
    )
    assert result.exit_code == 0, result.output
    out = result.output
    # Two static vars (R0, S), both concrete after entry-block assume.
    assert "interval.static_symbols_total: 2" in out
    assert "interval.concrete_count: 2" in out
    assert "interval.top_count: 0" in out
    assert "interval.bot_count: 0" in out


def test_absint_interval_details_shows_tightest_table(tmp_path):
    p = tmp_path / "q.tac"
    p.write_text(_bounded_program())
    result = CliRunner().invoke(
        app, ["absint", str(p), "--plain", "--show", "interval", "--details"]
    )
    assert result.exit_code == 0, result.output
    out = result.output
    assert "tightest static intervals" in out
    # S = 0x10 * R0 with R0 ≤ 0xff → S ≤ 0xff0 = 4080.
    assert "[0, 4080]" in out
    # R0 ≤ 0xff = 255.
    assert "[0, 255]" in out


def test_absint_interval_json_payload(tmp_path):
    p = tmp_path / "q.tac"
    p.write_text(_bounded_program())
    result = CliRunner().invoke(
        app, ["absint", str(p), "--plain", "--show", "interval", "--json"]
    )
    assert result.exit_code == 0, result.output
    data = json.loads(result.output)
    assert "interval" in data
    iv = data["interval"]
    assert iv["static_symbols_total"] == 2
    assert iv["concrete_count"] == 2
    # Tightest table contains both vars with concrete bounds.
    by_var = {row["var"]: row for row in iv["top_tightest"]}
    assert by_var["R0"]["lo"] == 0 and by_var["R0"]["hi"] == 0xFF
    assert by_var["S"]["lo"] == 0 and by_var["S"]["hi"] == 0x10 * 0xFF


def test_absint_all_includes_both_degree_and_interval(tmp_path):
    p = tmp_path / "q.tac"
    p.write_text(_bounded_program())
    result = CliRunner().invoke(app, ["absint", str(p), "--plain"])
    assert result.exit_code == 0, result.output
    out = result.output
    assert "degree.max_degree" in out
    assert "interval.static_symbols_total" in out
