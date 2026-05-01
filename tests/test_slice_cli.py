"""CLI tests for ``ctac slice``."""

from __future__ import annotations

import json
from pathlib import Path

from typer.testing import CliRunner

from ctac.tool.main import app


_TAC_BYTEMAP = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tM0:bytemap
\tM1:bytemap
\tM2:bytemap
\tk1:bv256
\tk2:bv256
\tv1:bv256
\tv2:bv256
\tr:bv256
\tjunk:bv256
}
Program {
\tBlock entry Succ [] {
\t\tAssignHavocCmd M0
\t\tAssignExpCmd k1 0x10
\t\tAssignExpCmd v1 0xaa
\t\tAssignExpCmd k2 0x20
\t\tAssignExpCmd v2 0xbb
\t\tAssignExpCmd M1 Store(M0 k1 v1)
\t\tAssignExpCmd M2 Store(M1 k2 v2)
\t\tAssignExpCmd r Select(M2 k1)
\t\tAssignExpCmd junk 0xdead
\t\tAssertCmd Eq(r v1) "select after store"
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""


def _write(tmp_path: Path, content: str, name: str = "f.tac") -> Path:
    p = tmp_path / name
    p.write_text(content, encoding="utf-8")
    return p


def test_slice_assert_shorthand_drops_unrelated(tmp_path: Path) -> None:
    """``-c entry:assert`` slices from the assert; ``junk`` is dropped."""
    f = _write(tmp_path, _TAC_BYTEMAP)
    runner = CliRunner()
    res = runner.invoke(app, ["slice", str(f), "-c", "entry:assert", "--plain"])
    assert res.exit_code == 0, res.output
    # Bytemap chain pulled in.
    assert "M0 = havoc" in res.output
    assert "Store" in res.output or "[" in res.output  # human printer rewrites
    # The unrelated def must be elided in --mark drop.
    assert "junk = " not in res.output


def test_slice_show_points_emits_block_cmd_pairs(tmp_path: Path) -> None:
    f = _write(tmp_path, _TAC_BYTEMAP)
    runner = CliRunner()
    res = runner.invoke(
        app, ["slice", str(f), "-c", "r", "--show", "points", "--plain"]
    )
    assert res.exit_code == 0, res.output
    # At least one BLK:IDX line (indices of cmds in `entry`).
    lines = [
        line for line in res.output.splitlines() if line.startswith("entry:")
    ]
    assert lines, res.output


def test_slice_show_stats_has_counts(tmp_path: Path) -> None:
    f = _write(tmp_path, _TAC_BYTEMAP)
    runner = CliRunner()
    res = runner.invoke(
        app, ["slice", str(f), "-c", "r", "--show", "stats", "--plain"]
    )
    assert res.exit_code == 0, res.output
    assert "selected_cmds:" in res.output
    assert "total_cmds:" in res.output
    assert "rounds:" in res.output


def test_slice_show_json_parses(tmp_path: Path) -> None:
    f = _write(tmp_path, _TAC_BYTEMAP)
    runner = CliRunner()
    res = runner.invoke(
        app, ["slice", str(f), "-c", "r", "--show", "json", "--plain"]
    )
    assert res.exit_code == 0, res.output
    # Strip preamble (only "{...}" payload is JSON).
    payload_start = res.output.find("{")
    payload = res.output[payload_start:].strip()
    obj = json.loads(payload)
    assert "selected" in obj
    assert "seeds" in obj
    assert "rounds" in obj


def test_slice_unknown_block_errors(tmp_path: Path) -> None:
    f = _write(tmp_path, _TAC_BYTEMAP)
    runner = CliRunner()
    res = runner.invoke(
        app, ["slice", str(f), "-c", "no_such_block:assert", "--plain"]
    )
    assert res.exit_code != 0
    assert "no_such_block" in res.output


def test_slice_missing_criterion_errors(tmp_path: Path) -> None:
    f = _write(tmp_path, _TAC_BYTEMAP)
    runner = CliRunner()
    res = runner.invoke(app, ["slice", str(f), "--plain"])
    assert res.exit_code != 0
    assert "criterion" in res.output.lower()


def test_slice_no_data_no_control_is_seed_only(tmp_path: Path) -> None:
    f = _write(tmp_path, _TAC_BYTEMAP)
    runner = CliRunner()
    res = runner.invoke(
        app,
        [
            "slice",
            str(f),
            "-c",
            "entry:assert",
            "--no-data",
            "--no-control",
            "--show",
            "stats",
            "--plain",
        ],
    )
    assert res.exit_code == 0, res.output
    assert "selected_cmds: 1" in res.output


def test_slice_mark_gray_under_plain_uses_hash(tmp_path: Path) -> None:
    f = _write(tmp_path, _TAC_BYTEMAP)
    runner = CliRunner()
    res = runner.invoke(
        app,
        [
            "slice",
            str(f),
            "-c",
            "entry:assert",
            "--mark",
            "gray",
            "--plain",
        ],
    )
    assert res.exit_code == 0, res.output
    # Under --plain, non-selected lines render as `# ` prefixed comments
    # (no ANSI escape sequences).
    assert "\x1b[" not in res.output
    # `junk = ` is non-selected; with --mark gray it shows up under '# '.
    assert "# junk = " in res.output


def test_slice_output_file_omits_ansi(tmp_path: Path) -> None:
    f = _write(tmp_path, _TAC_BYTEMAP)
    out = tmp_path / "slice.htac"
    runner = CliRunner()
    res = runner.invoke(
        app,
        ["slice", str(f), "-c", "entry:assert", "-o", str(out)],
    )
    assert res.exit_code == 0, res.output
    assert out.is_file()
    text = out.read_text(encoding="utf-8")
    assert "\x1b[" not in text
    assert "entry:" in text


def test_slice_pre_filter_with_only(tmp_path: Path) -> None:
    """``--only`` pre-scopes the program before slicing."""
    f = _write(tmp_path, _TAC_BYTEMAP)
    runner = CliRunner()
    res = runner.invoke(
        app,
        [
            "slice",
            str(f),
            "-c",
            "entry:assert",
            "--only",
            "entry",
            "--show",
            "stats",
            "--plain",
        ],
    )
    assert res.exit_code == 0, res.output
    # Pre-slice filter line shows reduced-program counts.
    assert "pre-slice filter" in res.output


def test_slice_symbol_in_block_form(tmp_path: Path) -> None:
    """``SYM@BLK`` is accepted and disambiguates correctly."""
    f = _write(tmp_path, _TAC_BYTEMAP)
    runner = CliRunner()
    res = runner.invoke(
        app, ["slice", str(f), "-c", "r@entry", "--show", "stats", "--plain"]
    )
    assert res.exit_code == 0, res.output
    # `r@entry` resolves to the def of r in entry; transitive closure
    # through M2/M1/M0 should make this >1.
    selected_line = next(
        line for line in res.output.splitlines() if line.startswith("selected_cmds:")
    )
    n = int(selected_line.split(":")[1].strip())
    assert n > 1


def test_slice_rejects_blk_idx_form(tmp_path: Path) -> None:
    """Numeric ``:IDX`` is rejected; only ``:assert`` is allowed."""
    f = _write(tmp_path, _TAC_BYTEMAP)
    runner = CliRunner()
    res = runner.invoke(app, ["slice", str(f), "-c", "entry:0", "--plain"])
    assert res.exit_code != 0
    assert "BLK:assert" in res.output or "indices" in res.output
