"""CLI tests for `ctac pin`."""

from __future__ import annotations

import json

from typer.testing import CliRunner

from ctac.tool.main import app


runner = CliRunner()


_TAC = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tB0:bool
}
Program {
\tBlock e Succ [a, b] {
\t\tJumpiCmd a b B0
\t}
\tBlock a Succ [exit] {
\t\tJumpCmd exit
\t}
\tBlock b Succ [exit] {
\t\tJumpCmd exit
\t}
\tBlock exit Succ [] {
\t\tNoSuchCmd
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""


def _write_tac(tmp_path):
    p = tmp_path / "test.tac"
    p.write_text(_TAC)
    return p


def test_pin_help():
    """--help should run without error and mention key flags."""
    result = runner.invoke(app, ["pin", "--help"])
    assert result.exit_code == 0
    out = result.stdout
    assert "--drop" in out
    assert "--bind" in out
    assert "--split" in out
    assert "--show" in out


def test_pin_drop_writes_output(tmp_path):
    src = _write_tac(tmp_path)
    out = tmp_path / "out.tac"
    result = runner.invoke(
        app,
        ["pin", str(src), "--drop", "a", "-o", str(out), "--plain"],
    )
    assert result.exit_code == 0, result.stdout
    assert out.is_file()
    body = out.read_text()
    # Block 'a' should be gone.
    assert "Block a " not in body
    # Block 'b' should remain.
    assert "Block b " in body


def test_pin_bind_writes_output(tmp_path):
    src = _write_tac(tmp_path)
    out = tmp_path / "out.tac"
    result = runner.invoke(
        app,
        [
            "pin",
            str(src),
            "--bind",
            "B0=false",
            "-o",
            str(out),
            "--plain",
        ],
    )
    assert result.exit_code == 0, result.stdout
    assert out.is_file()


def test_pin_rejects_rc_bind(tmp_path):
    src = _write_tac(tmp_path)
    result = runner.invoke(
        app,
        [
            "pin",
            str(src),
            "--bind",
            "ReachabilityCertorafoo=false",
            "-o",
            str(tmp_path / "out.tac"),
            "--plain",
        ],
    )
    assert result.exit_code != 0
    # Look for the error in stdout (typer prints there in Rich mode) and stderr
    # combined.
    out = (result.stdout or "") + (result.stderr or "")
    assert "ReachabilityCertora" in out or "RC" in out


def test_pin_rejects_unknown_drop(tmp_path):
    src = _write_tac(tmp_path)
    result = runner.invoke(
        app,
        [
            "pin",
            str(src),
            "--drop",
            "no_such_block",
            "-o",
            str(tmp_path / "out.tac"),
            "--plain",
        ],
    )
    assert result.exit_code != 0


def test_pin_split_writes_directory_with_manifest(tmp_path):
    """Split case: writes a directory with one .tac per case + manifest.json."""
    src = tmp_path / "test.tac"
    src.write_text(
        """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tB0:bool
}
Program {
\tBlock e Succ [p1, p2] {
\t\tJumpiCmd p1 p2 B0
\t}
\tBlock p1 Succ [j] {
\t\tJumpCmd j
\t}
\tBlock p2 Succ [j] {
\t\tJumpCmd j
\t}
\tBlock j Succ [exit] {
\t\tJumpCmd exit
\t}
\tBlock exit Succ [] {
\t\tNoSuchCmd
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""
    )
    out = tmp_path / "cases"
    result = runner.invoke(
        app,
        ["pin", str(src), "--split", "j", "-o", str(out), "--plain"],
    )
    assert result.exit_code == 0, result.stdout
    assert (out / "manifest.json").is_file()
    tac_files = list(out.glob("*.tac"))
    assert len(tac_files) == 2
    m = json.loads((out / "manifest.json").read_text())
    assert m["schema_version"] == 1
    assert len(m["cases"]) == 2


def test_pin_show_mode_on_manifest_directory(tmp_path):
    """First write a manifest, then read it back via show mode."""
    src = tmp_path / "test.tac"
    src.write_text(
        """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tB0:bool
}
Program {
\tBlock e Succ [p1, p2] {
\t\tJumpiCmd p1 p2 B0
\t}
\tBlock p1 Succ [j] {
\t\tJumpCmd j
\t}
\tBlock p2 Succ [j] {
\t\tJumpCmd j
\t}
\tBlock j Succ [exit] {
\t\tJumpCmd exit
\t}
\tBlock exit Succ [] {
\t\tNoSuchCmd
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""
    )
    out_dir = tmp_path / "cases"
    runner.invoke(
        app,
        ["pin", str(src), "--split", "j", "-o", str(out_dir), "--plain"],
    )
    # Now show.
    result = runner.invoke(app, ["pin", str(out_dir), "--plain"])
    assert result.exit_code == 0, result.stdout
    assert "Cases" in result.stdout
    assert "Splits" in result.stdout


def test_pin_show_flag_rejects_non_directory(tmp_path):
    src = _write_tac(tmp_path)
    result = runner.invoke(app, ["pin", str(src), "--show", "--plain"])
    assert result.exit_code != 0


def test_pin_trace_writes_jsonl(tmp_path):
    src = _write_tac(tmp_path)
    out = tmp_path / "out.tac"
    trace = tmp_path / "pin.trace"
    result = runner.invoke(
        app,
        [
            "pin",
            str(src),
            "--drop",
            "a",
            "-o",
            str(out),
            "--trace",
            str(trace),
            "--plain",
        ],
    )
    assert result.exit_code == 0, result.stdout
    assert trace.is_file()
    lines = trace.read_text().rstrip("\n").split("\n")
    events = [json.loads(line) for line in lines]
    event_names = {e["event"] for e in events}
    assert "pin-start" in event_names
    assert "block-dropped" in event_names
    assert "pin-complete" in event_names


def test_pin_no_input_errors():
    result = runner.invoke(app, ["pin", "--plain"])
    assert result.exit_code != 0
