"""CLI tests for `ctac pp`, focusing on the `-o`/`--output` file-output option."""

from __future__ import annotations

from pathlib import Path

from typer.testing import CliRunner

from ctac.tool.main import app

TAC_SMALL = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\ta:bv256
\tb:bool
}
Program {
\tBlock entry Succ [next] {
\t\tAssignExpCmd a 0x1
\t\tAssignExpCmd b true
\t\tJumpCmd next
\t}
\tBlock next Succ [] {
\t\tAssertCmd b "must hold"
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""


def _write_tac(tmp_path: Path, content: str, name: str) -> Path:
    p = tmp_path / name
    p.write_text(content, encoding="utf-8")
    return p


def test_pp_output_file_option_writes_content(tmp_path: Path) -> None:
    """`ctac pp -o FILE` writes the pretty-printed output to FILE and a confirmation line to stdout."""
    tac = _write_tac(tmp_path, TAC_SMALL, "small.tac")
    out = tmp_path / "pp.out"
    runner = CliRunner()
    res = runner.invoke(app, ["pp", str(tac), "-o", str(out), "--plain"])
    assert res.exit_code == 0, res.output
    assert out.is_file()
    text = out.read_text(encoding="utf-8")
    # Block headers and commands are in the file (plain, no ANSI).
    assert "entry:" in text
    assert "next:" in text
    assert "assert b" in text
    # `# printer:` metadata line.
    assert "# printer: human" in text
    # Stdout got only the confirmation message, not the pp content.
    assert "# wrote" in res.output
    assert "entry:" not in res.output


def test_pp_without_output_prints_to_stdout(tmp_path: Path) -> None:
    """Without `-o`, pp prints to stdout as before (no file written)."""
    tac = _write_tac(tmp_path, TAC_SMALL, "small2.tac")
    runner = CliRunner()
    res = runner.invoke(app, ["pp", str(tac), "--plain"])
    assert res.exit_code == 0, res.output
    assert "entry:" in res.output
    assert "# printer: human" in res.output


def test_pp_output_file_omits_ansi_codes(tmp_path: Path) -> None:
    """File output is plain text — no ANSI escape sequences."""
    tac = _write_tac(tmp_path, TAC_SMALL, "small3.tac")
    out = tmp_path / "pp3.out"
    runner = CliRunner()
    res = runner.invoke(app, ["pp", str(tac), "-o", str(out)])  # no --plain
    assert res.exit_code == 0, res.output
    text = out.read_text(encoding="utf-8")
    assert "\x1b[" not in text  # no ANSI escape sequences in the file


# Synthetic TAC carrying SBF bytecode address metadata. The Metas section
# below ties cmd index 1 -> 0xea60 (60000), cmd index 2 -> 0xea64
# (60004), cmd index 3 -> 0xeb00 (60160, out of a [0xea00, 0xeaff]
# window). Cmd index 4 has no metadata, exercising the blank-padding
# path.
TAC_WITH_ADDRS = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\ta:bv256
\tb:bv256
\tc:bv256
\td:bv256
\tflag:bool
}
Program {
\tBlock entry Succ [next] {
\t\tAssignExpCmd:1 a 0x1
\t\tAssignExpCmd:2 b 0x2
\t\tJumpCmd next
\t}
\tBlock next Succ [] {
\t\tAssignExpCmd:3 c 0x3
\t\tAssignExpCmd:4 d 0x4
\t\tAssertCmd flag "must hold"
\t}
}
Axioms {
}
Metas {
  "1": [
    {
      "key": {
        "name": "sbf.bytecode.address",
        "type": "java.lang.Long",
        "erasureStrategy": "Canonical"
      },
      "value": 60000
    }
  ],
  "2": [
    {
      "key": {
        "name": "sbf.bytecode.address",
        "type": "java.lang.Long",
        "erasureStrategy": "Canonical"
      },
      "value": 60004
    }
  ],
  "3": [
    {
      "key": {
        "name": "sbf.bytecode.address",
        "type": "java.lang.Long",
        "erasureStrategy": "Canonical"
      },
      "value": 60160
    }
  ]
}
"""


def test_pp_default_no_address_column(tmp_path: Path) -> None:
    """Without --with-address, output is unchanged — no hex address tokens injected."""
    tac = _write_tac(tmp_path, TAC_WITH_ADDRS, "addrs.tac")
    runner = CliRunner()
    res = runner.invoke(app, ["pp", str(tac), "--plain"])
    assert res.exit_code == 0, res.output
    # The synthetic metadata addresses must NOT leak into the default rendering.
    assert "0xea60" not in res.output
    assert "0xea64" not in res.output
    assert "0xeb00" not in res.output


def test_pp_with_address_prefixes_in_grepable_hex(tmp_path: Path) -> None:
    """--with-address prefixes commands with `0x{addr:x}` (lowercase, no separators)."""
    tac = _write_tac(tmp_path, TAC_WITH_ADDRS, "addrs.tac")
    runner = CliRunner()
    res = runner.invoke(app, ["pp", str(tac), "--plain", "--with-address"])
    assert res.exit_code == 0, res.output
    out = res.output
    # Each address shows up exactly as the grepable token, not decimal.
    assert "0xea60" in out
    assert "0xea64" in out
    assert "0xeb00" in out
    # No grouping separators or underscores in the printed address tokens.
    assert "0xea_60" not in out
    assert "59984" not in out  # decimal storage must not bleed through
    # Address column appears next to the command text (same line).
    addr_line = next((ln for ln in out.splitlines() if "0xea60" in ln), None)
    assert addr_line is not None
    assert "a = 1" in addr_line


def test_pp_with_address_blank_pad_when_metadata_missing(tmp_path: Path) -> None:
    """Commands without sbf.bytecode.address still render, with blank padding in the addr column."""
    tac = _write_tac(tmp_path, TAC_WITH_ADDRS, "addrs.tac")
    runner = CliRunner()
    res = runner.invoke(app, ["pp", str(tac), "--plain", "--with-address"])
    assert res.exit_code == 0, res.output
    # Cmd index 4 (assigning to `d`) has no metadata entry — line still
    # emitted, with no `0x...` prefix in the address column.
    d_line = next((ln for ln in res.output.splitlines() if "d = 4" in ln), None)
    assert d_line is not None, res.output
    # Two-space indent + 10-char blank address column = 12 leading spaces.
    assert d_line.startswith("  " + " " * 10), d_line


def test_pp_address_range_filters_in_range_only(tmp_path: Path) -> None:
    """--address-range LO-HI keeps only commands whose address is in [LO, HI]."""
    tac = _write_tac(tmp_path, TAC_WITH_ADDRS, "addrs.tac")
    runner = CliRunner()
    res = runner.invoke(app, ["pp", str(tac), "--plain", "--address-range", "0xea00-0xeaff"])
    assert res.exit_code == 0, res.output
    out = res.output
    # In-range cmds present.
    assert "0xea60" in out
    assert "0xea64" in out
    # Out-of-range cmd dropped.
    assert "0xeb00" not in out
    # Cmd without metadata is dropped under range filter (no addr to test).
    # The `d = 4` AssignExpCmd line should be gone.
    assert "d = 4" not in out


def test_pp_address_range_drops_blocks_with_no_in_range_cmds(tmp_path: Path) -> None:
    """A block whose every cmd is filtered out vanishes from the rendered output."""
    tac = _write_tac(tmp_path, TAC_WITH_ADDRS, "addrs.tac")
    runner = CliRunner()
    # Range covers only the entry block's two commands (0xea60, 0xea64).
    res = runner.invoke(app, ["pp", str(tac), "--plain", "--address-range", "0xea60-0xea64"])
    assert res.exit_code == 0, res.output
    out = res.output
    assert "entry:" in out
    # `next:` block has only 0xeb00 (out of range) + an unaddressed cmd + assert,
    # so the whole block should disappear.
    assert "next:" not in out


def test_pp_address_range_accepts_decimal_endpoints(tmp_path: Path) -> None:
    """LO-HI accepts plain decimal as well as 0x-prefixed hex."""
    tac = _write_tac(tmp_path, TAC_WITH_ADDRS, "addrs.tac")
    runner = CliRunner()
    # 60000 = 0xea60, 60004 = 0xea64 — same window as the hex test above.
    res = runner.invoke(app, ["pp", str(tac), "--plain", "--address-range", "60000-60004"])
    assert res.exit_code == 0, res.output
    assert "0xea60" in res.output
    assert "0xea64" in res.output
    assert "0xeb00" not in res.output


def test_pp_address_range_invalid_string_exits_nonzero(tmp_path: Path) -> None:
    """Malformed --address-range exits with a clear error."""
    tac = _write_tac(tmp_path, TAC_WITH_ADDRS, "addrs.tac")
    runner = CliRunner()
    res = runner.invoke(app, ["pp", str(tac), "--plain", "--address-range", "not-a-range"])
    assert res.exit_code != 0
    assert "address-range" in res.output


def test_pp_address_range_implies_with_address(tmp_path: Path) -> None:
    """Range filter alone (without --with-address) still prints addresses on surviving cmds."""
    tac = _write_tac(tmp_path, TAC_WITH_ADDRS, "addrs.tac")
    runner = CliRunner()
    res = runner.invoke(app, ["pp", str(tac), "--plain", "--address-range", "0xea00-0xeaff"])
    assert res.exit_code == 0, res.output
    assert "0xea60" in res.output
