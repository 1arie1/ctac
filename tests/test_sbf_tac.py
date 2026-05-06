"""CLI tests for `ctac sbf-tac` (SBF ↔ TAC bytecode-address join)."""

from __future__ import annotations

import json
from pathlib import Path

from typer.testing import CliRunner

from ctac.tool.main import app


def _write_sbf(tmp_path: Path, name: str, payload: dict) -> Path:
    p = tmp_path / name
    p.write_text(json.dumps(payload), encoding="utf-8")
    return p


def _write_tac(tmp_path: Path, name: str, content: str) -> Path:
    p = tmp_path / name
    p.write_text(content, encoding="utf-8")
    return p


# Two-block SBF program.
#
# Block A: r1 = 7 @ 0xea60, r2 = 9 @ 0xea64.
# Block B: r3 = r1 + r2 @ 0xea70, exit.
#
# Address 0xea64 is shared by the second SBF instruction *and* a third
# instruction in the test of duplicate handling — see DUP_SBF below.
_SBF_TWO_BLOCKS = {
    "name": "demo",
    "entry": "A",
    "exit": "B",
    "blocks": [
        {
            "label": "A",
            "successors": ["B"],
            "instructions": [
                {"inst": "r1 = 7", "meta": 0},
                {"inst": "r2 = 9", "meta": 1},
            ],
        },
        {
            "label": "B",
            "successors": [],
            "instructions": [
                {"inst": "r3 = r1 + r2", "meta": 2},
            ],
        },
    ],
    "metas": {
        "0": {"sbf_bytecode_address": 0xea60},
        "1": {"sbf_bytecode_address": 0xea64},
        "2": {"sbf_bytecode_address": 0xea70},
    },
}


# A TAC fragment that lowers each SBF instruction to scalar TAC cmds.
# - 0xea60 -> three TAC cmds (R10 = 7, R11 = R10, R12 = R11)
# - 0xea64 -> one TAC cmd (R20 = 9)
# - 0xeb00 -> one TAC cmd at an address NOT in the SBF (must be silently dropped)
# Address 0xea70 has no matching TAC; SBF instr there must still print.
_TAC_LOWERING = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tR10:bv256
\tR11:bv256
\tR12:bv256
\tR20:bv256
\tR99:bv256
\tflag:bool
}
Program {
\tBlock entry Succ [] {
\t\tAssignExpCmd:1 R10 0x7
\t\tAssignExpCmd:2 R11 R10
\t\tAssignExpCmd:3 R12 R11
\t\tAssignExpCmd:4 R20 0x9
\t\tAssignExpCmd:5 R99 0x99
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
      "value": 60000
    }
  ],
  "3": [
    {
      "key": {
        "name": "sbf.bytecode.address",
        "type": "java.lang.Long",
        "erasureStrategy": "Canonical"
      },
      "value": 60000
    }
  ],
  "4": [
    {
      "key": {
        "name": "sbf.bytecode.address",
        "type": "java.lang.Long",
        "erasureStrategy": "Canonical"
      },
      "value": 60004
    }
  ],
  "5": [
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


def test_sbf_tac_one_to_many_join(tmp_path: Path) -> None:
    """SBF instr at 0xea60 lowers to three TAC cmds; the first row carries the
    SBF text, the next two rows are continuation rows with empty SBF column."""
    sbf = _write_sbf(tmp_path, "demo.sbf.json", _SBF_TWO_BLOCKS)
    tac = _write_tac(tmp_path, "demo.tac", _TAC_LOWERING)
    runner = CliRunner()
    res = runner.invoke(app, ["sbf-tac", str(sbf), str(tac), "--plain"])
    assert res.exit_code == 0, res.output
    out = res.output

    # All three TAC cmds at 0xea60 must appear.
    assert "R10 = 7" in out
    assert "R11 = R10" in out
    assert "R12 = R11" in out

    # The first row carries the SBF text + first TAC cmd.
    lines = out.splitlines()
    sbf_row = next(ln for ln in lines if "0xea60" in ln)
    assert "r1 = 7" in sbf_row
    assert "R10 = 7" in sbf_row, sbf_row

    # Continuation rows: have R11/R12 but NOT the SBF text or the address.
    cont_rows = [ln for ln in lines if "R11 = R10" in ln or "R12 = R11" in ln]
    assert len(cont_rows) == 2
    for ln in cont_rows:
        assert "0xea60" not in ln
        assert "r1 = 7" not in ln


def test_sbf_tac_one_to_zero(tmp_path: Path) -> None:
    """SBF instr at 0xea70 has no matching TAC cmd. The SBF row still prints."""
    sbf = _write_sbf(tmp_path, "demo.sbf.json", _SBF_TWO_BLOCKS)
    tac = _write_tac(tmp_path, "demo.tac", _TAC_LOWERING)
    runner = CliRunner()
    res = runner.invoke(app, ["sbf-tac", str(sbf), str(tac), "--plain"])
    assert res.exit_code == 0, res.output
    sbf_row = next(ln for ln in res.output.splitlines() if "0xea70" in ln)
    assert "r3 = r1 + r2" in sbf_row


def test_sbf_tac_address_mismatch_silently_dropped(tmp_path: Path) -> None:
    """A TAC cmd at an address not in SBF must NOT appear in the join."""
    sbf = _write_sbf(tmp_path, "demo.sbf.json", _SBF_TWO_BLOCKS)
    tac = _write_tac(tmp_path, "demo.tac", _TAC_LOWERING)
    runner = CliRunner()
    res = runner.invoke(app, ["sbf-tac", str(sbf), str(tac), "--plain"])
    assert res.exit_code == 0, res.output
    # R99 is at 0xeb00 in TAC, never an SBF address — should not appear.
    assert "R99" not in res.output
    assert "0xeb00" not in res.output
    # And no trailer counting it (per-design: expert audience).
    assert "tac cmds with addresses not in sbf" not in res.output


def test_sbf_tac_top_note_emitted(tmp_path: Path) -> None:
    """One-line note up front so a newcomer isn't confused by what's missing."""
    sbf = _write_sbf(tmp_path, "demo.sbf.json", _SBF_TWO_BLOCKS)
    tac = _write_tac(tmp_path, "demo.tac", _TAC_LOWERING)
    runner = CliRunner()
    res = runner.invoke(app, ["sbf-tac", str(sbf), str(tac), "--plain"])
    assert res.exit_code == 0, res.output
    assert "tac cmds without sbf addresses are not shown" in res.output


def test_sbf_tac_repeated_sbf_address_keeps_join(tmp_path: Path) -> None:
    """SBF traces commonly repeat addresses (inlined call paths). Each
    occurrence must show the full TAC join, not be silenced."""
    payload = {
        "name": "dup",
        "entry": "A",
        "exit": "A",
        "blocks": [
            {
                "label": "A",
                "successors": [],
                "instructions": [
                    {"inst": "r1 = 7", "meta": 0},
                    {"inst": "r1 = 7", "meta": 0},  # repeated address
                ],
            }
        ],
        "metas": {"0": {"sbf_bytecode_address": 0xea60}},
    }
    sbf = _write_sbf(tmp_path, "dup.sbf.json", payload)
    tac = _write_tac(tmp_path, "demo.tac", _TAC_LOWERING)
    runner = CliRunner()
    res = runner.invoke(app, ["sbf-tac", str(sbf), str(tac), "--plain"])
    assert res.exit_code == 0, res.output
    # Both occurrences print 0xea60 with TAC content; no duplicate-address warning.
    assert res.output.count("0xea60") == 2
    assert res.output.count("R10 = 7") == 2  # TAC join repeated
    assert "duplicate sbf address" not in res.output


def test_sbf_tac_filter_only_keeps_selected_block(tmp_path: Path) -> None:
    """`--only B` slices the SBF CFG to block B; block A's rows must vanish."""
    sbf = _write_sbf(tmp_path, "demo.sbf.json", _SBF_TWO_BLOCKS)
    tac = _write_tac(tmp_path, "demo.tac", _TAC_LOWERING)
    runner = CliRunner()
    res = runner.invoke(app, ["sbf-tac", str(sbf), str(tac), "--plain", "--only", "B"])
    assert res.exit_code == 0, res.output
    out = res.output
    assert "B:" in out
    assert "A:" not in out
    assert "0xea70" in out  # block B address present
    assert "0xea60" not in out  # block A address absent
    assert "0xea64" not in out


def test_sbf_tac_address_format_is_grepable_hex(tmp_path: Path) -> None:
    """Address column uses `0x{addr:x}` lowercase, no separators —
    same contract as `pp --with-address`, so external tooling can grep."""
    sbf = _write_sbf(tmp_path, "demo.sbf.json", _SBF_TWO_BLOCKS)
    tac = _write_tac(tmp_path, "demo.tac", _TAC_LOWERING)
    runner = CliRunner()
    res = runner.invoke(app, ["sbf-tac", str(sbf), str(tac), "--plain"])
    assert res.exit_code == 0, res.output
    out = res.output
    assert "0xea60" in out
    assert "0xea64" in out
    assert "0xea70" in out
    # No grouping separators or capitalized hex.
    assert "0xEA60" not in out
    assert "0xea_60" not in out
    # No decimal leak.
    assert "60000" not in out


def test_sbf_tac_inline_comments_stripped(tmp_path: Path) -> None:
    """SBF cmds in production carry `/* 0x... */` and `/*inlined_function_name=…*/`
    comments. The join view strips them so the SBF cell is narrow enough to
    leave room for the TAC column."""
    payload = {
        "name": "comments",
        "entry": "A",
        "exit": "A",
        "blocks": [
            {
                "label": "A",
                "successors": [],
                "instructions": [
                    {
                        "inst": "call CVT_foo  /* 0xea60 */ /*inlined_function_name=very::long::path*/",
                        "meta": 0,
                    },
                ],
            }
        ],
        "metas": {"0": {"sbf_bytecode_address": 0xea60}},
    }
    sbf = _write_sbf(tmp_path, "comments.sbf.json", payload)
    tac = _write_tac(tmp_path, "demo.tac", _TAC_LOWERING)
    runner = CliRunner()
    res = runner.invoke(app, ["sbf-tac", str(sbf), str(tac), "--plain"])
    assert res.exit_code == 0, res.output
    out = res.output
    # Address comment and inlined-function comment must both be stripped.
    assert "/* 0xea60 */" not in out
    assert "inlined_function_name" not in out
    # The instruction itself is still present.
    assert "call CVT_foo" in out


def test_sbf_tac_writes_output_file(tmp_path: Path) -> None:
    """`-o FILE` writes the joined view; stdout gets only the confirmation."""
    sbf = _write_sbf(tmp_path, "demo.sbf.json", _SBF_TWO_BLOCKS)
    tac = _write_tac(tmp_path, "demo.tac", _TAC_LOWERING)
    out = tmp_path / "join.txt"
    runner = CliRunner()
    res = runner.invoke(app, ["sbf-tac", str(sbf), str(tac), "-o", str(out), "--plain"])
    assert res.exit_code == 0, res.output
    assert out.is_file()
    text = out.read_text(encoding="utf-8")
    assert "0xea60" in text
    assert "R10 = 7" in text
    # Stdout has the wrote-confirmation, not the joined content.
    assert "# wrote" in res.output
    assert "0xea60" not in res.output
