"""Tests for ctac.ua.split_asserts + the CLI --strategy split path."""

from __future__ import annotations

import json
from pathlib import Path

from typer.testing import CliRunner

from ctac.ast.nodes import (
    AssertCmd,
    AssumeExpCmd,
    ConstExpr,
    SymbolRef,
)
from ctac.parse import parse_string
from ctac.tool.main import app
from ctac.ua import split_asserts


def _wrap(body: str, *, syms: str) -> str:
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


def _block(program, block_id):
    for b in program.blocks:
        if b.id == block_id:
            return b
    raise AssertionError(f"no block {block_id!r}")


def _block_ids(program):
    return [b.id for b in program.blocks]


# --- split_asserts primitive ----------------------------------------------


def test_split_k3_converts_others_to_assumes():
    # Three asserts, each in its own block. For each output, the live
    # assert stays as AssertCmd; the other two become AssumeExpCmds on
    # the same predicate symbol.
    tac = parse_string(
        _wrap(
            "\tBlock entry Succ [a] {\n"
            "\t\tAssignHavocCmd TA0\n"
            "\t\tAssignHavocCmd TA1\n"
            "\t\tAssignHavocCmd TA2\n"
            "\t\tJumpCmd a\n"
            "\t}\n"
            "\tBlock a Succ [b] {\n"
            "\t\tAssertCmd TA0 \"m0\"\n"
            "\t\tJumpCmd b\n"
            "\t}\n"
            "\tBlock b Succ [c] {\n"
            "\t\tAssertCmd TA1 \"m1\"\n"
            "\t\tJumpCmd c\n"
            "\t}\n"
            "\tBlock c Succ [] {\n"
            "\t\tAssertCmd TA2 \"m2\"\n"
            "\t}",
            syms="TA0:bool\n\tTA1:bool\n\tTA2:bool",
        ),
        path="<s>",
    )
    res = split_asserts(tac.program)
    assert res.was_noop is False
    assert res.asserts_before == 3
    assert len(res.outputs) == 3
    # For each output, inspect its program.
    for out in res.outputs:
        assert out.message == f"m{out.index}"
        # Block containing the live assert still has an AssertCmd.
        live_block = _block(out.program, out.block_id)
        live_cmd = live_block.commands[out.cmd_index]
        assert isinstance(live_cmd, AssertCmd)
        assert live_cmd.predicate == SymbolRef(f"TA{out.index}")
        # Any other AssertCmd in the output has been converted.
        for b in out.program.blocks:
            for idx, cmd in enumerate(b.commands):
                if b.id == out.block_id and idx == out.cmd_index:
                    continue
                assert not isinstance(cmd, AssertCmd)


def test_split_k0_is_noop():
    tac = parse_string(
        _wrap(
            "\tBlock entry Succ [] {\n"
            "\t\tAssignHavocCmd X\n"
            "\t}",
            syms="X:bv256",
        ),
        path="<s>",
    )
    res = split_asserts(tac.program)
    assert res.was_noop is True
    assert res.asserts_before == 0
    assert res.outputs == ()


def test_split_k1_single_output_no_conversions():
    tac = parse_string(
        _wrap(
            "\tBlock entry Succ [] {\n"
            "\t\tAssignHavocCmd TA0\n"
            "\t\tAssertCmd TA0 \"only one\"\n"
            "\t}",
            syms="TA0:bool",
        ),
        path="<s>",
    )
    res = split_asserts(tac.program)
    assert res.was_noop is False
    assert len(res.outputs) == 1
    out = res.outputs[0]
    assert out.message == "only one"
    # The one assert remains; nothing to convert.
    block = _block(out.program, "entry")
    asserts = [c for c in block.commands if isinstance(c, AssertCmd)]
    assumes = [c for c in block.commands if isinstance(c, AssumeExpCmd)]
    assert len(asserts) == 1
    assert len(assumes) == 0


def test_split_preserves_assert_false_predicate():
    # `assert false` at a non-live index becomes `assume false`.
    tac = parse_string(
        _wrap(
            "\tBlock entry Succ [a] {\n"
            "\t\tAssignHavocCmd TA0\n"
            "\t\tJumpCmd a\n"
            "\t}\n"
            "\tBlock a Succ [b] {\n"
            "\t\tAssertCmd false \"boom\"\n"
            "\t\tJumpCmd b\n"
            "\t}\n"
            "\tBlock b Succ [] {\n"
            "\t\tAssertCmd TA0 \"live\"\n"
            "\t}",
            syms="TA0:bool",
        ),
        path="<s>",
    )
    res = split_asserts(tac.program)
    # Output 1 has TA0 live; the `assert false` becomes `assume false`.
    out1 = next(o for o in res.outputs if o.message == "live")
    block_a = _block(out1.program, "a")
    # The block's first command is the converted assume.
    first = block_a.commands[0]
    assert isinstance(first, AssumeExpCmd)
    assert first.condition == ConstExpr("false")


def test_split_coi_prunes_blocks_unreachable_from_entry_to_assert():
    # Build a CFG: entry -> live_block; entry -> dead_block. The live
    # block hosts the assertion. dead_block is not on any path from
    # entry to the live block, so COI should drop it.
    tac = parse_string(
        _wrap(
            "\tBlock entry Succ [live_block, dead_block] {\n"
            "\t\tAssignHavocCmd TA0\n"
            "\t\tJumpiCmd live_block dead_block TA0\n"
            "\t}\n"
            "\tBlock live_block Succ [] {\n"
            "\t\tAssertCmd TA0 \"live\"\n"
            "\t}\n"
            "\tBlock dead_block Succ [] {\n"
            "\t\tAssignHavocCmd Z\n"
            "\t}",
            syms="TA0:bool\n\tZ:bv256",
        ),
        path="<s>",
    )
    res = split_asserts(tac.program)
    assert len(res.outputs) == 1
    out = res.outputs[0]
    ids = _block_ids(out.program)
    # live_block and its predecessor `entry` stay; dead_block is pruned.
    assert "live_block" in ids
    assert "entry" in ids
    assert "dead_block" not in ids


# --- CLI --strategy split --------------------------------------------------


_SPLIT_FIXTURE = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tTA0:bool
\tTA1:bool
}
Program {
\tBlock entry Succ [a] {
\t\tAssignHavocCmd TA0
\t\tAssignHavocCmd TA1
\t\tJumpCmd a
\t}
\tBlock a Succ [b] {
\t\tAssertCmd TA0 "first"
\t\tJumpCmd b
\t}
\tBlock b Succ [] {
\t\tAssertCmd TA1 "second"
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""


def test_cli_split_creates_directory_and_manifest(tmp_path: Path) -> None:
    src = tmp_path / "in.tac"
    src.write_text(_SPLIT_FIXTURE, encoding="utf-8")
    out_dir = tmp_path / "out" / "split"  # nonexistent nested path

    runner = CliRunner()
    res = runner.invoke(
        app,
        ["ua", str(src), "-o", str(out_dir), "--strategy", "split", "--plain"],
    )
    assert res.exit_code == 0, res.output

    # Directory got created.
    assert out_dir.is_dir()
    files = sorted(p.name for p in out_dir.iterdir())
    assert "manifest.json" in files
    tac_files = [f for f in files if f.endswith(".tac")]
    assert tac_files == ["assert_00.tac", "assert_01.tac"]

    # Manifest parses and matches.
    manifest = json.loads((out_dir / "manifest.json").read_text())
    assert manifest["strategy"] == "split"
    assert manifest["asserts_before"] == 2
    assert [o["file"] for o in manifest["outputs"]] == tac_files
    assert [o["message"] for o in manifest["outputs"]] == ["first", "second"]


def test_cli_split_rejects_existing_file_as_output(tmp_path: Path) -> None:
    src = tmp_path / "in.tac"
    src.write_text(_SPLIT_FIXTURE, encoding="utf-8")
    existing_file = tmp_path / "not_a_dir.tac"
    existing_file.write_text("", encoding="utf-8")

    runner = CliRunner()
    res = runner.invoke(
        app,
        [
            "ua",
            str(src),
            "-o",
            str(existing_file),
            "--strategy",
            "split",
            "--plain",
        ],
    )
    assert res.exit_code == 1
    assert "not a directory" in res.stdout.lower()


def test_cli_split_requires_output(tmp_path: Path) -> None:
    src = tmp_path / "in.tac"
    src.write_text(_SPLIT_FIXTURE, encoding="utf-8")
    runner = CliRunner()
    res = runner.invoke(app, ["ua", str(src), "--strategy", "split", "--plain"])
    assert res.exit_code == 1
    assert "--strategy split requires -o" in res.stdout
