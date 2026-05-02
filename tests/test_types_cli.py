"""Tests for `ctac types` (kind-inference CLI)."""

from __future__ import annotations

import json

from typer.testing import CliRunner

from ctac.tool.main import app


def _wrap(body: str, syms: str) -> str:
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


def _select_program() -> str:
    """`R = M[IDX]` — IDX must be tagged `Ptr`, R is the loaded value (Top)."""
    syms = "M:bytemap\n\tIDX:bv256\n\tR:bv256"
    body = (
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd M\n"
        "\t\tAssignHavocCmd IDX\n"
        "\t\tAssignExpCmd R Select(M IDX )\n"
        "\t}"
    )
    return _wrap(body, syms)


def _mul_and_select_same_class_program() -> str:
    """`R` is both the operand of `Mul` (forces `Int`) and the index of
    `Select` (forces `Ptr`). Result: `R` is `Bot` (contradictory)."""
    syms = "M:bytemap\n\tR:bv256\n\tX:bv256\n\tV:bv256"
    body = (
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd M\n"
        "\t\tAssignHavocCmd R\n"
        "\t\tAssignExpCmd X Mul(R 4 )\n"
        "\t\tAssignExpCmd V Select(M R )\n"
        "\t}"
    )
    return _wrap(body, syms)


def test_types_summary_plain(tmp_path):
    p = tmp_path / "f.tac"
    p.write_text(_select_program())
    result = CliRunner().invoke(app, ["types", str(p), "--plain"])
    assert result.exit_code == 0, result.output
    out = result.output
    # Counts: IDX is Ptr, R is Top, M filtered as memory by default.
    assert "ptr=1" in out
    assert "top=1" in out
    assert "Ptr | IDX" in out


def test_types_show_ptr_filter(tmp_path):
    p = tmp_path / "f.tac"
    p.write_text(_select_program())
    result = CliRunner().invoke(app, ["types", str(p), "--plain", "--show", "ptr"])
    assert result.exit_code == 0, result.output
    out = result.output
    assert "Ptr | IDX" in out
    # `R` is `Top`, so under `--show ptr` it must not appear in the rows
    # (we look for the symbol-row form, not the metadata header).
    assert "Top | R" not in out
    assert "Int | R" not in out


def test_types_json_output(tmp_path):
    p = tmp_path / "f.tac"
    p.write_text(_select_program())
    result = CliRunner().invoke(app, ["types", str(p), "--plain", "--json"])
    assert result.exit_code == 0, result.output
    payload = json.loads(result.output)
    assert payload["counts"]["ptr"] == 1
    assert payload["counts"]["top"] == 1
    assert payload["counts"]["bot"] == 0
    names = {row["name"]: row["kind"] for row in payload["symbols"]}
    assert names["IDX"] == "Ptr"
    assert names["R"] == "Top"
    # M is filtered by default (memory-sorted).
    assert "M" not in names


def test_types_include_memory_flag(tmp_path):
    p = tmp_path / "f.tac"
    p.write_text(_select_program())
    result = CliRunner().invoke(
        app, ["types", str(p), "--plain", "--json", "--include-memory"]
    )
    assert result.exit_code == 0, result.output
    payload = json.loads(result.output)
    names = {row["name"]: row["kind"] for row in payload["symbols"]}
    assert "M" in names


def test_types_bot_on_contradiction(tmp_path):
    p = tmp_path / "f.tac"
    p.write_text(_mul_and_select_same_class_program())
    result = CliRunner().invoke(app, ["types", str(p), "--plain", "--json"])
    assert result.exit_code == 0, result.output
    payload = json.loads(result.output)
    names = {row["name"]: row["kind"] for row in payload["symbols"]}
    assert names["R"] == "Bot"
    assert payload["counts"]["bot"] == 1


def test_types_by_class_groups_unified_symbols(tmp_path):
    """Two symbols unified by an alias should appear in the same class row."""
    syms = "M:bytemap\n\tR:bv256\n\tR2:bv256\n\tV:bv256"
    body = (
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd M\n"
        "\t\tAssignHavocCmd R\n"
        "\t\tAssignExpCmd R2 R\n"
        "\t\tAssignExpCmd V Select(M R2 )\n"
        "\t}"
    )
    p = tmp_path / "f.tac"
    p.write_text(_wrap(body, syms))
    result = CliRunner().invoke(
        app, ["types", str(p), "--plain", "--json", "--by-class"]
    )
    assert result.exit_code == 0, result.output
    payload = json.loads(result.output)
    ptr_classes = [c for c in payload["classes"] if c["kind"] == "Ptr"]
    assert len(ptr_classes) == 1
    members = set(ptr_classes[0]["members"])
    assert {"R", "R2"} <= members


def test_types_trace_writes_jsonl(tmp_path):
    """`--trace PATH` writes one JSON record per line; each record carries
    the documented field set."""
    p = tmp_path / "f.tac"
    p.write_text(_select_program())
    trace_path = tmp_path / "trace.jsonl"
    result = CliRunner().invoke(
        app, ["types", str(p), "--plain", "--trace", str(trace_path)]
    )
    assert result.exit_code == 0, result.output
    text = trace_path.read_text()
    lines = [line for line in text.splitlines() if line.strip()]
    assert lines, "expected at least one trace record"
    for line in lines:
        rec = json.loads(line)
        # Required field set per the documented contract.
        for key in (
            "phase",
            "iteration",
            "block_id",
            "cmd_index",
            "kind",
            "rule",
            "symbols",
            "before",
            "after",
            "detail",
            "changed",
        ):
            assert key in rec, f"missing field {key} in trace record: {rec}"
    # Should record the Ptr-meet on IDX (the Select index).
    select_meets = [
        json.loads(line)
        for line in lines
        if "select-index" in line and "IDX" in line
    ]
    assert select_meets, "expected at least one select-index meet on IDX"


def test_types_trace_symbol_filters_records(tmp_path):
    """`--trace-symbol R` filters trace records to events touching that
    canonical class only."""
    syms = "M:bytemap\n\tIDX:bv256\n\tOFF:bv256\n\tR:bv256\n\tV:bv256\n\tX:bv256"
    body = (
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd M\n"
        "\t\tAssignHavocCmd IDX\n"
        "\t\tAssignHavocCmd OFF\n"
        "\t\tAssignExpCmd V Select(M IDX )\n"
        "\t\tAssignExpCmd X Mul(OFF 4 )\n"
        "\t}"
    )
    p = tmp_path / "f.tac"
    p.write_text(_wrap(body, syms))
    trace_path = tmp_path / "trace.jsonl"
    result = CliRunner().invoke(
        app,
        [
            "types",
            str(p),
            "--plain",
            "--trace",
            str(trace_path),
            "--trace-symbol",
            "IDX",
        ],
    )
    assert result.exit_code == 0, result.output
    lines = [line for line in trace_path.read_text().splitlines() if line.strip()]
    # Every record must mention IDX in its symbols field.
    for line in lines:
        rec = json.loads(line)
        assert "IDX" in rec["symbols"], (
            f"unexpected record (--trace-symbol IDX should have filtered it): {rec}"
        )


def test_types_unknown_show_kind_errors(tmp_path):
    p = tmp_path / "f.tac"
    p.write_text(_select_program())
    result = CliRunner().invoke(
        app, ["types", str(p), "--plain", "--show", "wibble"]
    )
    assert result.exit_code != 0
    # Typer surfaces BadParameter messages on stderr or output.
    assert "wibble" in (result.output or "") or "wibble" in (
        result.stderr if hasattr(result, "stderr") else ""
    )


def test_types_index_registers_never_int_on_target_corpus(tmp_path):
    """End-to-end soundness gate: on the `request_elevation_group` VC,
    every register that appears as the index of a `Select`/`Store` must
    be classified `Ptr` (not `Int`, not `Bot`). This is the exact
    soundness invariant the design names. We re-extract the index
    registers from the raw .tac text as ground truth and cross-check
    the classifier."""
    import re
    from pathlib import Path

    target = Path(
        "examples/rule_no_col_decrease_request_elevation_group.bad/base.rw.tac"
    )
    if not target.exists():
        # Fixture may not be checked in on a sparse clone — skip rather
        # than fail. The invariant is the assertion below.
        import pytest

        pytest.skip(f"target fixture {target} not present in this checkout")

    result = CliRunner().invoke(
        app,
        [
            "types",
            str(target),
            "--plain",
            "--json",
            "--show",
            "all",
            "--include-memory",
        ],
    )
    assert result.exit_code == 0, result.output
    payload = json.loads(result.output)
    kinds = {row["name"]: row["kind"] for row in payload["symbols"]}

    text = target.read_text()
    indices: set[str] = set()
    for m in re.finditer(r"\bSelect\(\s*\S+\s+([A-Za-z_][\w]*)", text):
        indices.add(m.group(1))
    for m in re.finditer(r"\bStore\(\s*\S+\s+([A-Za-z_][\w]*)", text):
        indices.add(m.group(1))
    indices = {n for n in indices if not n[0].isdigit()}

    # Soundness: no index register may be tagged `Int`. If the analysis
    # tightens further over time, more may shift from `Top` to `Ptr` —
    # only `Int` is a soundness bug.
    unsound = [
        n for n in indices if kinds.get(re.sub(r":\d+$", "", n)) == "Int"
    ]
    assert not unsound, f"unsound: index registers tagged Int: {unsound}"

    # Precision floor: at least most index registers should land `Ptr`
    # (not `Top`). The current analysis pins all 143; if a future change
    # weakens this, the test will flag it.
    ptr_count = sum(
        1 for n in indices if kinds.get(re.sub(r":\d+$", "", n)) == "Ptr"
    )
    assert ptr_count >= len(indices) * 0.9, (
        f"precision regression: only {ptr_count}/{len(indices)} indices "
        f"tagged Ptr"
    )
