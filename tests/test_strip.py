"""Tests for ctac.transform.strip and the `ctac strip` CLI command."""

from __future__ import annotations

import json

from typer.testing import CliRunner

from ctac.ast.nodes import AnnotationCmd, AssertCmd, LabelCmd
from ctac.parse import parse_string
from ctac.tool.main import app
from ctac.transform.strip import strip_tac


def _annotation(name: str, value, *, key_type: str = "some.Type") -> str:
    obj = {
        "key": {"name": name, "type": key_type, "erasureStrategy": "Canonical"},
        "value": value,
    }
    return "AnnotationCmd JSON" + json.dumps(obj, separators=(",", ":"))


def _meta_entry(name: str, value) -> dict:
    return {
        "key": {"name": name, "type": "some.Type", "erasureStrategy": "Canonical"},
        "value": value,
    }


def _wrap(body: str, metas: dict | None = None) -> str:
    metas_text = json.dumps(metas if metas is not None else {"0": []})
    return f"""TACSymbolTable {{
\tUserDefined {{
\t}}
\tBuiltinFunctions {{
\t}}
\tUninterpretedFunctions {{
\t}}
\tR0:bv256
\tB0:bool
}}
Program {{
{body}
}}
Axioms {{
}}
Metas {metas_text}
"""


def _cmds(program, block_id):
    for b in program.blocks:
        if b.id == block_id:
            return b.commands
    raise AssertionError(f"no block {block_id!r} in program")


def test_metas_keep_key_survives_strip_key_dropped():
    metas = {
        "1": [_meta_entry("sbf.bytecode.address", 164320)],
        "2": [_meta_entry("cvl.range", {"specFile": "programs/x/spec.rs"})],
        "3": [
            _meta_entry("sbf.bytecode.address", 99),
            _meta_entry("tac.assert.id", 100001),
        ],
    }
    body = """\tBlock entry Succ [] {
\t\tAssignExpCmd:1 R0 0x1
\t\tAssignExpCmd:2 R0 0x2
\t\tAssignExpCmd:3 R0 0x3
\t}"""
    tac = parse_string(_wrap(body, metas), path="<s>")
    res = strip_tac(tac)
    assert set(res.metas) == {"1", "3"}
    assert [e["key"]["name"] for e in res.metas["3"]] == ["sbf.bytecode.address"]
    assert res.report.kept_meta["sbf.bytecode.address"] == 2
    assert res.report.dropped_meta["cvl.range"] == 1
    assert res.report.dropped_meta["tac.assert.id"] == 1


def test_emptied_meta_index_removes_cmd_suffix():
    metas = {"7": [_meta_entry("sbf.source.segment", {"content": "secret"})]}
    body = """\tBlock entry Succ [] {
\t\tAssignExpCmd:7 R0 0x1
\t}"""
    tac = parse_string(_wrap(body, metas), path="<s>")
    res = strip_tac(tac)
    assert res.metas == {}
    (cmd,) = _cmds(res.program, "entry")
    assert cmd.meta_index is None
    assert cmd.raw.startswith("AssignExpCmd R0")
    assert res.report.meta_suffixes_removed == 1


def test_surviving_meta_index_keeps_cmd_suffix():
    metas = {"7": [_meta_entry("sbf.bytecode.address", 4)]}
    body = """\tBlock entry Succ [] {
\t\tAssignExpCmd:7 R0 0x1
\t}"""
    tac = parse_string(_wrap(body, metas), path="<s>")
    res = strip_tac(tac)
    (cmd,) = _cmds(res.program, "entry")
    assert cmd.meta_index == 7
    assert cmd.raw.startswith("AssignExpCmd:7 ")
    assert res.report.meta_suffixes_removed == 0


def test_unknown_meta_key_dropped_and_reported():
    metas = {"1": [_meta_entry("future.prover.key", {"x": 1})]}
    body = """\tBlock entry Succ [] {
\t\tAssignExpCmd:1 R0 0x1
\t}"""
    tac = parse_string(_wrap(body, metas), path="<s>")
    res = strip_tac(tac)
    assert res.metas == {}
    assert res.report.unknown_keys == {"future.prover.key"}


def test_inline_annotation_policy():
    keep_call = _annotation(
        "debug.sbf.external_call", "__rust_alloc", key_type="java.lang.String"
    )
    keep_memcpy = _annotation(
        "debug.sbf.function_start",
        "memcpy(dst=Stack{-104}, src=non-stack, len=1)",
        key_type="java.lang.String",
    )
    drop_struct = _annotation(
        "debug.sbf.function_start",
        {"name": "kvault::secret_fn", "mangledName": "_ZN..."},
        key_type="sbf.tac.SbfInlinedFuncStartAnnotation",
    )
    drop_snippet = _annotation("snippet.cmd", {"displayMessage": "CVT_alloc_slice"})
    drop_rule_loc = _annotation(
        "sbf.rule.location", {"filepath": "programs/x/spec.rs", "lineNumber": 9}
    )
    body = f"""\tBlock entry Succ [] {{
\t\t{keep_call}
\t\t{keep_memcpy}
\t\t{drop_struct}
\t\t{drop_snippet}
\t\t{drop_rule_loc}
\t\tAssignExpCmd R0 0x1
\t}}"""
    tac = parse_string(_wrap(body), path="<s>")
    res = strip_tac(tac)
    cmds = _cmds(res.program, "entry")
    payloads = [c.payload for c in cmds if isinstance(c, AnnotationCmd)]
    assert len(payloads) == 2
    assert any("__rust_alloc" in p for p in payloads)
    assert any("memcpy" in p for p in payloads)
    assert res.report.dropped_annotations["debug.sbf.function_start"] == 1
    assert res.report.dropped_annotations["snippet.cmd"] == 1
    assert res.report.dropped_annotations["sbf.rule.location"] == 1


def test_assert_messages_replaced_sequentially():
    body = """\tBlock entry Succ [] {
\t\tAssertCmd B0 "cvlr_assert!(secret_field < other_secret)"
\t\tAssertCmd B0
\t\tAssertCmd B0 "assertion failed"
\t}"""
    tac = parse_string(_wrap(body), path="<s>")
    res = strip_tac(tac)
    asserts = [c for c in _cmds(res.program, "entry") if isinstance(c, AssertCmd)]
    assert [a.message for a in asserts] == ["assert 1", None, "assert 3"]
    assert asserts[0].raw == 'AssertCmd B0 "assert 1"'
    assert res.report.assert_messages_replaced == 2


def test_label_cmd_preserved():
    body = """\tBlock entry Succ [] {
\t\tLabelCmd "Parallel assignment for R0 := R0"
\t\tAssignExpCmd R0 0x1
\t}"""
    tac = parse_string(_wrap(body), path="<s>")
    res = strip_tac(tac)
    cmds = _cmds(res.program, "entry")
    assert any(isinstance(c, LabelCmd) for c in cmds)


def test_strip_all_drops_everything():
    metas = {"1": [_meta_entry("sbf.bytecode.address", 4)]}
    keep_call = _annotation(
        "debug.sbf.external_call", "__rust_alloc", key_type="java.lang.String"
    )
    body = f"""\tBlock entry Succ [] {{
\t\t{keep_call}
\t\tAssignExpCmd:1 R0 0x1
\t}}"""
    tac = parse_string(_wrap(body, metas), path="<s>")
    res = strip_tac(tac, strip_all=True)
    assert res.metas == {}
    cmds = _cmds(res.program, "entry")
    assert not any(isinstance(c, AnnotationCmd) for c in cmds)
    (cmd,) = cmds
    assert cmd.meta_index is None
    assert cmd.raw.startswith("AssignExpCmd R0")


def test_output_reparses():
    from ctac.parse import render_tac_file
    import dataclasses

    metas = {
        "1": [_meta_entry("sbf.bytecode.address", 4)],
        "2": [_meta_entry("cvl.range", {"specFile": "x.rs"})],
    }
    body = f"""\tBlock entry Succ [] {{
\t\t{_annotation("snippet.cmd", {"displayMessage": "m"})}
\t\tAssignExpCmd:1 R0 0x1
\t\tAssertCmd:2 B0 "secret"
\t}}"""
    tac = parse_string(_wrap(body, metas), path="<s>")
    res = strip_tac(tac)
    text = render_tac_file(
        dataclasses.replace(tac, metas=res.metas), program=res.program
    )
    reparsed = parse_string(text, path="<roundtrip>")
    assert "secret" not in text
    assert "snippet.cmd" not in text
    (a,) = [
        c
        for b in reparsed.program.blocks
        for c in b.commands
        if isinstance(c, AssertCmd)
    ]
    assert a.message == "assert 1"
    assert a.meta_index is None  # cvl.range entry died, suffix removed


def test_cli_report_rows(tmp_path):
    metas = {
        "1": [_meta_entry("sbf.bytecode.address", 4)],
        "2": [_meta_entry("cvl.range", {"specFile": "x.rs"})],
    }
    body = """\tBlock entry Succ [] {
\t\tAssignExpCmd:1 R0 0x1
\t\tAssertCmd:2 B0 "secret"
\t}"""
    src = tmp_path / "in.tac"
    src.write_text(_wrap(body, metas), encoding="utf-8")
    out = tmp_path / "out.tac"
    runner = CliRunner()
    result = runner.invoke(
        app, ["strip", str(src), "-o", str(out), "--plain", "--report"]
    )
    assert result.exit_code == 0, result.output
    assert "  metas_kept: 1" in result.output
    assert "  metas_dropped: 1" in result.output
    assert "  assert_messages_replaced: 1" in result.output
    assert "  meta_suffixes_removed: 1" in result.output
    text = out.read_text(encoding="utf-8")
    assert "secret" not in text
    assert "sbf.bytecode.address" in text
