"""Tests for ctac.transform.pin_manifest."""

from __future__ import annotations

import json

import pytest

from ctac.parse import parse_string
from ctac.transform.pin import PinPlan, enumerate as pin_enumerate
from ctac.transform.pin_manifest import (
    SCHEMA_VERSION,
    Manifest,
    read_manifest,
    summarize_manifest,
    write_manifest,
)


def _wrap(blocks_text: str, *, syms: str = "B0:bool") -> str:
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
{blocks_text}
}}
Axioms {{
}}
Metas {{
  "0": []
}}
"""


def _two_pred_join():
    return parse_string(
        _wrap(
            "\tBlock e Succ [p1, p2] {\n"
            "\t\tJumpiCmd p1 p2 B0\n"
            "\t}\n"
            "\tBlock p1 Succ [j] {\n"
            "\t\tJumpCmd j\n"
            "\t}\n"
            "\tBlock p2 Succ [j] {\n"
            "\t\tJumpCmd j\n"
            "\t}\n"
            "\tBlock j Succ [exit] {\n"
            "\t\tJumpCmd exit\n"
            "\t}\n"
            "\tBlock exit Succ [] {\n"
            "\t\tNoSuchCmd\n"
            "\t}\n"
        ),
        path="<s>",
    )


def test_write_and_read_roundtrip(tmp_path):
    tac = _two_pred_join()
    cs = pin_enumerate(tac.program, PinPlan(splits=("j",)))
    write_manifest(
        cs,
        tmp_path,
        source_tac=tac,
        source_path="test.tac",
        command="ctac pin test.tac --split j",
    )
    m = read_manifest(tmp_path)
    assert m.schema_version == SCHEMA_VERSION
    assert m.source == "test.tac"
    assert m.command == "ctac pin test.tac --split j"
    assert len(m.cases) == 2
    assert len(m.splits) == 1


def test_write_emits_one_tac_per_case(tmp_path):
    tac = _two_pred_join()
    cs = pin_enumerate(tac.program, PinPlan(splits=("j",)))
    write_manifest(cs, tmp_path, source_tac=tac)
    tac_files = list(tmp_path.glob("*.tac"))
    assert len(tac_files) == 2
    # Each .tac file should be parseable.
    from ctac.parse import parse_path
    for f in tac_files:
        parse_path(f)  # no exception


def test_write_descriptive_name_style(tmp_path):
    tac = _two_pred_join()
    cs = pin_enumerate(tac.program, PinPlan(splits=("j",)))
    m = write_manifest(cs, tmp_path, source_tac=tac, name_style="descriptive")
    # Filenames should mention the kept predecessor short name.
    filenames = {c.filename for c in m.cases}
    assert any("p1" in f for f in filenames)
    assert any("p2" in f for f in filenames)


def test_write_index_name_style(tmp_path):
    tac = _two_pred_join()
    cs = pin_enumerate(tac.program, PinPlan(splits=("j",)))
    m = write_manifest(cs, tmp_path, source_tac=tac, name_style="index")
    filenames = {c.filename for c in m.cases}
    assert "case_001.tac" in filenames
    assert "case_002.tac" in filenames


def test_write_creates_dir_if_missing(tmp_path):
    tac = _two_pred_join()
    cs = pin_enumerate(tac.program, PinPlan(splits=("j",)))
    out = tmp_path / "deep" / "dir"
    write_manifest(cs, out, source_tac=tac)
    assert (out / "manifest.json").is_file()


def test_read_missing_manifest_raises(tmp_path):
    with pytest.raises(FileNotFoundError):
        read_manifest(tmp_path)


def test_read_unsupported_schema_raises(tmp_path):
    (tmp_path / "manifest.json").write_text(
        json.dumps({"schema_version": 999})
    )
    with pytest.raises(ValueError, match="schema_version"):
        read_manifest(tmp_path)


def test_summarize_basic(tmp_path):
    tac = _two_pred_join()
    cs = pin_enumerate(tac.program, PinPlan(splits=("j",)))
    m = write_manifest(
        cs, tmp_path, source_tac=tac, source_path="test.tac",
        command="ctac pin test.tac --split j"
    )
    out = summarize_manifest(m)
    assert "test.tac" in out
    assert "ctac pin" in out
    assert "Splits" in out
    assert "Cases" in out
    assert "p1" in out  # at least one kept predecessor mentioned


def test_summarize_plain_strips_decorations(tmp_path):
    tac = _two_pred_join()
    cs = pin_enumerate(tac.program, PinPlan(splits=("j",)))
    m = write_manifest(cs, tmp_path, source_tac=tac, source_path="test.tac")
    out = summarize_manifest(m, plain=True)
    # Plain mode shouldn't include the "# pin manifest" header line.
    assert "# pin manifest" not in out


def test_summarize_marks_missing_source(tmp_path):
    tac = _two_pred_join()
    cs = pin_enumerate(tac.program, PinPlan(splits=("j",)))
    m = write_manifest(
        cs, tmp_path, source_tac=tac, source_path="/no/such/path.tac"
    )
    out = summarize_manifest(m, manifest_dir=tmp_path)
    assert "(missing)" in out


def test_manifest_to_from_json_dict_roundtrip():
    """Schema serialization is bijective for the typed Manifest."""
    m = Manifest(
        schema_version=1,
        source="x.tac",
        command="ctac pin x.tac",
        drops=("a", "b"),
        binds={"B0": "false"},
        splits=(),
        cases=(),
        block_short_names={"a": "A", "b": "B"},
        pruned_count=0,
    )
    d = m.to_json_dict()
    m2 = Manifest.from_json_dict(d)
    assert m2 == m
