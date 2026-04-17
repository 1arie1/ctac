from __future__ import annotations

from ctac.tac_ast.nodes import AssertCmd
from ctac.tool.main import _source_prefix_for_cmd


def test_source_prefix_uses_cvl_range() -> None:
    cmd = AssertCmd(raw='AssertCmd B1 "x"', predicate="B1", message="x", meta_index=42)
    metas = {
        "42": [
            {
                "key": {"name": "cvl.range", "type": "utils.Range"},
                "value": {
                    "#class": "utils.Range.Range",
                    "specFile": "programs/liquidity/src/certora/specs/solvency.rs",
                    "start": {"line": 161, "charByteOffset": 0},
                    "end": {"line": 162, "charByteOffset": 0},
                },
            }
        ]
    }
    got = _source_prefix_for_cmd(cmd, metas, max_path_chars=18)
    assert got == "…/solvency.rs:161"

