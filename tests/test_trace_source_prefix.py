from __future__ import annotations

from ctac.ast.nodes import AssertCmd, AssignExpCmd, ConstExpr, SymbolRef
from ctac.ast.run_format import bytecode_addr_for_cmd
from ctac.tool.main import _source_prefix_for_cmd


def test_source_prefix_uses_cvl_range() -> None:
    cmd = AssertCmd(
        raw='AssertCmd B1 "x"',
        predicate=SymbolRef("B1"),
        message="x",
        meta_index=42,
    )
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


def _ae_with_meta(idx: int) -> AssignExpCmd:
    return AssignExpCmd(
        raw=f"AssignExpCmd:{idx} R0 0x1",
        lhs="R0",
        rhs=ConstExpr("0x1"),
        meta_index=idx,
    )


def test_bytecode_addr_tac_dump_shape() -> None:
    """TAC dump format: ``metas[idx]`` is a list of key/value entry dicts."""
    cmd = _ae_with_meta(7)
    metas = {
        "7": [
            {
                "key": {
                    "name": "sbf.bytecode.address",
                    "type": "java.lang.Long",
                    "erasureStrategy": "Canonical",
                },
                "value": 0xea60,
            }
        ]
    }
    assert bytecode_addr_for_cmd(cmd, metas) == 0xea60


def test_bytecode_addr_sbf_json_shape() -> None:
    """SBF compiler JSON: ``metas[idx]`` is a flat dict with the
    underscore-spelled key ``sbf_bytecode_address``."""
    cmd = _ae_with_meta(0)
    metas = {
        "0": {"set_global": "", "sbf_bytecode_address": 389256},
    }
    assert bytecode_addr_for_cmd(cmd, metas) == 389256


def test_bytecode_addr_returns_none_when_missing() -> None:
    cmd = _ae_with_meta(3)
    # idx present but neither key spelling
    assert bytecode_addr_for_cmd(cmd, {"3": {"other_key": 1}}) is None
    assert bytecode_addr_for_cmd(cmd, {"3": []}) is None
    # idx absent
    assert bytecode_addr_for_cmd(cmd, {}) is None
    # cmd has no meta_index
    assert bytecode_addr_for_cmd(_ae_with_meta(0).__class__(
        raw="AssignExpCmd R0 0x1", lhs="R0", rhs=ConstExpr("0x1"),
    ), {}) is None

