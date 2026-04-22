"""Tests for symbol-sort parsing and bytemap classification."""

from __future__ import annotations

from ctac.analysis import (
    BytemapCapability,
    SymbolKind,
    classify_bytemap_usage,
    classify_sort,
    parse_symbol_sorts,
)
from ctac.parse import parse_string


SYM_TABLE = """TACSymbolTable {
\tUserDefined {
\t\tUninterpSort skey
\t}
\tBuiltinFunctions {
\t\tsafe_math_narrow_bv256:JSON{"#class":"vc.data.TACBuiltInFunction.SafeMathNarrow.Implicit","returnSort":{"bits":256}}
\t}
\tUninterpretedFunctions {
\t}
\tR10:bv256
\tR11:bv256
\tB0:bool
\tI5:int
\tI5:int:2
\tM16:bytemap
\tM_23:bytemap
\tG0:ghostmap
}
"""


def test_parse_symbol_sorts_skips_nested_blocks_and_json():
    sorts = parse_symbol_sorts(SYM_TABLE)
    # Regular symbols + DSA-revisioned symbols get through.
    assert sorts["R10"] == "bv256"
    assert sorts["B0"] == "bool"
    assert sorts["I5"] == "int"
    assert sorts["M16"] == "bytemap"
    assert sorts["M_23"] == "bytemap"
    assert sorts["G0"] == "ghostmap"
    # Nested-section markers and JSON-annotated builtins must not show up.
    assert "safe_math_narrow_bv256" not in sorts
    assert "UninterpSort" not in sorts


def test_classify_sort_memory_vs_scalar():
    assert classify_sort("bv256") is SymbolKind.SCALAR
    assert classify_sort("int") is SymbolKind.SCALAR
    assert classify_sort("bool") is SymbolKind.SCALAR
    assert classify_sort("bytemap") is SymbolKind.MEMORY
    assert classify_sort("ghostmap") is SymbolKind.MEMORY
    # Unknown sorts default to SCALAR.
    assert classify_sort("mystery") is SymbolKind.SCALAR


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


def test_classify_bytemap_usage_free():
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd R0\n"
            "\t}",
            "R0:bv256",
        ),
        path="<s>",
    )
    assert (
        classify_bytemap_usage(tac.program, tac.symbol_sorts)
        is BytemapCapability.BYTEMAP_FREE
    )


def test_classify_bytemap_usage_declared_but_unused_is_free():
    """Bytemap declared in the symbol table but never referenced: FREE.

    Matches what an SMT encoder actually sees — classification is about
    reachable memory usage, not stale symbol-table entries.
    """
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd R0\n"
            "\t}",
            "R0:bv256\n\tM16:bytemap",
        ),
        path="<s>",
    )
    assert (
        classify_bytemap_usage(tac.program, tac.symbol_sorts)
        is BytemapCapability.BYTEMAP_FREE
    )


def test_classify_bytemap_usage_read_only():
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd M16\n"
            "\t\tAssignExpCmd R1 Select(M16 0x10)\n"
            "\t}",
            "R1:bv256\n\tM16:bytemap",
        ),
        path="<s>",
    )
    assert (
        classify_bytemap_usage(tac.program, tac.symbol_sorts)
        is BytemapCapability.BYTEMAP_RO
    )


def test_classify_bytemap_usage_store_is_rw():
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd M16\n"
            "\t\tAssignExpCmd M16 Store(M16 0x10 0x42)\n"
            "\t}",
            "M16:bytemap",
        ),
        path="<s>",
    )
    assert (
        classify_bytemap_usage(tac.program, tac.symbol_sorts)
        is BytemapCapability.BYTEMAP_RW
    )


def test_parser_populates_symbol_sorts_field_on_tac_file():
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd M16\n"
            "\t}",
            "R0:bv256\n\tM16:bytemap",
        ),
        path="<s>",
    )
    assert tac.symbol_sorts["R0"] == "bv256"
    assert tac.symbol_sorts["M16"] == "bytemap"
