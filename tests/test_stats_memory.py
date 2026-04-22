"""Tests for the ``memory.*`` section emitted by ``ctac stats``."""

from __future__ import annotations

from ctac.parse import parse_string
from ctac.tool.commands_stats import collect_tac_stats


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


def _stats_map(stats) -> dict[str, object]:
    return {e.path: e.value.value for e in stats.entries()}


def test_memory_section_reports_ro_counts_for_bytemap_target():
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd M16\n"
            "\t\tAssignExpCmd R1 Select(M16 0x10)\n"
            "\t\tAssignExpCmd R2 Select(M16 0x20)\n"
            "\t}",
            "R1:bv256\n\tR2:bv256\n\tM16:bytemap",
        ),
        path="<s>",
    )
    m = _stats_map(collect_tac_stats(tac))
    assert m["memory.bytemap_symbols"] == 1
    assert m["memory.capability"] == "bytemap-ro"
    assert m["memory.havocs"] == 1
    assert m["memory.select_reads"] == 2
    assert m["memory.store_writes"] == 0
    assert m["memory.by_symbol.M16.selects"] == 2
    assert m["memory.by_symbol.M16.havocs"] == 1


def test_memory_section_omits_per_symbol_when_unused():
    """Declared-but-unused memory symbols appear as FREE and don't get a
    per-symbol breakdown (they'd all be zero)."""
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd R0\n"
            "\t}",
            "R0:bv256\n\tM99:bytemap",
        ),
        path="<s>",
    )
    m = _stats_map(collect_tac_stats(tac))
    assert m["memory.bytemap_symbols"] == 1
    assert m["memory.capability"] == "bytemap-free"
    # by_symbol.* entries only emitted for symbols with havocs or reads.
    assert not any(k.startswith("memory.by_symbol.") for k in m)


def test_memory_section_free_when_no_bytemap_symbols():
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd R0\n"
            "\t}",
            "R0:bv256",
        ),
        path="<s>",
    )
    m = _stats_map(collect_tac_stats(tac))
    assert m["memory.bytemap_symbols"] == 0
    assert m["memory.capability"] == "bytemap-free"
    # No detail counters emitted when there are no memory symbols at all.
    assert "memory.havocs" not in m
    assert "memory.select_reads" not in m
