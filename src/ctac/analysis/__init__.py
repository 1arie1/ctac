"""Data-flow analyses over TAC programs."""

from ctac.analysis.defuse import extract_def_use
from ctac.analysis.normalize import normalize_program_symbols
from ctac.analysis.model import BytemapCapability
from ctac.analysis.passes import (
    analyze_control_dependence,
    analyze_dsa,
    analyze_liveness,
    analyze_reaching_definitions,
    analyze_use_before_def,
    classify_bytemap_usage,
    eliminate_dead_assignments,
    eliminate_useless_assumes,
    remove_true_asserts,
)
from ctac.analysis.symbols import (
    SymbolKind,
    classify_sort,
    parse_symbol_sorts,
)

__all__ = [
    "BytemapCapability",
    "SymbolKind",
    "analyze_control_dependence",
    "analyze_dsa",
    "analyze_liveness",
    "analyze_reaching_definitions",
    "analyze_use_before_def",
    "classify_bytemap_usage",
    "classify_sort",
    "eliminate_dead_assignments",
    "eliminate_useless_assumes",
    "extract_def_use",
    "normalize_program_symbols",
    "parse_symbol_sorts",
    "remove_true_asserts",
]
