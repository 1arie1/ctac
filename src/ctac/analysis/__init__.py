"""Data-flow analyses over TAC programs."""

from ctac.analysis.defuse import extract_def_use
from ctac.analysis.normalize import normalize_program_symbols
from ctac.analysis.passes import (
    analyze_control_dependence,
    analyze_dsa,
    analyze_liveness,
    analyze_reaching_definitions,
    analyze_use_before_def,
    eliminate_dead_assignments,
)

__all__ = [
    "analyze_control_dependence",
    "analyze_dsa",
    "analyze_liveness",
    "analyze_reaching_definitions",
    "analyze_use_before_def",
    "eliminate_dead_assignments",
    "extract_def_use",
    "normalize_program_symbols",
]
