"""Abstract interpreter framework: frontier-based forward sweep over DSA, loop-free TAC."""

from ctac.analysis.abs_int.framework import Frontier, run
from ctac.analysis.abs_int.protocol import Domain
from ctac.analysis.abs_int.domains.poly_deg import (
    BOT,
    TOP,
    ExprDegree,
    PolyDegResult,
    PolynomialDegreeDomain,
    analyze_polynomial_degree,
    evaluate_degree,
)
from ctac.analysis.abs_int.domains.interval import (
    ExprInterval,
    Interval,
    IntervalDomain,
    IntervalResult,
    analyze_intervals,
)
from ctac.analysis.abs_int.materialize import (
    MaterializeReport,
    materialize_intervals,
)
from ctac.analysis.abs_int.explain import (
    DefSite,
    RefinementSite,
    VarExplanation,
    explain_var,
    format_var_explanation,
)

__all__ = [
    "BOT",
    "DefSite",
    "Domain",
    "ExprDegree",
    "ExprInterval",
    "Frontier",
    "Interval",
    "IntervalDomain",
    "IntervalResult",
    "MaterializeReport",
    "PolyDegResult",
    "PolynomialDegreeDomain",
    "RefinementSite",
    "TOP",
    "VarExplanation",
    "analyze_intervals",
    "analyze_polynomial_degree",
    "evaluate_degree",
    "explain_var",
    "format_var_explanation",
    "materialize_intervals",
    "run",
]
