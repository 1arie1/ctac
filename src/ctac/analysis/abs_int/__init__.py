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

__all__ = [
    "BOT",
    "Domain",
    "ExprDegree",
    "Frontier",
    "PolyDegResult",
    "PolynomialDegreeDomain",
    "TOP",
    "analyze_polynomial_degree",
    "evaluate_degree",
    "run",
]
