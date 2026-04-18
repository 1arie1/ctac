"""Shared helpers for AST-level range constraint recognition."""

from __future__ import annotations

import re
from dataclasses import dataclass

from ctac.tac_ast.nodes import ApplyExpr, ConstExpr, SymbolRef, TacExpr

MAX_U256 = (1 << 256) - 1
_TYPED_CONST = re.compile(
    r"^(?P<num>(?:-?[0-9]+|0[xX][0-9a-fA-F_]+))\((?P<tag>[A-Za-z0-9_]+)\)$"
)
_VAR_SUFFIX = re.compile(r":\d+$")


@dataclass(frozen=True)
class InclusiveRangeConstraint:
    symbol: str
    lower: TacExpr
    upper: TacExpr


@dataclass(frozen=True)
class SymbolIntervalConstraint:
    symbol: str
    lower: int | None  # inclusive, None means -infinity
    upper: int | None  # inclusive, None means +infinity


def const_expr_to_int(expr: TacExpr) -> int | None:
    """Parse TAC constant expression into Python int."""
    if not isinstance(expr, ConstExpr):
        return None
    tok = expr.value.strip().replace("_", "")
    m = _TYPED_CONST.fullmatch(tok)
    if m is not None:
        tok = m.group("num")
    try:
        if tok.startswith(("0x", "0X")):
            return int(tok, 16)
        return int(tok, 10)
    except ValueError:
        return None


def interval_intersects_u256(lower: int, upper: int) -> bool:
    """Return whether [lower, upper] intersects [0, MAX_U256]."""
    if lower > upper:
        return False
    lo = max(lower, 0)
    hi = min(upper, MAX_U256)
    return lo <= hi


def _canonical_symbol_name(name: str, *, strip_var_suffixes: bool) -> str:
    if not strip_var_suffixes:
        return name
    return _VAR_SUFFIX.sub("", name)


def _normalize_inclusive_cmp(
    expr: TacExpr, *, strip_var_suffixes: bool
) -> tuple[str, str, TacExpr] | None:
    """Normalize one comparison side into lower/upper bound relation."""
    if not (isinstance(expr, ApplyExpr) and expr.op in {"Ge", "Le"} and len(expr.args) == 2):
        return None
    left, right = expr.args
    if isinstance(left, SymbolRef):
        sym = _canonical_symbol_name(left.name, strip_var_suffixes=strip_var_suffixes)
        # x >= c -> lower bound; x <= c -> upper bound
        kind = "lower" if expr.op == "Ge" else "upper"
        return kind, sym, right
    if isinstance(right, SymbolRef):
        sym = _canonical_symbol_name(right.name, strip_var_suffixes=strip_var_suffixes)
        # c >= x -> upper bound; c <= x -> lower bound
        kind = "upper" if expr.op == "Ge" else "lower"
        return kind, sym, left
    return None


def _normalize_symbol_const_cmp(
    expr: TacExpr, *, strip_var_suffixes: bool
) -> tuple[str, str, int] | None:
    if not (isinstance(expr, ApplyExpr) and expr.op in {"Lt", "Le", "Gt", "Ge"} and len(expr.args) == 2):
        return None
    left, right = expr.args
    left_const = const_expr_to_int(left)
    right_const = const_expr_to_int(right)

    if isinstance(left, SymbolRef) and right_const is not None:
        sym = _canonical_symbol_name(left.name, strip_var_suffixes=strip_var_suffixes)
        return expr.op, sym, right_const
    if isinstance(right, SymbolRef) and left_const is not None:
        sym = _canonical_symbol_name(right.name, strip_var_suffixes=strip_var_suffixes)
        flipped = {
            "Lt": "Gt",
            "Le": "Ge",
            "Gt": "Lt",
            "Ge": "Le",
        }[expr.op]
        return flipped, sym, left_const
    return None


def match_inclusive_range_constraint(
    expr: TacExpr, *, strip_var_suffixes: bool = True
) -> InclusiveRangeConstraint | None:
    """Match conjunction form equivalent to `lo <= X <= hi`."""
    if not (isinstance(expr, ApplyExpr) and expr.op == "LAnd" and len(expr.args) == 2):
        return None
    left = _normalize_inclusive_cmp(expr.args[0], strip_var_suffixes=strip_var_suffixes)
    right = _normalize_inclusive_cmp(expr.args[1], strip_var_suffixes=strip_var_suffixes)
    if left is None or right is None:
        return None
    lkind, lsym, lbound = left
    rkind, rsym, rbound = right
    if lsym != rsym:
        return None
    if {lkind, rkind} != {"lower", "upper"}:
        return None
    lower = lbound if lkind == "lower" else rbound
    upper = lbound if lkind == "upper" else rbound
    return InclusiveRangeConstraint(symbol=lsym, lower=lower, upper=upper)


def match_symbol_interval_constraint(
    expr: TacExpr,
    *,
    strip_var_suffixes: bool = True,
) -> SymbolIntervalConstraint | None:
    """
    Match comparison/range forms into an inclusive integer interval.

    Supports:
    - single comparisons: X <= c, X < c, X >= c, X > c (including flipped-operand forms)
    - conjunction of two supported constraints over the same symbol.
    """
    if isinstance(expr, ApplyExpr) and expr.op == "LAnd" and len(expr.args) == 2:
        left = match_symbol_interval_constraint(
            expr.args[0],
            strip_var_suffixes=strip_var_suffixes,
        )
        right = match_symbol_interval_constraint(
            expr.args[1],
            strip_var_suffixes=strip_var_suffixes,
        )
        if left is None or right is None or left.symbol != right.symbol:
            return None
        low = left.lower
        if right.lower is not None:
            low = right.lower if low is None else max(low, right.lower)
        high = left.upper
        if right.upper is not None:
            high = right.upper if high is None else min(high, right.upper)
        return SymbolIntervalConstraint(symbol=left.symbol, lower=low, upper=high)

    norm = _normalize_symbol_const_cmp(expr, strip_var_suffixes=strip_var_suffixes)
    if norm is None:
        return None
    op, sym, c = norm
    if op == "Le":
        return SymbolIntervalConstraint(symbol=sym, lower=None, upper=c)
    if op == "Lt":
        return SymbolIntervalConstraint(symbol=sym, lower=None, upper=c - 1)
    if op == "Ge":
        return SymbolIntervalConstraint(symbol=sym, lower=c, upper=None)
    if op == "Gt":
        return SymbolIntervalConstraint(symbol=sym, lower=c + 1, upper=None)
    return None


def interval_constraint_intersects_u256(constraint: SymbolIntervalConstraint) -> bool:
    lo = 0 if constraint.lower is None else max(0, constraint.lower)
    hi = MAX_U256 if constraint.upper is None else min(MAX_U256, constraint.upper)
    return lo <= hi
