"""Shared helpers for AST-level range constraint recognition."""

from __future__ import annotations

import re
from dataclasses import dataclass

from ctac.ast.nodes import ApplyExpr, ConstExpr, SymbolRef, TacExpr

MAX_U256 = (1 << 256) - 1
_TYPED_CONST = re.compile(
    # ``num`` accepts decimal (``-?\d+``) or hex with optional sign in
    # either position: ``-0x...`` (sign in front) or ``0x-...`` (sign
    # after the ``0x`` prefix — TAC uses this for typed negative hex
    # like ``0x-48(int)``).
    r"^(?P<num>(?:-?[0-9]+|-?0[xX]-?[0-9a-fA-F_]+))\((?P<tag>[A-Za-z0-9_]+)\)$"
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


@dataclass(frozen=True)
class SymbolRelationConstraint:
    """``left op right`` where both operands are canonicalized symbol names.

    ``op`` is one of ``"<"``, ``"<="``, ``"=="``, ``">="``, ``">"``. Used
    to capture relational assume facts like ``assume R139 == R575`` that
    don't fit a single-symbol interval.
    """

    left: str
    op: str
    right: str


def const_expr_to_int(expr: TacExpr) -> int | None:
    """Parse TAC constant expression into Python int."""
    if not isinstance(expr, ConstExpr):
        return None
    tok = expr.value.strip().replace("_", "")
    m = _TYPED_CONST.fullmatch(tok)
    if m is not None:
        tok = m.group("num")
    # TAC's negative-hex form ``0x-48`` writes the sign after the ``0x``
    # prefix; ``int(..., 16)`` rejects that. Normalize ``0x-N`` /
    # ``-0x-N`` to a single leading sign before parsing.
    if tok.startswith(("0x-", "0X-")):
        tok = "-" + tok[:2] + tok[3:]
    elif tok.startswith(("-0x-", "-0X-")):
        tok = tok[:3] + tok[4:]
    try:
        if tok.startswith(("0x", "0X", "-0x", "-0X")):
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
    expr: TacExpr, *, strip_var_suffixes: bool, allow_eq: bool = False
) -> tuple[str, str, int] | None:
    ops = {"Lt", "Le", "Gt", "Ge"}
    if allow_eq:
        ops = ops | {"Eq"}
    if not (
        isinstance(expr, ApplyExpr)
        and expr.op in ops
        and len(expr.args) == 2
    ):
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
            "Eq": "Eq",
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
    - single comparisons: ``X <= c``, ``X < c``, ``X >= c``, ``X > c``
      (including flipped-operand forms);
    - conjunction (``LAnd``) of two supported constraints on the same
      symbol — intersection of their intervals;
    - disjunction (``LOr``) of two supported constraints on the same
      symbol — convex hull of their intervals (sound over-approximation:
      the symbol's value is in either arm, so it's in the hull). Disjuncts
      may also be ``Eq(X, c)`` (treated as ``[c, c]``).

    Top-level ``Eq(X, c)`` is *not* matched here — that's a singleton
    pin, semantically distinct from a range. Callers reasoning about
    range-shaped constraints (e.g. UCE's "interval intersects u256")
    should not collapse a singleton equality into the same bucket.
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

    if isinstance(expr, ApplyExpr) and expr.op == "LOr" and len(expr.args) == 2:
        left = _match_disjunct(
            expr.args[0], strip_var_suffixes=strip_var_suffixes
        )
        right = _match_disjunct(
            expr.args[1], strip_var_suffixes=strip_var_suffixes
        )
        if left is None or right is None or left.symbol != right.symbol:
            return None
        # Convex hull: a side that's open in either arm is open in the
        # hull (the disjunction admits values reaching that ±∞).
        low = (
            None
            if left.lower is None or right.lower is None
            else min(left.lower, right.lower)
        )
        high = (
            None
            if left.upper is None or right.upper is None
            else max(left.upper, right.upper)
        )
        if low is None and high is None:
            return None
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


def _match_disjunct(
    expr: TacExpr, *, strip_var_suffixes: bool
) -> SymbolIntervalConstraint | None:
    """Match a disjunct inside an ``LOr`` — same shapes as the top-level
    matcher, plus ``Eq(X, c)``. Used only when an ``Eq`` arm is one of
    several alternatives, not as a stand-alone interval constraint."""
    norm = _normalize_symbol_const_cmp(
        expr, strip_var_suffixes=strip_var_suffixes, allow_eq=True
    )
    if norm is not None:
        op, sym, c = norm
        if op == "Eq":
            return SymbolIntervalConstraint(symbol=sym, lower=c, upper=c)
    return match_symbol_interval_constraint(
        expr, strip_var_suffixes=strip_var_suffixes
    )


def interval_constraint_intersects_u256(constraint: SymbolIntervalConstraint) -> bool:
    lo = 0 if constraint.lower is None else max(0, constraint.lower)
    hi = MAX_U256 if constraint.upper is None else min(MAX_U256, constraint.upper)
    return lo <= hi


_REL_OPS = {"Lt": "<", "Le": "<=", "Gt": ">", "Ge": ">=", "Eq": "=="}


def match_symbol_relation_constraint(
    expr: TacExpr,
    *,
    strip_var_suffixes: bool = True,
) -> SymbolRelationConstraint | None:
    """Match a binary comparison between two symbols.

    Returns ``SymbolRelationConstraint(left=X, op='<=', right=Y)`` for
    forms like ``Le(X, Y)``, ``Lt(X, Y)``, ``Ge(X, Y)``, ``Gt(X, Y)``,
    ``Eq(X, Y)`` when both operands are ``SymbolRef`` nodes. Returns
    ``None`` otherwise — single-symbol-vs-constant forms are handled by
    :func:`match_symbol_interval_constraint`.
    """
    if not (isinstance(expr, ApplyExpr) and expr.op in _REL_OPS and len(expr.args) == 2):
        return None
    left, right = expr.args
    if not (isinstance(left, SymbolRef) and isinstance(right, SymbolRef)):
        return None
    l_name = _canonical_symbol_name(left.name, strip_var_suffixes=strip_var_suffixes)
    r_name = _canonical_symbol_name(right.name, strip_var_suffixes=strip_var_suffixes)
    return SymbolRelationConstraint(left=l_name, op=_REL_OPS[expr.op], right=r_name)
