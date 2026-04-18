"""Expression/command use extraction for TAC analyses."""

from __future__ import annotations

from collections.abc import Iterator

from ctac.analysis.symbols import canonical_symbol
from ctac.ast.nodes import (
    ApplyExpr,
    AssertCmd,
    AssignExpCmd,
    AssumeExpCmd,
    JumpiCmd,
    SymExpr,
    TacCmd,
    TacExpr,
)


def iter_expr_symbols(expr: TacExpr, *, strip_var_suffixes: bool = True) -> Iterator[str]:
    if isinstance(expr, SymExpr):
        yield canonical_symbol(expr.name, strip_var_suffixes=strip_var_suffixes)
        return
    if isinstance(expr, ApplyExpr):
        for arg in expr.args:
            yield from iter_expr_symbols(arg, strip_var_suffixes=strip_var_suffixes)


def command_uses(cmd: TacCmd, *, strip_var_suffixes: bool = True) -> tuple[str, ...]:
    seen: set[str] = set()
    ordered: list[str] = []

    def _add(sym: str) -> None:
        if sym not in seen:
            seen.add(sym)
            ordered.append(sym)

    if isinstance(cmd, AssignExpCmd):
        for s in iter_expr_symbols(cmd.rhs, strip_var_suffixes=strip_var_suffixes):
            _add(s)
    elif isinstance(cmd, AssumeExpCmd):
        for s in iter_expr_symbols(cmd.condition, strip_var_suffixes=strip_var_suffixes):
            _add(s)
    elif isinstance(cmd, AssertCmd):
        _add(canonical_symbol(cmd.predicate, strip_var_suffixes=strip_var_suffixes))
    elif isinstance(cmd, JumpiCmd):
        _add(canonical_symbol(cmd.condition, strip_var_suffixes=strip_var_suffixes))
    return tuple(ordered)
