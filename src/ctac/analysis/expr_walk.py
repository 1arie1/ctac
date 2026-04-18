"""Expression/command use extraction for TAC analyses."""

from __future__ import annotations

from collections.abc import Iterator

from ctac.builtins import is_known_builtin_function_symbol
from ctac.analysis.symbols import canonical_symbol
from ctac.ast.nodes import (
    ApplyExpr,
    AnnotationCmd,
    AssertCmd,
    AssignExpCmd,
    AssumeExpCmd,
    JumpiCmd,
    SymbolRef,
    TacCmd,
    TacExpr,
)


def iter_expr_symbols(expr: TacExpr, *, strip_var_suffixes: bool = True) -> Iterator[str]:
    if isinstance(expr, SymbolRef):
        yield canonical_symbol(expr.name, strip_var_suffixes=strip_var_suffixes)
        return
    if isinstance(expr, ApplyExpr):
        # TAC `Apply(fn, ...)` encodes function application where the first arg is function symbol.
        # Known builtins are not dataflow variables and should be excluded from use-def.
        if expr.op == "Apply" and expr.args and isinstance(expr.args[0], SymbolRef):
            fn_sym = canonical_symbol(expr.args[0].name, strip_var_suffixes=strip_var_suffixes)
            start = 1 if is_known_builtin_function_symbol(fn_sym) else 0
            for arg in expr.args[start:]:
                yield from iter_expr_symbols(arg, strip_var_suffixes=strip_var_suffixes)
            return
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
    elif isinstance(cmd, AnnotationCmd):
        for ref in cmd.strong_refs:
            _add(canonical_symbol(ref.name, strip_var_suffixes=strip_var_suffixes))
    elif isinstance(cmd, AssumeExpCmd):
        for s in iter_expr_symbols(cmd.condition, strip_var_suffixes=strip_var_suffixes):
            _add(s)
    elif isinstance(cmd, AssertCmd):
        _add(canonical_symbol(cmd.predicate, strip_var_suffixes=strip_var_suffixes))
    elif isinstance(cmd, JumpiCmd):
        _add(canonical_symbol(cmd.condition, strip_var_suffixes=strip_var_suffixes))
    return tuple(ordered)


def command_weak_uses(cmd: TacCmd, *, strip_var_suffixes: bool = True) -> tuple[str, ...]:
    if not isinstance(cmd, AnnotationCmd):
        return ()
    seen: set[str] = set()
    ordered: list[str] = []
    for ref in cmd.weak_refs:
        sym = canonical_symbol(ref.name, strip_var_suffixes=strip_var_suffixes)
        if sym not in seen:
            seen.add(sym)
            ordered.append(sym)
    return tuple(ordered)
