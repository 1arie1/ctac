"""Builtin function registry shared by analysis/eval/pretty layers."""

from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class BuiltinFunction:
    key_prefix: str
    pretty_name: str


# Keep this list small and explicit; expand as new builtins are supported.
BUILTIN_FUNCTIONS: tuple[BuiltinFunction, ...] = (
    BuiltinFunction(key_prefix="safe_math_narrow_bv256", pretty_name="narrow"),
)


def _strip_bif_suffix(symbol: str) -> str:
    s = symbol.strip()
    if s.endswith(":bif"):
        return s[:-4]
    return s


def resolve_builtin_function(symbol: str) -> BuiltinFunction | None:
    """Return builtin metadata if symbol identifies a known builtin function."""
    core = _strip_bif_suffix(symbol)
    for fn in BUILTIN_FUNCTIONS:
        if core.startswith(fn.key_prefix):
            return fn
    return None


def pretty_builtin_name(symbol: str) -> str:
    """Map builtin token to short pretty name, or return the original symbol."""
    fn = resolve_builtin_function(symbol)
    if fn is None:
        return symbol
    return fn.pretty_name


def is_known_builtin_function_symbol(symbol: str) -> bool:
    return resolve_builtin_function(symbol) is not None
