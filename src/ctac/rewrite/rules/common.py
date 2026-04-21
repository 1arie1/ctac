"""Shared helpers for TAC rewrite rules.

Kept tiny on purpose — op-group sets, constant parsing, and a
:func:`reformat_const` helper that emits new integers in the same lexical style
(hex/decimal, typed/untyped) as a template :class:`ConstExpr`.
"""

from __future__ import annotations

import re

from ctac.ast.nodes import ApplyExpr, ConstExpr, TacExpr
from ctac.ast.range_constraints import const_expr_to_int as _const_to_int

DIV_OPS = frozenset({"Div", "IntDiv"})
MUL_OPS = frozenset({"Mul", "IntMul"})
MOD_OPS = frozenset({"Mod", "IntMod"})
BWAND_OP = "BWAnd"

_TYPED_CONST = re.compile(
    r"^(?P<num>(?:-?\d+|0[xX][0-9a-fA-F_]+))\((?P<tag>[A-Za-z0-9_]+)\)$"
)
_UNTYPED_HEX = re.compile(r"^-?0[xX][0-9a-fA-F_]+$")


def const_to_int(expr: TacExpr) -> int | None:
    return _const_to_int(expr)


def log2_if_pow2(n: int) -> int | None:
    if n <= 0:
        return None
    if n & (n - 1) != 0:
        return None
    return n.bit_length() - 1


def _fmt_int(n: int, *, hex_style: bool) -> str:
    if hex_style:
        return f"0x{n:x}" if n >= 0 else f"-0x{-n:x}"
    return str(n)


def reformat_const(template: ConstExpr, new_value: int) -> ConstExpr:
    """Emit ``new_value`` with the same notation (hex/decimal, typed or not) as ``template``."""
    text = template.value.strip().replace("_", "")
    m = _TYPED_CONST.fullmatch(text)
    if m is not None:
        num = m.group("num")
        tag = m.group("tag")
        return ConstExpr(f"{_fmt_int(new_value, hex_style='x' in num.lower())}({tag})")
    if _UNTYPED_HEX.fullmatch(text):
        return ConstExpr(_fmt_int(new_value, hex_style=True))
    return ConstExpr(str(new_value))


def as_int_const(template: ConstExpr, new_value: int) -> ConstExpr:
    """Emit ``new_value`` as an ``(int)``-tagged :class:`ConstExpr`.

    Preserves hex/decimal style from ``template`` but always applies the
    ``(int)`` type tag — used when rewrites need Int-domain arithmetic
    regardless of the template's original sort.
    """
    text = template.value.strip().replace("_", "")
    m = _TYPED_CONST.fullmatch(text)
    if m is not None and m.group("tag") == "int":
        # Already int-tagged — just reformat to the new value while keeping style.
        return reformat_const(template, new_value)
    is_hex = ("x" in (m.group("num") if m is not None else text).lower())
    num_str = _fmt_int(new_value, hex_style=is_hex)
    return ConstExpr(f"{num_str}(int)")


def is_apply_of(expr: TacExpr, op: str, arity: int | None = None) -> bool:
    if not isinstance(expr, ApplyExpr) or expr.op != op:
        return False
    return arity is None or len(expr.args) == arity


def is_apply_in(expr: TacExpr, ops: frozenset[str], arity: int | None = None) -> bool:
    if not isinstance(expr, ApplyExpr) or expr.op not in ops:
        return False
    return arity is None or len(expr.args) == arity
