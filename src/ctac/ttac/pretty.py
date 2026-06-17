"""Pretty-printer for Tiny TAC.

Renders an AST back to surface syntax. Parenthesization is driven by
operator precedence so the output re-parses to the same AST (the
round-trip contract exercised by the tests).
"""

from __future__ import annotations

from . import ast
from .parser import _BINOP_BP

_ATOM = 100
_NOT_BP = 3


def _prec(e: ast.Expr) -> int:
    if isinstance(e, ast.BinExpr):
        return _BINOP_BP[e.op]
    if isinstance(e, ast.UnExpr):
        return _NOT_BP
    return _ATOM


def _wrap(e: ast.Expr, do_wrap: bool) -> str:
    s = expr_str(e)
    return f"({s})" if do_wrap else s


def expr_str(e: ast.Expr) -> str:
    if isinstance(e, ast.Num):
        return str(e.value)
    if isinstance(e, ast.BoolLit):
        return "true" if e.value else "false"
    if isinstance(e, ast.HavocExpr):
        return "havoc"
    if isinstance(e, ast.Var):
        return e.name
    if isinstance(e, ast.Load):
        return f"{_base_str(e.base)}[{expr_str(e.index)}]"
    if isinstance(e, ast.Update):
        return f"{_base_str(e.base)}[{expr_str(e.index)} := {expr_str(e.value)}]"
    if isinstance(e, ast.Field):
        return f"{_base_str(e.base)}.{e.name}"
    if isinstance(e, ast.Record):
        return (
            f"{{ addr: {expr_str(e.addr)}, value: {expr_str(e.value)}, "
            f"promise: {expr_str(e.promise)} }}"
        )
    if isinstance(e, ast.IfExpr):
        return f"if {expr_str(e.cond)} {{ {expr_str(e.then)} }} else {{ {expr_str(e.els)} }}"
    if isinstance(e, ast.UnExpr):
        return f"not {_wrap(e.operand, _prec(e.operand) < _NOT_BP)}"
    if isinstance(e, ast.BinExpr):
        bp = _BINOP_BP[e.op]
        left = _wrap(e.lhs, _prec(e.lhs) < bp)
        right = _wrap(e.rhs, _prec(e.rhs) <= bp)
        return f"{left} {e.op} {right}"
    raise TypeError(f"unknown expression node {type(e).__name__}")


def _base_str(e: ast.Expr) -> str:
    """Render a postfix base, parenthesizing compound (non-atom) operands."""
    return _wrap(e, _prec(e) < _ATOM)


def _target_str(t: ast.Target) -> str:
    return t.name if t.ty is None else f"{t.name}: {t.ty.value}"


def cmd_str(c: ast.Cmd) -> str:
    if isinstance(c, ast.Assign):
        return f"{_target_str(c.target)} := {expr_str(c.rhs)}"
    if isinstance(c, ast.Havoc):
        return f"{_target_str(c.target)} := havoc"
    if isinstance(c, ast.Phi):
        arms = ", ".join(f"{a.label}: {a.value}" for a in c.arms)
        return f"{_target_str(c.target)} := phi [{arms}]"
    if isinstance(c, ast.GetRef):
        return f"{_target_str(c.target)} := get_ref {c.ref}"
    if isinstance(c, ast.Borrow):
        return f"{_target_str(c.target)} := borrow {_base_str(c.base)}[{expr_str(c.index)}]"
    if isinstance(c, ast.BorrowMut):
        return (
            f"{_target_str(c.ref_target)}, {_target_str(c.map_target)} := "
            f"borrow_mut {_base_str(c.base)}[{expr_str(c.index)}]"
        )
    if isinstance(c, ast.BorrowRef):
        return f"{_target_str(c.target)} := borrow_ref {c.src}"
    if isinstance(c, ast.BorrowRefMut):
        return (
            f"{_target_str(c.ref_target)}, {_target_str(c.cont_target)} := "
            f"borrow_ref_mut {c.src}"
        )
    if isinstance(c, ast.PutRef):
        return f"{_target_str(c.target)} := put_ref {c.ref}, {expr_str(c.value)}"
    if isinstance(c, ast.Release):
        return f"release {c.ref}"
    if isinstance(c, ast.Assume):
        return f"assume {expr_str(c.cond)}"
    if isinstance(c, ast.Assert):
        return f"assert {c.cond_name}"
    raise TypeError(f"unknown command node {type(c).__name__}")


def terminator_str(t: ast.Terminator) -> str:
    if isinstance(t, ast.Halt):
        return "halt"
    if isinstance(t, ast.Goto):
        return f"goto {t.target}"
    if isinstance(t, ast.IfGoto):
        return f"if {t.cond} goto {t.then_target} else {t.else_target}"
    raise TypeError(f"unknown terminator node {type(t).__name__}")


def block_str(b: ast.Block) -> str:
    lines = [f"{b.label}:"]
    lines.extend(f"  {cmd_str(c)}" for c in b.commands)
    lines.append(f"  {terminator_str(b.terminator)}")
    return "\n".join(lines)


def pretty(p: ast.Program) -> str:
    """Render a program; blocks separated by a blank line, trailing newline."""
    return "\n\n".join(block_str(b) for b in p.blocks) + "\n"
