"""Pluggable pretty printers for TAC command AST."""

from __future__ import annotations

import re
from collections.abc import Iterable
from dataclasses import dataclass
from typing import Protocol

from ctac.tac_ast.nodes import (
    AnnotationCmd,
    ApplyExpr,
    AssertCmd,
    AssignExpCmd,
    AssignHavocCmd,
    AssumeExpCmd,
    ConstExpr,
    JumpCmd,
    JumpiCmd,
    LabelCmd,
    RawCmd,
    SymExpr,
    TacCmd,
    TacExpr,
)
from ctac.tac_ast.visitor import TacVisitor


class CommandPrinter(Protocol):
    name: str

    def print_expr(self, expr: TacExpr) -> str: ...

    def print_cmd(self, cmd: TacCmd) -> str | None: ...


class PrettyPrinter(TacVisitor):
    """Base class for one concrete pretty-print style."""

    name = 'base'

    def __init__(self, *, strip_var_suffixes: bool = True) -> None:
        self.strip_var_suffixes = strip_var_suffixes

    @staticmethod
    def _strip_var_suffix(tok: str) -> str:
        # TAC variables/symbols often carry meta suffixes like `:1`, `:25`, `:0`.
        # Keep this optional, because raw/debug views may prefer the original token.
        return re.sub(r":\d+$", "", tok)

    def _fmt_symbol_token(self, tok: str) -> str:
        if self.strip_var_suffixes:
            return self._strip_var_suffix(tok)
        return tok

    @staticmethod
    def _strip_outer_parens_once(s: str) -> str:
        """
        Remove one surrounding pair of parentheses if they wrap the whole string.

        Example: ``(a + b)`` -> ``a + b``; ``(a) + (b)`` stays unchanged.
        """
        s = s.strip()
        if len(s) < 2 or s[0] != "(" or s[-1] != ")":
            return s
        depth = 0
        for i, ch in enumerate(s):
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
                if depth == 0 and i != len(s) - 1:
                    return s
        return s[1:-1].strip()

    def print_expr(self, expr: TacExpr) -> str:
        return self.visit(expr)

    def print_cmd(self, cmd: TacCmd) -> str | None:
        return self.visit(cmd)

    # expressions
    def visit_SymExpr(self, node: SymExpr) -> str:
        return self._fmt_symbol_token(node.name)

    def visit_ConstExpr(self, node: ConstExpr) -> str:
        return node.value

    def visit_ApplyExpr(self, node: ApplyExpr) -> str:
        args = ', '.join(self.print_expr(a) for a in node.args)
        return f"{node.op}({args})"

    # commands defaults
    def visit_AssignExpCmd(self, node: AssignExpCmd) -> str:
        rhs = self._strip_outer_parens_once(self.print_expr(node.rhs))
        return f"{self._fmt_symbol_token(node.lhs)} = {rhs}"

    def visit_AssumeExpCmd(self, node: AssumeExpCmd) -> str:
        cond = self._strip_outer_parens_once(self.print_expr(node.condition))
        return f"assume {cond}"

    def visit_JumpCmd(self, node: JumpCmd) -> str:
        return f"goto {node.target}"

    def visit_JumpiCmd(self, node: JumpiCmd) -> str:
        cond = self._fmt_symbol_token(node.condition)
        return f"if {cond} goto {node.then_target} else {node.else_target}"

    def visit_AssertCmd(self, node: AssertCmd) -> str:
        pred = self._fmt_symbol_token(node.predicate)
        if node.message:
            return f"assert {pred}  # {node.message}"
        return f"assert {pred}"

    def visit_LabelCmd(self, node: LabelCmd) -> str | None:
        return None

    def visit_AnnotationCmd(self, node: AnnotationCmd) -> str | None:
        return None

    def visit_RawCmd(self, node: RawCmd) -> str:
        return node.raw


class HumanPrettyPrinter(PrettyPrinter):
    """Default human printer; skips labels/annotations by design."""

    name = 'human'

    _binary_infix = {
        "Eq": "==",
        "Lt": "<",
        "Le": "<=",
        "Gt": ">",
        "Ge": ">=",
        "Slt": "<s",
        "Sle": "<=s",
        "Sgt": ">s",
        "Sge": ">=s",
        "LAnd": "&&",
        "LOr": "||",
        "BWAnd": "&",
        "BWOr": "|",
        "BWXOr": "^",
        "Add": "+",
        "IntAdd": "+int",
        "Sub": "-",
        "IntSub": "-int",
        "Mul": "*",
        "IntMul": "*int",
        "Div": "/",
        "IntDiv": "/int",
        "Mod": "%",
        "IntMod": "%int",
        "ShiftLeft": "<<",
        "ShiftRightLogical": ">>",
        "ShiftRightArithmetical": ">>s",
    }

    _unary_prefix = {
        "LNot": "!",
        "BWNot": "~",
    }

    def _short_fn_name(self, fn: str) -> str:
        # Common builtin in TAC dumps: convert Int -> bv256.
        # Keep it compact in human output.
        if fn.startswith("safe_math_narrow_bv256"):
            return "narrow"
        return fn

    def visit_ApplyExpr(self, node: ApplyExpr) -> str:
        op = node.op
        args = [self.print_expr(a) for a in node.args]

        if op in self._unary_prefix and len(args) == 1:
            return f"{self._unary_prefix[op]}({args[0]})"

        if op == "Ite" and len(args) == 3:
            # Rust-like conditional expression form.
            cond = self._strip_outer_parens_once(args[0])
            return f"(if {cond} {{ {args[1]} }} else {{ {args[2]} }})"

        if op in self._binary_infix and len(args) >= 2:
            inf = self._binary_infix[op]
            return "(" + f" {inf} ".join(args) + ")"

        if op == "Apply" and args:
            fn = self._short_fn_name(args[0])
            rest = ", ".join(args[1:])
            return f"{fn}({rest})"

        return super().visit_ApplyExpr(node)

    def visit_AssignHavocCmd(self, node: AssignHavocCmd) -> str:
        return f"{self._fmt_symbol_token(node.lhs)} = havoc"

    def visit_JumpCmd(self, node: JumpCmd) -> str | None:
        # Block terminator is rendered from CFG successors in `pp`.
        return None

    def visit_JumpiCmd(self, node: JumpiCmd) -> str | None:
        # Block terminator is rendered from CFG successors in `pp`.
        return None


class RawPrettyPrinter(PrettyPrinter):
    """Printer that preserves command lines exactly as in dump."""

    name = 'raw'

    def print_expr(self, expr: TacExpr) -> str:
        return super().print_expr(expr)

    def print_cmd(self, cmd: TacCmd) -> str | None:
        return cmd.raw


@dataclass
class PrinterRegistry:
    _printers: dict[str, CommandPrinter]

    @classmethod
    def with_defaults(cls) -> 'PrinterRegistry':
        reg = cls({})
        reg.register(HumanPrettyPrinter())
        reg.register(RawPrettyPrinter())
        return reg

    def register(self, p: CommandPrinter) -> None:
        self._printers[p.name] = p

    def names(self) -> list[str]:
        return sorted(self._printers)

    def get(self, name: str) -> CommandPrinter:
        if name not in self._printers:
            raise KeyError(f"unknown pretty-printer {name!r}; choose one of: {', '.join(self.names())}")
        return self._printers[name]


DEFAULT_PRINTERS = PrinterRegistry.with_defaults()


def configured_printer(name: str, *, strip_var_suffixes: bool = True) -> CommandPrinter:
    """Instantiate a configurable printer by name from defaults registry."""
    if name == "human":
        return HumanPrettyPrinter(strip_var_suffixes=strip_var_suffixes)
    if name == "raw":
        # Raw printer intentionally preserves `cmd.raw` exactly.
        return RawPrettyPrinter(strip_var_suffixes=strip_var_suffixes)
    return DEFAULT_PRINTERS.get(name)


def pretty_lines(cmds: Iterable[TacCmd], *, printer: CommandPrinter) -> list[str]:
    out: list[str] = []
    for c in cmds:
        line = printer.print_cmd(c)
        if line is not None and line != '':
            out.append(line)
    return out
