"""Public command/expression AST package for TAC IR."""

from ctac.ast.nodes import (
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
    TacNode,
)
from ctac.ast.parse_cmd import parse_command_line
from ctac.ast.parse_expr import parse_expr, parse_expr_safe
from ctac.ast.visitor import TacVisitor

_PRETTY_EXPORTS = {
    "DEFAULT_PRINTERS",
    "CommandPrinter",
    "HumanPrettyPrinter",
    "PrettyPrinter",
    "PrinterRegistry",
    "RawPrettyPrinter",
    "configured_printer",
    "pretty_lines",
}


def __getattr__(name: str):
    # Keep ctac.ast public API stable without eagerly importing pretty.py.
    # Eager import creates a cycle through eval/value_format during interpreter imports.
    if name in _PRETTY_EXPORTS:
        from ctac.ast import pretty as _pretty

        return getattr(_pretty, name)
    raise AttributeError(name)


__all__ = [
    "AnnotationCmd",
    "ApplyExpr",
    "AssertCmd",
    "AssignExpCmd",
    "AssignHavocCmd",
    "AssumeExpCmd",
    "ConstExpr",
    "JumpCmd",
    "JumpiCmd",
    "LabelCmd",
    "HumanPrettyPrinter",
    "RawPrettyPrinter",
    "CommandPrinter",
    "PrinterRegistry",
    "DEFAULT_PRINTERS",
    "configured_printer",
    "PrettyPrinter",
    "RawCmd",
    "SymExpr",
    "TacCmd",
    "TacExpr",
    "TacNode",
    "TacVisitor",
    "parse_command_line",
    "parse_expr",
    "parse_expr_safe",
    "pretty_lines",
]
