"""
TAC command / expression AST, parsers, visitor, and pretty-printer.

``ctac.ast`` holds program-level structures (``TacProgram``, ``TacBlock``);
``ctac.tac_ast`` holds per-command IR (``TacCmd``, ``TacExpr``) like a small compiler front-end.
"""

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
    TacNode,
)
from ctac.tac_ast.parse_cmd import parse_command_line
from ctac.tac_ast.parse_expr import parse_expr, parse_expr_safe
from ctac.tac_ast.visitor import TacVisitor

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
    # Keep ctac.tac_ast public API stable without eagerly importing pretty.py.
    # Eager import creates a cycle through eval/value_format during interpreter imports.
    if name in _PRETTY_EXPORTS:
        from ctac.tac_ast import pretty as _pretty

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
