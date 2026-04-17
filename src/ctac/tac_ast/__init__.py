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
from ctac.tac_ast.pretty import (
    DEFAULT_PRINTERS,
    CommandPrinter,
    HumanPrettyPrinter,
    PrettyPrinter,
    PrinterRegistry,
    RawPrettyPrinter,
    configured_printer,
    pretty_lines,
)
from ctac.tac_ast.visitor import TacVisitor

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
