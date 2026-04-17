"""Visitor base for TAC AST nodes."""

from __future__ import annotations

from ctac.tac_ast.nodes import TacNode


class TacVisitor:
    """Simple dynamic-dispatch visitor (`visit_<ClassName>`)."""

    def visit(self, node: TacNode):
        name = f"visit_{type(node).__name__}"
        fn = getattr(self, name, self.generic_visit)
        return fn(node)

    def generic_visit(self, node: TacNode):
        raise NotImplementedError(f"no visitor for {type(node).__name__}")
