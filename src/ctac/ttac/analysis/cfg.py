"""CFG helpers for Tiny TAC, built on networkx.

``ttac`` blocks carry a terminator rather than a successor list, so we
derive edges from the terminator and hand the graph to networkx for the
standard algorithms (predecessors, topological order). We trust the
validated library over hand-rolled traversals.
"""

from __future__ import annotations

import networkx as nx

from ctac.ttac import ast


def successors(block: ast.Block) -> tuple[str, ...]:
    """Successor block labels implied by the block's terminator."""
    term = block.terminator
    if isinstance(term, ast.Goto):
        return (term.target,)
    if isinstance(term, ast.IfGoto):
        return (term.then_target, term.else_target)
    return ()  # Halt


def block_by_label(program: ast.Program) -> dict[str, ast.Block]:
    return {b.label: b for b in program.blocks}


def to_digraph(program: ast.Program) -> nx.DiGraph:
    """One node per block label; edges from terminators to existing blocks."""
    g = nx.DiGraph()
    labels = {b.label for b in program.blocks}
    g.add_nodes_from(b.label for b in program.blocks)
    for block in program.blocks:
        for succ in successors(block):
            if succ in labels:
                g.add_edge(block.label, succ)
    return g


def predecessors(program: ast.Program) -> dict[str, list[str]]:
    g = to_digraph(program)
    return {node: list(g.predecessors(node)) for node in g.nodes}


def topo_order(program: ast.Program) -> list[str]:
    """Topological block order; falls back to source order on cycles.

    VCGen targets are loop-free, but a goto may form a cycle; the
    reaching-defs fixpoint stays correct either way, and a stable order
    only speeds convergence.
    """
    g = to_digraph(program)
    if nx.is_directed_acyclic_graph(g):
        return list(nx.lexicographical_topological_sort(g))
    return [b.label for b in program.blocks]
