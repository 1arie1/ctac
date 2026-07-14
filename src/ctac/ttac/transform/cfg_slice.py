"""Prune a Tiny TAC program to a target block's cone of influence.

``restrict_to_block`` keeps the target block and every block that can
reach it, dropping the rest, while preserving single-entry/single-exit
(SESE). When a kept branch block loses one arm to pruning, the
conditional is rewritten into ``assume guard; goto kept-arm`` (polarity
matching the surviving arm) rather than redirected to a sink block - the
path condition is preserved and the only exit stays the target block.

This is the structured-terminator analogue of ``ctac.graph.Cfg.filtered``
with a ``--to`` filter; reachability uses networkx (validated library).
"""

from __future__ import annotations

import networkx as nx

from ctac.ttac import ast
from ctac.ttac.analysis import cfg


def restrict_to_block(program: ast.Program, target: str) -> ast.Program:
    """Keep ``target`` and its CFG ancestors; SESE-preserving."""
    g = cfg.to_digraph(program)
    keep = {target} | nx.ancestors(g, target)

    new_blocks: list[ast.Block] = []
    for block in program.blocks:
        if block.label not in keep:
            continue
        new_blocks.append(_rewrite_block(block, keep))

    exit_ = program.exit if program.exit in keep else None
    return ast.Program(tuple(new_blocks), entry=program.entry, exit=exit_)


def _rewrite_block(block: ast.Block, keep: set[str]) -> ast.Block:
    term = block.terminator
    if isinstance(term, ast.Halt):
        return block

    if isinstance(term, ast.Goto):
        # Ancestors' gotos stay inside keep; the target block's goto leads
        # to a pruned descendant, so the target becomes a sink.
        if term.target in keep:
            return block
        return ast.Block(block.label, block.commands, ast.Halt())

    # IfGoto
    then_in = term.then_target in keep
    else_in = term.else_target in keep
    if then_in and else_in:
        return block
    if not then_in and not else_in:
        # Both arms pruned (target block branching to descendants) -> sink.
        return ast.Block(block.label, block.commands, ast.Halt())

    cond = ast.Var(term.cond)
    if then_in:
        guard: ast.Expr = cond
        goto = ast.Goto(term.then_target)
    else:
        guard = ast.UnExpr("not", cond)
        goto = ast.Goto(term.else_target)

    commands = block.commands + (ast.Assume(guard),)
    return ast.Block(label=block.label, commands=commands, terminator=goto)
