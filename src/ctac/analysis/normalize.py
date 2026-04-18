"""Program normalization passes for data-flow analyses."""

from __future__ import annotations

from dataclasses import replace

from ctac.analysis.symbols import canonical_symbol
from ctac.ast.nodes import (
    AnnotationCmd,
    ApplyExpr,
    AssertCmd,
    AssignExpCmd,
    AssignHavocCmd,
    AssumeExpCmd,
    JumpiCmd,
    SymbolRef,
    SymbolWeakRef,
    TacCmd,
    TacExpr,
)
from ctac.ir.models import TacBlock, TacProgram


def _normalize_expr(expr: TacExpr, *, strip_var_suffixes: bool) -> TacExpr:
    if isinstance(expr, SymbolRef):
        name = canonical_symbol(expr.name, strip_var_suffixes=strip_var_suffixes)
        if name == expr.name:
            return expr
        return replace(expr, name=name)
    if isinstance(expr, ApplyExpr):
        args = tuple(_normalize_expr(a, strip_var_suffixes=strip_var_suffixes) for a in expr.args)
        if args == expr.args:
            return expr
        return replace(expr, args=args)
    return expr


def _normalize_cmd(cmd: TacCmd, *, strip_var_suffixes: bool) -> TacCmd:
    if isinstance(cmd, AssignExpCmd):
        lhs = canonical_symbol(cmd.lhs, strip_var_suffixes=strip_var_suffixes)
        rhs = _normalize_expr(cmd.rhs, strip_var_suffixes=strip_var_suffixes)
        if lhs == cmd.lhs and rhs == cmd.rhs:
            return cmd
        return replace(cmd, lhs=lhs, rhs=rhs)
    if isinstance(cmd, AssumeExpCmd):
        cond = _normalize_expr(cmd.condition, strip_var_suffixes=strip_var_suffixes)
        if cond == cmd.condition:
            return cmd
        return replace(cmd, condition=cond)
    if isinstance(cmd, AssignHavocCmd):
        lhs = canonical_symbol(cmd.lhs, strip_var_suffixes=strip_var_suffixes)
        if lhs == cmd.lhs:
            return cmd
        return replace(cmd, lhs=lhs)
    if isinstance(cmd, JumpiCmd):
        cond = canonical_symbol(cmd.condition, strip_var_suffixes=strip_var_suffixes)
        if cond == cmd.condition:
            return cmd
        return replace(cmd, condition=cond)
    if isinstance(cmd, AssertCmd):
        pred = canonical_symbol(cmd.predicate, strip_var_suffixes=strip_var_suffixes)
        if pred == cmd.predicate:
            return cmd
        return replace(cmd, predicate=pred)
    if isinstance(cmd, AnnotationCmd):
        strong_refs = tuple(
            SymbolRef(canonical_symbol(ref.name, strip_var_suffixes=strip_var_suffixes))
            for ref in cmd.strong_refs
        )
        weak_refs = tuple(
            SymbolWeakRef(canonical_symbol(ref.name, strip_var_suffixes=strip_var_suffixes))
            for ref in cmd.weak_refs
        )
        if strong_refs == cmd.strong_refs and weak_refs == cmd.weak_refs:
            return cmd
        return replace(cmd, strong_refs=strong_refs, weak_refs=weak_refs)
    return cmd


def normalize_program_symbols(program: TacProgram, *, strip_var_suffixes: bool = True) -> TacProgram:
    """Return a program with command/expr symbols canonicalized for analysis."""
    if not strip_var_suffixes:
        return program
    changed = False
    new_blocks: list[TacBlock] = []
    for b in program.blocks:
        cmds = [_normalize_cmd(c, strip_var_suffixes=strip_var_suffixes) for c in b.commands]
        if any(a is not bcmd for a, bcmd in zip(cmds, b.commands, strict=False)):
            changed = True
            new_blocks.append(replace(b, commands=cmds))
        else:
            new_blocks.append(b)
    if not changed:
        return program
    return TacProgram(blocks=new_blocks)
