"""Uniquify assertions for Tiny TAC (the ``ttac ua`` strategies).

A program may have several ``assert`` commands; the VC encoder wants
exactly one. Two strategies:

- **merge** - fold every ``assert c`` into a single ``__UA_ERROR`` sink
  by branching ``if c goto <continue> else <land>`` (predicate verbatim,
  Floyd-Hoare: the continuation assumes ``c``); the sink asserts false.
- **split** - emit one Single-Assert-form program per assertion
  (delegates to :func:`single_assert.to_single_assert`).

ttac needs no purify/true-drop pre-passes: ``assert c`` already names a
bool register by grammar.
"""

from __future__ import annotations

import itertools
from dataclasses import dataclass

from ctac.ttac import ast
from ctac.ttac.analysis import analyze_types

from .single_assert import to_single_assert

ERROR_BLOCK = "__UA_ERROR"
FAIL_VAR = "__ua_fail"


@dataclass(frozen=True)
class MergeResult:
    program: ast.Program
    asserts_merged: int
    error_block: str
    was_noop: bool


@dataclass(frozen=True)
class SplitOutput:
    index: int
    block: str
    cond_name: str
    program: ast.Program


@dataclass(frozen=True)
class SplitResult:
    outputs: tuple[SplitOutput, ...]
    asserts_before: int
    was_noop: bool


def _assert_sites(program: ast.Program) -> list[tuple[str, int, str]]:
    """Every ``assert`` location in program order: (block, cmd_index, cond)."""
    return [
        (b.label, i, c.cond_name)
        for b in program.blocks
        for i, c in enumerate(b.commands)
        if isinstance(c, ast.Assert)
    ]


def split_asserts(program: ast.Program) -> SplitResult:
    sites = _assert_sites(program)
    if not sites:
        return SplitResult(outputs=(), asserts_before=0, was_noop=True)
    # Stamp each havoc with its type inferred from the whole program, so the
    # annotation survives COI pruning and every per-assert output stays
    # type-total even when an arm no longer reads the variable.
    program = annotate_havoc_types(program)
    outputs = tuple(
        SplitOutput(
            index=idx,
            block=bl,
            cond_name=cond,
            program=to_single_assert(program, bl, ci),
        )
        for idx, (bl, ci, cond) in enumerate(sites)
    )
    return SplitResult(outputs=outputs, asserts_before=len(sites), was_noop=False)


def annotate_havoc_types(program: ast.Program) -> ast.Program:
    """Annotate each unannotated ``havoc`` target with its inferred type.

    Runs type inference over the whole program (where every variable is
    determined) and writes the inferred type onto the havoc's target. Only
    havocs carry no inherent type; every other definition is self-typing.
    Variables whose type is unknown/conflicting are left untouched.
    """
    types = analyze_types(program).types
    new_blocks: list[ast.Block] = []
    for block in program.blocks:
        cmds: list[ast.Cmd] = []
        for cmd in block.commands:
            if isinstance(cmd, ast.Havoc) and cmd.target.ty is None:
                ty = types.get(cmd.target.name)
                if isinstance(ty, ast.Ty):
                    cmd = ast.Havoc(ast.Target(cmd.target.name, ty))
            cmds.append(cmd)
        new_blocks.append(ast.Block(block.label, tuple(cmds), block.terminator))
    return ast.Program(tuple(new_blocks), entry=program.entry, exit=program.exit)


def merge_asserts(program: ast.Program) -> MergeResult:
    sites = _assert_sites(program)
    if len(sites) <= 1:
        return MergeResult(
            program=program, asserts_merged=0, error_block="", was_noop=True
        )
    if any(b.label == ERROR_BLOCK for b in program.blocks):
        raise ValueError(f"block {ERROR_BLOCK!r} already exists; merge would collide")

    fresh = itertools.count(0)
    new_blocks: list[ast.Block] = []
    merged = 0
    for block in program.blocks:
        pieces, count = _split_block(block, fresh)
        new_blocks.extend(pieces)
        merged += count
    new_blocks.append(_error_block())

    return MergeResult(
        program=ast.Program(tuple(new_blocks), entry=program.entry, exit=program.exit),
        asserts_merged=merged,
        error_block=ERROR_BLOCK,
        was_noop=False,
    )


def _split_block(
    block: ast.Block, fresh: "itertools.count[int]"
) -> tuple[list[ast.Block], int]:
    pieces: list[ast.Block] = []
    cur_label = block.label
    cur_cmds: list[ast.Cmd] = []
    merged = 0

    for cmd in block.commands:
        if not isinstance(cmd, ast.Assert):
            cur_cmds.append(cmd)
            continue
        merged += 1
        n = next(fresh)
        cont = f"{block.label}_UA{n}"
        land = f"{block.label}_UA{n}_land"
        # Branch on the predicate verbatim: true continues, false lands at error.
        pieces.append(
            ast.Block(cur_label, tuple(cur_cmds), ast.IfGoto(cmd.cond_name, cont, land))
        )
        pieces.append(ast.Block(land, (), ast.Goto(ERROR_BLOCK)))
        cur_label = cont
        cur_cmds = [ast.Assume(ast.Var(cmd.cond_name))]  # Floyd-Hoare

    # Final piece keeps the block's original terminator.
    pieces.append(ast.Block(cur_label, tuple(cur_cmds), block.terminator))
    return pieces, merged


def _error_block() -> ast.Block:
    return ast.Block(
        label=ERROR_BLOCK,
        commands=(
            ast.Assign(ast.Target(FAIL_VAR), ast.BoolLit(False)),
            ast.Assert(FAIL_VAR),
        ),
        terminator=ast.Halt(),
    )
