"""Convert a Tiny TAC program into Single-Assert form around one assert.

``to_single_assert(program, block, cmd_index)``:

1. demote every *other* ``assert c`` to ``assume c`` (predicate
   verbatim);
2. truncate the chosen block at the chosen assert (assert becomes the
   last command, terminator becomes ``halt``);
3. slice the CFG to the chosen block (``cfg_slice.restrict_to_block``).

The result is single-entry/single-exit with exactly one assertion, every
other obligation kept as an assumption, and the path conditions leading
to the assertion preserved.
"""

from __future__ import annotations

from ctac.ttac import ast

from .cfg_slice import restrict_to_block


def to_single_assert(program: ast.Program, block: str, cmd_index: int) -> ast.Program:
    demoted = _demote_other_asserts(program, block, cmd_index)
    truncated = _truncate_live_block(demoted, block, cmd_index)
    return restrict_to_block(truncated, block)


def _demote_other_asserts(
    program: ast.Program, live_block: str, live_index: int
) -> ast.Program:
    new_blocks: list[ast.Block] = []
    for b in program.blocks:
        cmds: list[ast.Cmd] = []
        for idx, cmd in enumerate(b.commands):
            is_live = b.label == live_block and idx == live_index
            if isinstance(cmd, ast.Assert) and not is_live:
                cmds.append(ast.Assume(ast.Var(cmd.cond_name)))
            else:
                cmds.append(cmd)
        new_blocks.append(ast.Block(b.label, tuple(cmds), b.terminator))
    return ast.Program(tuple(new_blocks), entry=program.entry, exit=program.exit)


def _truncate_live_block(
    program: ast.Program, live_block: str, live_index: int
) -> ast.Program:
    new_blocks: list[ast.Block] = []
    for b in program.blocks:
        if b.label == live_block:
            new_blocks.append(
                ast.Block(b.label, b.commands[: live_index + 1], ast.Halt())
            )
        else:
            new_blocks.append(b)
    return ast.Program(tuple(new_blocks), entry=program.entry, exit=program.exit)
