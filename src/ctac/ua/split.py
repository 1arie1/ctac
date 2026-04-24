"""Split strategy: emit one program per assertion.

For each of the k assertions in the input program, produce a
``TacProgram`` in which that assertion is preserved verbatim and all
k-1 other ``AssertCmd`` sites have been converted to
``AssumeExpCmd`` with the same predicate. Each output is then pruned
to the cone of influence of its live assert (only the live-assert
block and its CFG ancestors are kept).

This is the ``split`` counterpart to the existing ``merge`` strategy:
where merge folds all asserts into one ``__UA_ERROR`` block for a
single monolithic VC, split produces k independent single-assert
programs suitable for per-assert solving / timing / UNSAT-core
isolation.
"""

from __future__ import annotations

from ctac.ast.nodes import AssertCmd, AssumeExpCmd, TacCmd
from ctac.graph import Cfg, CfgFilter
from ctac.ir.models import TacBlock, TacProgram
from ctac.rewrite.unparse import canonicalize_cmd
from ctac.ua.model import SplitAssertOutput, SplitAssertsResult


def split_asserts(program: TacProgram) -> SplitAssertsResult:
    """Emit one :class:`TacProgram` per assertion in ``program``.

    Assertions are traversed in program order (block order, then
    command index). For each live index, the other assertion sites
    become :class:`AssumeExpCmd` with the original predicate; the
    program is then pruned to the live assert's cone of influence.
    """
    sites = _assert_sites(program)
    if not sites:
        return SplitAssertsResult(
            outputs=(),
            asserts_before=0,
            was_noop=True,
        )

    outputs: list[SplitAssertOutput] = []
    for idx, (block_id, cmd_index, assert_cmd) in enumerate(sites):
        converted_program = _convert_others(program, live=(block_id, cmd_index))
        # Truncate the live block at the assert: commands after are
        # irrelevant to whether the assert fails, and ``ctac smt``
        # requires the AssertCmd be the last command in its block.
        truncated_program = _truncate_live_block(
            converted_program, live=(block_id, cmd_index)
        )
        pruned_program = _prune_to_assert(truncated_program, block_id)
        outputs.append(
            SplitAssertOutput(
                index=idx,
                block_id=block_id,
                cmd_index=cmd_index,
                message=assert_cmd.message,
                program=pruned_program,
            )
        )
    return SplitAssertsResult(
        outputs=tuple(outputs),
        asserts_before=len(sites),
        was_noop=False,
    )


def _assert_sites(program: TacProgram) -> list[tuple[str, int, AssertCmd]]:
    """Return every ``AssertCmd`` location in program-order traversal."""
    return [
        (b.id, i, c)
        for b in program.blocks
        for i, c in enumerate(b.commands)
        if isinstance(c, AssertCmd)
    ]


def _convert_others(
    program: TacProgram, *, live: tuple[str, int]
) -> TacProgram:
    """Build a new program where every ``AssertCmd`` except the one at
    ``live`` position has been replaced by an ``AssumeExpCmd``."""
    live_block, live_cmd = live
    new_blocks: list[TacBlock] = []
    for block in program.blocks:
        new_cmds: list[TacCmd] = []
        for idx, cmd in enumerate(block.commands):
            if (
                isinstance(cmd, AssertCmd)
                and not (block.id == live_block and idx == live_cmd)
            ):
                new_cmds.append(
                    canonicalize_cmd(AssumeExpCmd(raw="", condition=cmd.predicate))
                )
            else:
                new_cmds.append(cmd)
        new_blocks.append(
            TacBlock(
                id=block.id,
                successors=list(block.successors),
                commands=new_cmds,
            )
        )
    return TacProgram(blocks=new_blocks)


def _truncate_live_block(
    program: TacProgram, *, live: tuple[str, int]
) -> TacProgram:
    """Drop commands after the live assert in its block and clear
    successors. Satisfies ``ctac smt``'s "AssertCmd is last in block"
    precondition, and is sound for VC purposes — anything after the
    assert in execution order doesn't affect whether the assert fails.
    """
    live_block, live_cmd = live
    new_blocks: list[TacBlock] = []
    for block in program.blocks:
        if block.id != live_block:
            new_blocks.append(block)
            continue
        new_blocks.append(
            TacBlock(
                id=block.id,
                successors=[],  # terminal in this output
                commands=list(block.commands[: live_cmd + 1]),
            )
        )
    return TacProgram(blocks=new_blocks)


def _prune_to_assert(program: TacProgram, assert_block_id: str) -> TacProgram:
    """Keep only the assert's block and its CFG ancestors. Reuses
    :class:`ctac.graph.Cfg`'s ``--to`` filter, which computes
    ``{assert_block} | nx.ancestors(g, assert_block)`` and rewrites
    successor lists to drop references to pruned blocks."""
    sliced, _warnings = Cfg(program).filtered(CfgFilter(to_id=assert_block_id))
    return sliced.program
