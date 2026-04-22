"""Merge strategy: redirect every AssertCmd to a shared ``__UA_ERROR`` block.

Each ``AssertCmd P`` in a block ``B`` splits ``B`` into two pieces:

    B:        ... (commands before the assert)
              if (P) goto B_UA<N> else goto __UA_ERROR
    B_UA<N>:  assume P            # Floyd-Hoare: predicate holds below
              ... (commands after the assert)

The condition variable in ``JumpiCmd`` is taken verbatim from the
predicate's :class:`SymbolRef` name — the predicate is never inverted or
structurally altered. ``__UA_ERROR`` is the sole error block and contains
a single ``assert false``.

Pre-conditions the caller must ensure (e.g. via
:func:`ctac.ua.uniquify_asserts`):

- every ``AssertCmd.predicate`` is a :class:`SymbolRef` or
  :class:`ConstExpr` — run PURIFY_ASSERT first to get there.
- no block is already named ``__UA_ERROR``.

Semantic model of the special cases:

- ``assert false`` becomes an unconditional ``goto __UA_ERROR`` and any
  commands sequentially after it in the same block are dropped as
  unreachable.
- ``assert true`` is a no-op on the merged program; callers are expected
  to have stripped these via :func:`ctac.analysis.remove_true_asserts`,
  but the strategy treats them as no-ops if they slip through.
"""

from __future__ import annotations

import itertools

from ctac.ast.nodes import (
    AssertCmd,
    AssumeExpCmd,
    ConstExpr,
    JumpCmd,
    JumpiCmd,
    SymbolRef,
    TacCmd,
)
from ctac.ir.models import TacBlock, TacProgram
from ctac.rewrite.unparse import canonicalize_cmd
from ctac.ua.model import UnifyAssertsResult

ERROR_BLOCK_ID = "__UA_ERROR"


def merge_asserts(program: TacProgram) -> UnifyAssertsResult:
    """Redirect every ``AssertCmd`` to a shared ``__UA_ERROR`` block.

    Returns a :class:`UnifyAssertsResult`. When the input has at most one
    assertion the program is returned unchanged with ``was_noop=True``;
    otherwise the program is rewritten and ``asserts_merged`` counts how
    many asserts were redirected (including any ``assert false`` converted
    to unconditional jumps).
    """
    assert_sites = [
        (b.id, i, c)
        for b in program.blocks
        for i, c in enumerate(b.commands)
        if isinstance(c, AssertCmd)
    ]

    if len(assert_sites) <= 1:
        return UnifyAssertsResult(
            program=program,
            asserts_merged=0,
            error_block_id="",
            was_noop=True,
        )

    _validate_predicates(assert_sites)
    if any(b.id == ERROR_BLOCK_ID for b in program.blocks):
        raise ValueError(
            f"block {ERROR_BLOCK_ID!r} already exists; merge_asserts would collide"
        )

    fresh = itertools.count(0)
    new_blocks: list[TacBlock] = []
    merged = 0
    for block in program.blocks:
        split, block_merged = _split_block_for_asserts(block, fresh)
        new_blocks.extend(split)
        merged += block_merged

    new_blocks.append(_make_error_block())

    return UnifyAssertsResult(
        program=TacProgram(blocks=new_blocks),
        asserts_merged=merged,
        error_block_id=ERROR_BLOCK_ID,
        was_noop=False,
    )


def _validate_predicates(
    assert_sites: list[tuple[str, int, AssertCmd]],
) -> None:
    for block_id, idx, cmd in assert_sites:
        pred = cmd.predicate
        if not isinstance(pred, (SymbolRef, ConstExpr)):
            raise ValueError(
                f"AssertCmd at {block_id}[{idx}] has predicate of type "
                f"{type(pred).__name__}; merge_asserts requires SymbolRef or "
                f"ConstExpr predicates. Run PURIFY_ASSERT (e.g. "
                f"`ctac rw --purify-assert`) first."
            )


def _split_block_for_asserts(
    block: TacBlock,
    fresh: itertools.count,
) -> tuple[list[TacBlock], int]:
    """Split ``block`` at each AssertCmd. Returns (new_blocks, count)."""
    result: list[TacBlock] = []
    merged = 0
    current_id = block.id
    current_cmds: list[TacCmd] = []
    remaining = list(block.commands)
    idx = 0
    while idx < len(remaining):
        cmd = remaining[idx]
        if not isinstance(cmd, AssertCmd):
            current_cmds.append(cmd)
            idx += 1
            continue

        pred = cmd.predicate
        # assert true → ignore; the block stays intact around it (the
        # command is just dropped). Pre-pass should have removed it, but
        # treating it as a no-op here keeps the strategy robust.
        if isinstance(pred, ConstExpr) and pred.value == "true":
            idx += 1
            continue

        merged += 1
        if isinstance(pred, ConstExpr) and pred.value == "false":
            current_cmds.append(_raw(JumpCmd(raw="", target=ERROR_BLOCK_ID)))
            result.append(
                TacBlock(
                    id=current_id,
                    successors=[ERROR_BLOCK_ID],
                    commands=current_cmds,
                )
            )
            # Anything after `assert false` in this block is unreachable.
            return result, merged

        assert isinstance(pred, SymbolRef)  # _validate_predicates guarantees this.
        cont_id = f"{block.id}_UA{next(fresh)}"
        current_cmds.append(
            _raw(
                JumpiCmd(
                    raw="",
                    then_target=cont_id,
                    else_target=ERROR_BLOCK_ID,
                    condition=pred.name,
                )
            )
        )
        result.append(
            TacBlock(
                id=current_id,
                successors=[cont_id, ERROR_BLOCK_ID],
                commands=current_cmds,
            )
        )
        current_id = cont_id
        current_cmds = [_raw(AssumeExpCmd(raw="", condition=SymbolRef(pred.name)))]
        idx += 1

    result.append(
        TacBlock(
            id=current_id,
            successors=list(block.successors),
            commands=current_cmds,
        )
    )
    return result, merged


def _make_error_block() -> TacBlock:
    err = _raw(
        AssertCmd(
            raw="",
            predicate=ConstExpr("false"),
            message="unified assertion failure",
        )
    )
    return TacBlock(id=ERROR_BLOCK_ID, successors=[], commands=[err])


def _raw(cmd: TacCmd) -> TacCmd:
    """Populate ``cmd.raw`` via the canonical unparser when it's empty."""
    if cmd.raw:
        return cmd
    return canonicalize_cmd(cmd)
