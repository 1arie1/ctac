"""Split critical edges by inserting single-command shim blocks.

A critical edge ``(u, v)`` has ``|succ(u)| > 1`` and ``|pred(v)| > 1``.
This transform inserts one shim block per critical edge:

    u:     ... ; JumpiCmd(then=v, else=w, c)
    v:     ...                                   (many predecessors)

becomes

    u:           ... ; JumpiCmd(then=u_to_v, else=w, c)
    u_to_v:      JumpCmd v                       (single pred, single succ)
    v:           ...

Each shim has exactly one predecessor (``u``) and one successor (``v``),
so no new critical edges are introduced and every edge incident to the
shim is non-critical.

After the pass, every merge block's predecessors are single-successor
blocks — exactly the structural property that makes sea_vc's
predecessor exclusivity sound.
"""

from __future__ import annotations

import itertools

from ctac.ast.nodes import JumpCmd, JumpiCmd
from ctac.ir.models import NBId, TacBlock, TacProgram
from ctac.rewrite.unparse import canonicalize_cmd
from ctac.splitcrit.model import SplitCritResult


def split_critical_edges(program: TacProgram) -> SplitCritResult:
    """Return a program with every critical edge broken by a shim block."""
    existing_ids = {b.id for b in program.blocks}
    preds = _predecessor_counts(program)

    critical: list[tuple[str, str]] = []
    for block in program.blocks:
        out = block.successors
        if len(out) <= 1:
            continue
        for succ in out:
            if preds.get(succ, 0) > 1:
                critical.append((block.id, succ))

    if not critical:
        return SplitCritResult(
            program=program,
            shims_added=0,
            edges_split=(),
            was_noop=True,
        )

    shim_ids = _mint_shim_ids(critical, existing_ids)

    new_blocks: list[TacBlock] = []
    for block in program.blocks:
        new_block = _rewrite_block(block, shim_ids)
        new_blocks.append(new_block)
        # Emit shims for edges that originated in this block, keeping
        # shim insertion adjacent to the source for readability.
        for succ in block.successors:
            key = (block.id, succ)
            if key in shim_ids:
                new_blocks.append(_make_shim(shim_ids[key], succ))

    return SplitCritResult(
        program=TacProgram(blocks=new_blocks),
        shims_added=len(shim_ids),
        edges_split=tuple(shim_ids.keys()),
        was_noop=False,
    )


def _predecessor_counts(program: TacProgram) -> dict[NBId, int]:
    counts: dict[NBId, int] = {}
    for block in program.blocks:
        for succ in block.successors:
            counts[succ] = counts.get(succ, 0) + 1
    return counts


def _mint_shim_ids(
    critical: list[tuple[str, str]],
    existing_ids: set[str],
) -> dict[tuple[str, str], str]:
    # Prefer readable `{u}_to_{v}` ids; fall back to a suffix counter on
    # collision with existing or already-minted ids.
    chosen: dict[tuple[str, str], str] = {}
    used = set(existing_ids)
    for u, v in critical:
        base = f"{u}_to_{v}"
        name = base
        if name in used:
            for i in itertools.count(1):
                name = f"{base}_{i}"
                if name not in used:
                    break
        chosen[(u, v)] = name
        used.add(name)
    return chosen


def _rewrite_block(
    block: TacBlock,
    shim_ids: dict[tuple[str, str], str],
) -> TacBlock:
    new_successors: list[str] = [
        shim_ids.get((block.id, s), s) for s in block.successors
    ]
    new_commands = list(block.commands)
    # The terminator names successors textually; rewrite it in lockstep.
    if new_commands:
        last = new_commands[-1]
        if isinstance(last, JumpCmd):
            new_target = shim_ids.get((block.id, last.target), last.target)
            if new_target != last.target:
                new_commands[-1] = canonicalize_cmd(
                    JumpCmd(raw="", target=new_target)
                )
        elif isinstance(last, JumpiCmd):
            new_then = shim_ids.get((block.id, last.then_target), last.then_target)
            new_else = shim_ids.get((block.id, last.else_target), last.else_target)
            if new_then != last.then_target or new_else != last.else_target:
                new_commands[-1] = canonicalize_cmd(
                    JumpiCmd(
                        raw="",
                        then_target=new_then,
                        else_target=new_else,
                        condition=last.condition,
                    )
                )
    return TacBlock(id=block.id, successors=new_successors, commands=new_commands)


def _make_shim(shim_id: str, target: str) -> TacBlock:
    jump = canonicalize_cmd(JumpCmd(raw="", target=target))
    return TacBlock(id=shim_id, successors=[target], commands=[jump])
