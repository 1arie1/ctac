"""Load a TAC CFG into a networkx DiGraph + entry/assert resolution.

Pure in-process (no subprocess to `ctac cfg`): reuses `ctac.parse` to
get a `TacFile`, walks `block.successors` to build the graph. Block
IDs are kept verbatim (e.g. ``"0_0_0_0_0_0"``).

The cover assumes:
- single AssertCmd (caller has run `ctac ua` first);
- loop-free TAC (CFG is a DAG); the cover's random-walk samples
  assume DAG semantics.

Both invariants are checked at load time so a downstream cover-loop
bug doesn't silently produce nonsense.
"""
from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path

import networkx as nx

from ctac.ast.nodes import AssertCmd
from ctac.ir.models import NBId, TacFile
from ctac.parse.tac_file import parse_path


@dataclass(frozen=True)
class CfgInfo:
    """Resolved CFG metadata for a single-assert TAC file."""

    graph: nx.DiGraph
    entry: NBId
    assert_block: NBId
    tac: TacFile


class CfgError(ValueError):
    """CFG-load preconditions violated (no entry, no assert, cycle, ...)."""


def load_cfg(tac_path: Path | str) -> CfgInfo:
    """Parse a `.tac` file and return its CFG + entry / assert IDs.

    Raises `CfgError` if the file has no assert, multiple asserts, no
    entry block, or contains a cycle (CFG cover requires a DAG)."""
    tac = parse_path(Path(tac_path))
    g = _build_graph(tac)
    entry = _resolve_entry(tac, g)
    assert_block = _resolve_assert_block(tac)
    _check_dag(g)
    return CfgInfo(graph=g, entry=entry, assert_block=assert_block, tac=tac)


def _build_graph(tac: TacFile) -> nx.DiGraph:
    """Walk `block.successors` to populate a DiGraph."""
    g = nx.DiGraph()
    for b in tac.program.blocks:
        g.add_node(b.id)
    for b in tac.program.blocks:
        for s in b.successors:
            g.add_edge(b.id, s)
    return g


def _resolve_entry(tac: TacFile, g: nx.DiGraph) -> NBId:
    """The unique block with no predecessors. Multiple roots ⇒ error."""
    blocks = list(tac.program.blocks)
    if not blocks:
        raise CfgError('TAC has no blocks')
    roots = [n for n in g.nodes if g.in_degree(n) == 0]
    if len(roots) == 1:
        return roots[0]
    if len(roots) == 0:
        raise CfgError('CFG has no entry (every block has a predecessor)')
    # Multiple roots: prefer the first block listed in the TAC if it's
    # among the roots — TAC dumps put the entry first conventionally.
    first = blocks[0].id
    if first in roots:
        return first
    raise CfgError(
        f'CFG has multiple entry candidates: {sorted(roots)!r}')


def _resolve_assert_block(tac: TacFile) -> NBId:
    """Return the unique block containing an AssertCmd.

    Single-assert is the cover's precondition; users should have run
    `ctac ua` first."""
    asserters = [b.id for b in tac.program.blocks
                  if any(isinstance(c, AssertCmd) for c in b.commands)]
    if len(asserters) == 1:
        return asserters[0]
    if not asserters:
        raise CfgError('TAC has no AssertCmd; run `ctac ua` first')
    raise CfgError(
        f'TAC has {len(asserters)} AssertCmd blocks (need exactly 1); '
        f'run `ctac ua` first. found: {asserters!r}')


def _check_dag(g: nx.DiGraph) -> None:
    if not nx.is_directed_acyclic_graph(g):
        cycles = list(nx.simple_cycles(g))
        sample = cycles[0] if cycles else []
        raise CfgError(
            f'CFG has a cycle (cover requires loop-free TAC). '
            f'Example cycle: {sample!r}')


def reachable_to_assert(info: CfgInfo) -> set[NBId]:
    """All blocks that can reach the assert. Useful to trim dead
    sub-CFGs before sampling — e.g. blocks that pin nothing because
    they only feed unreachable terminators."""
    return set(nx.ancestors(info.graph, info.assert_block)) \
        | {info.assert_block}


def blocks_on_entry_to_assert_paths(info: CfgInfo) -> set[NBId]:
    """Blocks that lie on at least one entry → assert simple path.

    Intersection of `descendants(entry)` (reachable from entry) and
    `ancestors(assert) ∪ {assert}` (can reach assert)."""
    g = info.graph
    forward = set(nx.descendants(g, info.entry)) | {info.entry}
    backward = set(nx.ancestors(g, info.assert_block)) | {info.assert_block}
    return forward & backward
