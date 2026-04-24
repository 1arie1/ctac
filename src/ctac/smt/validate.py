from __future__ import annotations

from dataclasses import dataclass

import networkx as nx

from ctac.ast.nodes import AssertCmd
from ctac.graph import Cfg
from ctac.ir.models import TacProgram


class SmtValidationError(ValueError):
    """Raised when a TAC program does not meet SMT encoding preconditions."""


@dataclass(frozen=True)
class AssertSite:
    block_id: str
    cmd_index: int
    command: AssertCmd


def find_assert_site(program: TacProgram) -> AssertSite:
    sites: list[AssertSite] = []
    for block in program.blocks:
        for idx, cmd in enumerate(block.commands):
            if isinstance(cmd, AssertCmd):
                sites.append(AssertSite(block_id=block.id, cmd_index=idx, command=cmd))
    if len(sites) != 1:
        raise SmtValidationError(
            f"expected exactly one AssertCmd in program, found {len(sites)}"
        )
    return sites[0]


def ensure_assert_last(program: TacProgram, site: AssertSite) -> None:
    block = program.block_by_id().get(site.block_id)
    if block is None:
        raise SmtValidationError(f"assert block {site.block_id!r} not found in program")
    if site.cmd_index != len(block.commands) - 1:
        raise SmtValidationError(
            f"AssertCmd must be the last command in block {site.block_id}"
        )


def ensure_acyclic(program: TacProgram) -> None:
    g = Cfg(program).to_digraph()
    if not nx.is_directed_acyclic_graph(g):
        raise SmtValidationError("SMT encoding currently requires a loop-free (acyclic) TAC program")


def ensure_no_critical_edges(program: TacProgram) -> None:
    # A critical edge (u, v) has |succ(u)| > 1 AND |pred(v)| > 1. sea_vc's
    # at-most-one exclusivity over a merge block's predecessors is sound only
    # when those predecessors can't both be reachable in one execution.
    # Critical-edge freedom is a sufficient structural condition: if every
    # predecessor of a merge block has that block as its sole successor, no
    # two of them can be nested, so their block-reachability predicates are
    # mutually exclusive per execution.
    g = Cfg(program).to_digraph()
    offenders: list[tuple[str, str, int, int]] = []
    for u, v in g.edges():
        out_u = g.out_degree(u)
        in_v = g.in_degree(v)
        if out_u > 1 and in_v > 1:
            offenders.append((u, v, out_u, in_v))
    if offenders:
        u, v, out_u, in_v = offenders[0]
        extra = f" (and {len(offenders) - 1} more)" if len(offenders) > 1 else ""
        raise SmtValidationError(
            f"critical edge ({u} -> {v}) detected: {u} has {out_u} successors "
            f"and {v} has {in_v} predecessors{extra}. sea_vc's merge-block "
            "exclusivity is unsound on critical edges; split them (e.g. insert "
            "a single-successor shim block on each branch) before encoding."
        )


def validate_program_for_smt(program: TacProgram) -> AssertSite:
    site = find_assert_site(program)
    ensure_assert_last(program, site)
    ensure_acyclic(program)
    ensure_no_critical_edges(program)
    return site
