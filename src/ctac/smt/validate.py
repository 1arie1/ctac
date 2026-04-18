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


def validate_program_for_smt(program: TacProgram) -> AssertSite:
    site = find_assert_site(program)
    ensure_assert_last(program, site)
    ensure_acyclic(program)
    return site
