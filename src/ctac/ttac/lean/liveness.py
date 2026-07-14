"""Phi-aware backward liveness for the shallow embedding.

Each shallow block-def takes its live-in variables plus its phi targets
as parameters. Phi arm values are charged to the *predecessor edge* (the
predecessor's call site passes them), never to the block's own live-in,
so a phi target is defined exactly where the shallow call happens - the
"phi = block parameter" translation.

The CFG is validated acyclic before this runs, so one reverse
topological pass suffices (no fixpoint).
"""

from __future__ import annotations

from dataclasses import dataclass

from ctac.ttac import ast
from ctac.ttac.analysis import cfg
from ctac.ttac.analysis.defuse import cmd_defs, cmd_uses, terminator_uses


@dataclass(frozen=True)
class BlockLiveness:
    live_in: dict[str, frozenset[str]]  # phi targets excluded
    phi_targets: dict[str, tuple[str, ...]]  # per block, command order
    params: dict[str, tuple[str, ...]]  # sorted(live_in | phi_targets)


def block_liveness(program: ast.Program) -> BlockLiveness:
    by_label = {b.label: b for b in program.blocks}
    phi_targets = {
        b.label: tuple(
            c.target.name for c in b.commands if isinstance(c, ast.Phi)
        )
        for b in program.blocks
    }

    live_in: dict[str, frozenset[str]] = {}
    for label in reversed(cfg.topo_order(program)):
        block = by_label[label]
        live: set[str] = set()
        for succ in dict.fromkeys(cfg.successors(block)):
            if succ not in by_label:
                continue
            live |= live_in[succ]
            for c in by_label[succ].commands:
                if isinstance(c, ast.Phi):
                    live.update(a.value for a in c.arms if a.label == label)
        live.update(terminator_uses(block.terminator))
        for cmd in reversed(block.commands):
            for target in cmd_defs(cmd):
                live.discard(target.name)
            if not isinstance(cmd, ast.Phi):
                live.update(cmd_uses(cmd))
        live_in[label] = frozenset(live)

    params = {
        label: tuple(sorted(live_in[label] | set(phi_targets[label])))
        for label in live_in
    }
    return BlockLiveness(live_in=live_in, phi_targets=phi_targets, params=params)
