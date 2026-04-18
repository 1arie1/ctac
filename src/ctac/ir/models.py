from __future__ import annotations

from dataclasses import dataclass, field
from typing import TYPE_CHECKING, Any

if TYPE_CHECKING:
    from ctac.ast.nodes import TacCmd

# Block id in dumps (e.g. "0_0_0_0_0_0")
NBId = str


@dataclass
class TacBlock:
    """One basic block: id, CFG successors, parsed command AST nodes."""

    id: NBId
    successors: list[NBId]
    commands: list["TacCmd"] = field(default_factory=list)

    @property
    def raw_commands(self) -> list[str]:
        """Serialized command lines (derived from command AST `raw`)."""
        return [c.raw for c in self.commands]


@dataclass
class TacProgram:
    """Program { ... } section: control-flow graph + per-block commands."""

    blocks: list[TacBlock] = field(default_factory=list)

    def block_by_id(self) -> dict[NBId, TacBlock]:
        return {b.id: b for b in self.blocks}


@dataclass
class TacFile:
    """Full contents of a `.tac` file in four logical sections."""

    symbol_table_text: str
    program: TacProgram
    axioms_text: str
    metas: dict[str, Any]
    path: str | None = None
