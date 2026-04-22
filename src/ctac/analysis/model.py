"""Shared data models for TAC data-flow analyses."""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
from typing import Literal

from ctac.ir.models import TacProgram


class BytemapCapability(str, Enum):
    """How the program uses bytemap-sorted (memory) symbols.

    - ``BYTEMAP_FREE``: no memory symbols in the program at all.
    - ``BYTEMAP_RO``: memory symbols exist but are only havoced and read
      (via ``Select``). No ``Store`` and no ``AssignExpCmd`` targeting a
      memory-sorted LHS. This is the shape the upcoming sea_vc memory
      support will accept first.
    - ``BYTEMAP_RW``: memory is updated — either a ``Store`` expression
      appears somewhere, or some ``AssignExpCmd`` writes to a
      memory-sorted symbol (direct aliasing).
    """

    BYTEMAP_FREE = "bytemap-free"
    BYTEMAP_RO = "bytemap-ro"
    BYTEMAP_RW = "bytemap-rw"


@dataclass(frozen=True)
class ProgramPoint:
    block_id: str
    cmd_index: int


@dataclass(frozen=True)
class DefinitionSite:
    def_id: int
    origin_uid: str
    symbol_id: int
    symbol: str
    block_id: str
    cmd_index: int
    cmd_kind: str
    raw: str


@dataclass(frozen=True)
class UseSite:
    symbol_id: int
    symbol: str
    block_id: str
    cmd_index: int
    cmd_kind: str
    raw: str
    is_weak: bool = False


@dataclass(frozen=True)
class BlockDefUse:
    block_id: str
    defs: tuple[str, ...]
    uses: tuple[str, ...]
    kills: tuple[str, ...]
    definition_sites: tuple[DefinitionSite, ...]
    use_sites: tuple[UseSite, ...]
    weak_use_sites: tuple[UseSite, ...]
    dsa_shape_ok: bool
    dsa_shape_violation: str | None


@dataclass(frozen=True)
class DefUseResult:
    by_block: dict[str, BlockDefUse]
    definitions_by_symbol: dict[str, tuple[DefinitionSite, ...]]
    uses_by_symbol: dict[str, tuple[UseSite, ...]]
    weak_uses_by_symbol: dict[str, tuple[UseSite, ...]]
    symbol_to_id: dict[str, int]
    id_to_symbol: tuple[str, ...]
    definitions: tuple[DefinitionSite, ...]  # indexed by `def_id`


@dataclass(frozen=True)
class ReachingDefinitionsResult:
    in_by_block: dict[str, dict[str, tuple[DefinitionSite, ...]]]
    out_by_block: dict[str, dict[str, tuple[DefinitionSite, ...]]]
    in_by_command: dict[ProgramPoint, dict[str, tuple[DefinitionSite, ...]]]
    out_by_command: dict[ProgramPoint, dict[str, tuple[DefinitionSite, ...]]]


@dataclass(frozen=True)
class LivenessResult:
    live_in_by_block: dict[str, tuple[str, ...]]
    live_out_by_block: dict[str, tuple[str, ...]]
    live_before_command: dict[ProgramPoint, tuple[str, ...]]
    live_after_command: dict[ProgramPoint, tuple[str, ...]]


@dataclass(frozen=True)
class UseBeforeDefIssue:
    symbol: str
    block_id: str
    cmd_index: int
    cmd_kind: str
    raw: str


@dataclass(frozen=True)
class UseBeforeDefResult:
    issues: tuple[UseBeforeDefIssue, ...]


@dataclass(frozen=True)
class DsaIssue:
    kind: Literal["shape", "ambiguous-use"]
    symbol: str | None
    block_id: str
    cmd_index: int | None
    detail: str


@dataclass(frozen=True)
class DsaDynamicAssignment:
    symbol: str
    block_id: str
    cmd_index: int
    cmd_kind: str
    raw: str
    sibling_defs: tuple[str, ...]  # "block_id:cmd_index"


@dataclass(frozen=True)
class DsaResult:
    issues: tuple[DsaIssue, ...]
    dynamic_assignments: tuple[DsaDynamicAssignment, ...] = field(default_factory=tuple)

    @property
    def is_valid(self) -> bool:
        return len(self.issues) == 0


@dataclass(frozen=True)
class ControlDependenceResult:
    edges: tuple[tuple[str, str], ...]  # controller -> dependent
    postdominators: dict[str, tuple[str, ...]]


@dataclass(frozen=True)
class DeadAssignment:
    symbol: str
    block_id: str
    cmd_index: int
    cmd_kind: str
    raw: str


@dataclass(frozen=True)
class RemovedAssert:
    block_id: str
    cmd_index: int
    raw: str


@dataclass(frozen=True)
class DceResult:
    removed: tuple[DeadAssignment, ...]
    program: TacProgram
    removed_asserts: tuple[RemovedAssert, ...] = ()


@dataclass(frozen=True)
class RemovedAssume:
    symbol: str
    block_id: str
    cmd_index: int
    cmd_kind: str
    raw: str
    reason: str


@dataclass(frozen=True)
class UceResult:
    removed: tuple[RemovedAssume, ...]
    program: TacProgram
