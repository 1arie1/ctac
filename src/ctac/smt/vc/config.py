from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum, auto
from typing import Any, Protocol


class FactKind(Enum):
    DEF = auto()
    ASSUME = auto()
    RANGE = auto()
    ASSERT = auto()
    LEMMA = auto()


@dataclass(frozen=True)
class AssertionPolicy:
    grouped_kinds: frozenset[FactKind] = frozenset()


class FactLowerer(Protocol):
    def lower(self, builder: Any) -> tuple[Any, ...]: ...


class OpMode(Enum):
    INLINE = auto()
    DEFINE_FUN = auto()
    UF = auto()


@dataclass(frozen=True)
class OpConfig:
    mode: OpMode
    instantiate_lemmas: bool = True
    lemma_scope: str = "callsite"
    lemmas: tuple[str, ...] = ()


@dataclass
class VCConfig:
    logic: str = "QF_UFNIA"
    produce_models: bool = False
    produce_unsat_cores: bool = False
    check_sat: bool = True
    fact_lowerer: FactLowerer | None = None
    assertion_policy: AssertionPolicy = field(default_factory=AssertionPolicy)
    op_models: dict[str, OpConfig] = field(default_factory=dict)
