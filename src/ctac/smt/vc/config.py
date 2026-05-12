from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum, auto


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
    op_models: dict[str, OpConfig] = field(default_factory=dict)
