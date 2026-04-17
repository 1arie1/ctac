"""Shared runtime value types for evaluator modules."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Literal

HavocMode = Literal["zero", "random", "ask"]
ValueKind = Literal["bv", "int", "bool"]


@dataclass(frozen=True)
class Value:
    kind: ValueKind
    data: int | bool

