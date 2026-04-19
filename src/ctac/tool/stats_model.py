from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Literal


class StatType(str, Enum):
    NUM = "num"
    STR = "str"
    TIME = "time"


@dataclass(frozen=True)
class StatValue:
    kind: StatType
    value: int | float | str


@dataclass(frozen=True)
class StatEntry:
    path: str
    value: StatValue


class StatsCollection:
    """
    Hierarchical stats keyed by dot paths.

    Path convention:
    - Dot (.) separates hierarchy levels, e.g. "expression_ops.Add".
    - Paths must be non-empty and cannot contain empty segments.

    Duplicate keys:
    - Last write wins.
    - Insertion order is preserved for deterministic iteration.
    """

    def __init__(self) -> None:
        self._by_path: dict[str, StatValue] = {}

    def add_num(self, path: str, value: int | float) -> None:
        self._set(path, StatValue(StatType.NUM, value))

    def add_str(self, path: str, value: str) -> None:
        self._set(path, StatValue(StatType.STR, value))

    def add_time(self, path: str, value: int | float, *, unit: Literal["ms", "s"] = "ms") -> None:
        if unit == "ms":
            ms_value = float(value)
        else:
            ms_value = float(value) * 1000.0
        self._set(path, StatValue(StatType.TIME, ms_value))

    def entries(self) -> list[StatEntry]:
        return [StatEntry(path, value) for path, value in self._by_path.items()]

    def _set(self, path: str, value: StatValue) -> None:
        self._validate_path(path)
        self._by_path[path] = value

    @staticmethod
    def _validate_path(path: str) -> None:
        if not path or path.strip() == "":
            raise ValueError("stats path cannot be empty")
        parts = path.split(".")
        if any(part.strip() == "" for part in parts):
            raise ValueError(f"stats path has empty hierarchy segment: {path!r}")
