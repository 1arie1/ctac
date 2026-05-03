"""Public dataclasses and exceptions for ``ctac.project``."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Literal


ObjectKind = Literal[
    "tac",
    "htac",
    "smt",
    "tac-set",
    "htac-set",
    "smt-set",
]

OBJECT_KINDS: tuple[ObjectKind, ...] = (
    "tac",
    "htac",
    "smt",
    "tac-set",
    "htac-set",
    "smt-set",
)


@dataclass(frozen=True)
class ObjectInfo:
    """Provenance record for one project object.

    ``sha`` is the canonical id (full sha256 hex). ``names`` is the
    list of friendly symlinks in the project root that point at this
    object — there can be more than one if the same content was added
    twice with different ``suggested_name`` values.
    """

    sha: str
    kind: ObjectKind
    parents: tuple[str, ...]
    command: str
    args: tuple[str, ...]
    names: tuple[str, ...]
    created: str  # ISO8601 UTC, e.g. "2026-05-03T12:34:56Z"
    size: int


class ProjectError(Exception):
    """Raised by ``ctac.project`` for project-specific failures."""
