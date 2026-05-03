"""Project format for ctac.

A project is a working directory with a ``.ctac/`` sidecar that
tracks a content-addressed object store, HEAD + named refs, a
provenance manifest, and an append-only command log. Friendly-name
symlinks in the project root (``base.tac``, ``base.rw.tac``, ...)
point at canonical objects under ``.ctac/objects/``.

Public API:

- :class:`Project` — high-level read/write surface.
- :class:`ObjectInfo` — per-object provenance record.
- :data:`ObjectKind` — ``Literal`` of supported object kinds.
- :class:`ProjectError` — raised on project-specific failures.
"""

from ctac.project.core import DOT_CTAC, Project
from ctac.project.types import OBJECT_KINDS, ObjectInfo, ObjectKind, ProjectError


__all__ = [
    "DOT_CTAC",
    "OBJECT_KINDS",
    "ObjectInfo",
    "ObjectKind",
    "Project",
    "ProjectError",
]
