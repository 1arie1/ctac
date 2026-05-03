"""Shared input/output plumbing for project-aware TAC commands.

Each command that takes a TAC path and (optionally) writes output
gains two integration points:

1. **Input**: instead of calling :func:`resolve_user_path` +
   :func:`resolve_tac_input_path` directly, call
   :func:`resolve_project_or_tac`. If the user passed a ``.ctac``
   project directory, the helper opens the project and returns
   ``ResolvedInput.tac_path = prj.head_path()`` along with the open
   :class:`Project` handle.

2. **Output**: after the command produces an artifact (TAC, htac,
   smt, ...), call :func:`ingest_or_write_text` /
   :func:`ingest_or_write_program`. Behavior depends on whether
   ``-o`` was given and whether the input was a project:

   - ``-o`` given → write to the user's path; no project ingestion.
   - project, no ``-o`` → write to a temp file, ingest into the
     project (advancing HEAD for HEAD-moving commands), unlink the
     temp.
   - no project, no ``-o`` → caller's responsibility (typically
     stream to stdout).

The helpers handle the temp-file lifecycle so each command stays
short and consistent.
"""

from __future__ import annotations

import tempfile
from dataclasses import dataclass, field
from pathlib import Path
from typing import Optional

from ctac.ir.models import TacFile, TacProgram
from ctac.project import Project, ProjectError
from ctac.project.types import ObjectInfo, ObjectKind
from ctac.tool.input_resolution import resolve_tac_input_path, resolve_user_path
from ctac.tool.tac_output import write_program_to_path


@dataclass
class ResolvedInput:
    """Resolved input for a TAC command.

    ``tac_path`` is the file to feed :func:`parse_path`. ``project``
    is the open :class:`Project` if the user passed a project
    directory, else None. ``warnings`` aggregates warnings from
    user-path resolution and (when no project) the Certora-output
    resolver.
    """

    tac_path: Path
    project: Optional[Project] = None
    warnings: list[str] = field(default_factory=list)


def resolve_project_or_tac(path: Path | None) -> ResolvedInput:
    """Resolve a user path that may be a TAC file, a Certora output
    directory, or a ``.ctac`` project directory.

    Project directories take precedence: if ``path`` contains a
    ``.ctac/HEAD``, the project is opened and HEAD's content path is
    returned. Otherwise the existing TAC-input resolver runs.
    """
    user_path, user_warnings = resolve_user_path(path)
    if user_path.is_dir() and Project.is_project(user_path):
        try:
            prj = Project.open(user_path)
        except ProjectError as e:
            raise ValueError(f"failed to open project at {user_path}: {e}") from e
        return ResolvedInput(
            tac_path=prj.head_path(),
            project=prj,
            warnings=list(user_warnings),
        )
    tac_path, input_warnings = resolve_tac_input_path(user_path)
    return ResolvedInput(
        tac_path=tac_path,
        project=None,
        warnings=list(user_warnings) + list(input_warnings),
    )


def ingest_or_write_program(
    *,
    explicit_output: Optional[Path],
    project: Optional[Project],
    tac: TacFile,
    program: TacProgram,
    extra_symbols: tuple[tuple[str, str], ...] = (),
    command: str,
    kind: ObjectKind,
    args: list[str] | None = None,
    advance_head: bool,
) -> tuple[Optional[Path], Optional[ObjectInfo]]:
    """Write a TAC/htac program to its appropriate destination.

    Returns ``(written_path, object_info)``:
    - ``-o`` given → ``(explicit_output, None)``.
    - project, no ``-o`` → ``(symlink_path, ObjectInfo)``. The temp
      file is created, written, ingested, and unlinked; the returned
      path is the friendly symlink in the project root.
    - neither → ``(None, None)``; caller should stream to stdout.
    """
    if explicit_output is not None:
        write_program_to_path(
            output_path=explicit_output,
            tac=tac,
            program=program,
            extra_symbols=extra_symbols,
        )
        return explicit_output, None

    if project is None:
        return None, None

    suffix = _suffix_for_kind(kind)
    with tempfile.NamedTemporaryFile(
        prefix="ctac-prj-", suffix=suffix, delete=False
    ) as tmp_handle:
        tmp_path = Path(tmp_handle.name)
    try:
        write_program_to_path(
            output_path=tmp_path,
            tac=tac,
            program=program,
            extra_symbols=extra_symbols,
        )
        info = project.add(
            tmp_path,
            kind=kind,
            parents=[project.head_sha] if project.manifest.head else [],
            command=command,
            args=list(args or []),
            advance_head=advance_head,
        )
    finally:
        tmp_path.unlink(missing_ok=True)
    written = project.root / info.names[-1] if info.names else project.object_path(info.sha)
    return written, info


def ingest_or_write_text(
    *,
    explicit_output: Optional[Path],
    project: Optional[Project],
    text: str,
    command: str,
    kind: ObjectKind,
    args: list[str] | None = None,
    advance_head: bool,
    parents: list[str] | None = None,
) -> tuple[Optional[Path], Optional[ObjectInfo]]:
    """Like :func:`ingest_or_write_program` but for plain text artifacts
    (e.g. SMT-LIB scripts produced by ``ctac smt``)."""
    if explicit_output is not None:
        explicit_output.write_text(text, encoding="utf-8")
        return explicit_output, None

    if project is None:
        return None, None

    suffix = _suffix_for_kind(kind)
    with tempfile.NamedTemporaryFile(
        prefix="ctac-prj-", suffix=suffix, delete=False
    ) as tmp_handle:
        tmp_path = Path(tmp_handle.name)
    try:
        tmp_path.write_text(text, encoding="utf-8")
        resolved_parents = list(parents) if parents is not None else (
            [project.head_sha] if project.manifest.head else []
        )
        info = project.add(
            tmp_path,
            kind=kind,
            parents=resolved_parents,
            command=command,
            args=list(args or []),
            advance_head=advance_head,
        )
    finally:
        tmp_path.unlink(missing_ok=True)
    written = project.root / info.names[-1] if info.names else project.object_path(info.sha)
    return written, info


_KIND_SUFFIX = {
    "tac": ".tac",
    "htac": ".htac",
    "smt": ".smt2",
    "tac-set": ".tac",
    "htac-set": ".htac",
    "smt-set": ".smt2",
}


def _suffix_for_kind(kind: ObjectKind) -> str:
    return _KIND_SUFFIX.get(kind, "")
