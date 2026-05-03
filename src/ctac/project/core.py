"""High-level Project API.

A :class:`Project` is the public surface other ctac commands and the
REPL use. Its job is to glue together the manifest, refs, log, and
object-store modules behind a simple API:

- :meth:`Project.init` creates a new ``.ctac/`` and registers a base
  TAC file.
- :meth:`Project.open` loads an existing project.
- :meth:`Project.head_path` returns an absolute path to the current
  HEAD's content (suitable for read-only commands).
- :meth:`Project.add` ingests a produced artifact (TAC, htac, smt,
  or a fileset directory), records provenance, creates a friendly-
  name symlink, and optionally advances HEAD.
- :meth:`Project.info` / :meth:`resolve` / :meth:`list_objects` are
  the read API.
"""

from __future__ import annotations

from datetime import datetime, timezone
from pathlib import Path

from ctac.project import refs as refs_mod
from ctac.project import store as store_mod
from ctac.project.log import LogEntry, append_log
from ctac.project.manifest import (
    Manifest,
    read_manifest,
    write_manifest,
)
from ctac.project.naming import auto_name, auto_set_name, collision_suffix
from ctac.project.types import OBJECT_KINDS, ObjectInfo, ObjectKind, ProjectError


DOT_CTAC = ".ctac"


class Project:
    """A ctac working directory: a project root plus a ``.ctac/`` sidecar."""

    root: Path
    manifest: Manifest

    # ------------------------------------------------------ construction

    def __init__(self, root: Path, manifest: Manifest) -> None:
        self.root = root
        self.manifest = manifest

    @property
    def dot_ctac(self) -> Path:
        return self.root / DOT_CTAC

    @classmethod
    def is_project(cls, path: Path) -> bool:
        return (path / DOT_CTAC / "HEAD").is_file()

    @classmethod
    def open(cls, root: Path) -> "Project":
        if not cls.is_project(root):
            raise ProjectError(f"not a ctac project: {root} (no {DOT_CTAC}/HEAD)")
        manifest = read_manifest(root / DOT_CTAC)
        return cls(root, manifest)

    @classmethod
    def init(
        cls,
        root: Path,
        base_tac: Path,
        *,
        label: str = "base",
        force: bool = False,
    ) -> "Project":
        """Create a new project at ``root`` with ``base_tac`` as the initial object.

        ``root`` is created if missing. If ``root/.ctac`` already exists,
        ``force=True`` is required to overwrite it.
        """
        if not base_tac.is_file():
            raise ProjectError(f"base TAC not found or not a file: {base_tac}")
        root.mkdir(parents=True, exist_ok=True)
        dot = root / DOT_CTAC
        if dot.exists():
            if not force:
                raise ProjectError(
                    f"project already exists at {root} (use force=True to overwrite)"
                )
            _rmtree(dot)
        dot.mkdir(parents=True, exist_ok=False)
        (dot / "objects").mkdir(parents=True)
        (dot / "refs").mkdir(parents=True)

        prj = cls(root, Manifest())
        # Determine the friendly name from the input filename.
        suggested = base_tac.name
        info = prj.add(
            base_tac,
            kind=_kind_from_extension(base_tac, default="tac"),
            parents=[],
            command="init",
            args=[],
            suggested_name=suggested,
            advance_head=True,
        )
        prj.set_label(info.sha, label)
        return prj

    # ------------------------------------------------------- read API

    @property
    def head_sha(self) -> str:
        return refs_mod.read_head(self.dot_ctac)

    @property
    def head(self) -> ObjectInfo:
        return self.info(self.head_sha)

    def head_path(self) -> Path:
        """Absolute path to HEAD's content (file or directory)."""
        return self.object_path(self.head_sha)

    def info(self, ref: str) -> ObjectInfo:
        sha = self.resolve(ref)
        return self.manifest.objects[sha]

    def resolve(self, ref: str) -> str:
        """Resolve a reference to a full sha.

        Recognized forms (checked in order):
          1. full sha (64 hex chars), if present in the manifest
          2. label name (entry in ``refs/<label>``)
          3. friendly name (existing symlink in the project root)
          4. unique sha prefix (>= 4 hex chars)
          5. relative path inside the project root (file or symlink
             pointing at an object)
        """
        if not ref:
            raise ProjectError("empty reference")

        # 1. full sha
        if _looks_like_sha(ref) and ref in self.manifest.objects:
            return ref

        # 2. label
        if refs_mod.is_valid_label(ref):
            try:
                sha = refs_mod.read_ref(self.dot_ctac, ref)
            except FileNotFoundError:
                sha = ""
            if sha and sha in self.manifest.objects:
                return sha

        # 3. friendly-name symlink in project root
        link_sha = store_mod.friendly_name_target_sha(self.root, ref)
        if link_sha and link_sha in self.manifest.objects:
            return link_sha

        # 4. unique sha prefix
        if _looks_like_short_sha(ref):
            matches = [s for s in self.manifest.objects if s.startswith(ref)]
            if len(matches) == 1:
                return matches[0]
            if len(matches) > 1:
                raise ProjectError(
                    f"ambiguous sha prefix {ref!r}: {len(matches)} matches"
                )

        # 5. project-relative path (might be a symlink to an object)
        try:
            cand = (self.root / ref).resolve(strict=False)
            if cand.is_relative_to(self.dot_ctac / "objects"):
                rel = cand.relative_to(self.dot_ctac / "objects")
                parts = rel.parts
                if len(parts) == 2 and len(parts[0]) == 2:
                    sha = parts[0] + parts[1]
                    if sha in self.manifest.objects:
                        return sha
        except (OSError, ValueError):
            pass

        raise ProjectError(f"could not resolve reference: {ref!r}")

    def list_objects(self) -> list[ObjectInfo]:
        """All objects, oldest-first by ``created`` timestamp."""
        return sorted(self.manifest.objects.values(), key=lambda o: (o.created, o.sha))

    def object_path(self, ref: str) -> Path:
        sha = self.resolve(ref)
        return store_mod.object_path(self.dot_ctac, sha)

    # ------------------------------------------------------- write API

    def add(
        self,
        content_path: Path,
        *,
        kind: ObjectKind,
        parents: list[str],
        command: str,
        args: list[str],
        suggested_name: str | None = None,
        advance_head: bool = False,
    ) -> ObjectInfo:
        """Ingest ``content_path`` (file or directory) as a project object.

        - Hashes the content; if new, copies it into the object store.
        - Creates / reuses a friendly-name symlink in the project root.
        - Records provenance in the manifest and the log.
        - Optionally advances HEAD to the new object.

        Returns the ``ObjectInfo`` for the resulting object. If the
        content was already present (same sha), the existing record is
        kept and only the friendly-name list is extended (idempotent).
        """
        if kind not in OBJECT_KINDS:
            raise ProjectError(f"unknown object kind: {kind!r}")
        content_path = content_path.resolve()
        is_set = kind.endswith("-set")

        if is_set:
            sha, _stored_path, was_new = store_mod.store_fileset(
                self.dot_ctac, content_path
            )
            size = _dir_size_bytes(store_mod.object_path(self.dot_ctac, sha))
        else:
            if not content_path.is_file():
                raise ProjectError(
                    f"content not found or not a file: {content_path}"
                )
            sha, _stored_path, was_new = store_mod.store_file(
                self.dot_ctac, content_path
            )
            size = store_mod.object_path(self.dot_ctac, sha).stat().st_size

        existing = self.manifest.objects.get(sha)
        names = list(existing.names) if existing is not None else []

        # Resolve the friendly name (auto + collision suffix).
        chosen_name = self._choose_friendly_name(suggested_name, command, kind, sha, names)
        if chosen_name and chosen_name not in names:
            store_mod.relink_friendly_name(
                self.root, self.dot_ctac, chosen_name, sha
            )
            names.append(chosen_name)
        elif chosen_name in names:
            # Make sure the symlink is still valid (re-create if missing).
            store_mod.relink_friendly_name(
                self.root, self.dot_ctac, chosen_name, sha
            )

        if existing is None:
            info = ObjectInfo(
                sha=sha,
                kind=kind,
                parents=tuple(parents),
                command=command,
                args=tuple(args),
                names=tuple(names),
                created=_iso_now(),
                size=size,
            )
        else:
            # Same content, extend names; keep the original creation record.
            info = ObjectInfo(
                sha=existing.sha,
                kind=existing.kind,
                parents=existing.parents,
                command=existing.command,
                args=existing.args,
                names=tuple(names),
                created=existing.created,
                size=existing.size,
            )
        self.manifest.objects[sha] = info

        if advance_head:
            refs_mod.write_head(self.dot_ctac, sha)
            self.manifest.head = sha

        write_manifest(self.manifest, self.dot_ctac)

        append_log(
            self.dot_ctac,
            LogEntry(
                ts=_iso_now(),
                command=command,
                args=tuple(args),
                result_sha=sha,
                parents=tuple(parents),
                kind=kind,
                name=chosen_name or "",
                advance_head=advance_head,
            ),
        )

        # was_new is currently informational; keep variable to make the
        # control flow explicit for future use (e.g. a --quiet/--verbose
        # selector). Reference here keeps linters happy.
        _ = was_new
        return info

    def set_head(self, ref: str) -> None:
        """Move HEAD to the object identified by ``ref``.

        ``ref`` accepts the same forms as :meth:`resolve`. The
        additional ``<set-ref>:<member-name>`` syntax materializes
        the named member of a fileset as a fresh first-class
        object (kind inferred from the set's kind: ``tac-set`` ->
        ``tac``, ``htac-set`` -> ``htac``, ``smt-set`` -> ``smt``)
        with parent = fileset, then moves HEAD to it. Useful after
        ``ua --strategy split`` / ``pin --split`` to focus a single
        case before continuing with ``rw`` / ``smt``.
        """
        if ":" in ref:
            set_ref, _, member = ref.partition(":")
            sha = self._focus_member(set_ref, member)
        else:
            sha = self.resolve(ref)
        refs_mod.write_head(self.dot_ctac, sha)
        self.manifest.head = sha
        write_manifest(self.manifest, self.dot_ctac)
        append_log(
            self.dot_ctac,
            LogEntry(
                ts=_iso_now(),
                command="set-head",
                args=(ref,),
                result_sha=sha,
                advance_head=True,
            ),
        )

    def _focus_member(self, set_ref: str, member: str) -> str:
        if not member:
            raise ProjectError("fileset member name is empty")
        set_sha = self.resolve(set_ref)
        set_info = self.manifest.objects[set_sha]
        if not set_info.kind.endswith("-set"):
            raise ProjectError(
                f"reference {set_ref!r} is not a fileset (kind={set_info.kind})"
            )
        set_dir = store_mod.object_path(self.dot_ctac, set_sha)
        member_path = set_dir / member
        if not member_path.is_file():
            raise ProjectError(
                f"fileset {set_ref!r} has no member {member!r}; "
                f"available: {sorted(p.name for p in set_dir.iterdir() if p.is_file())}"
            )
        member_kind: ObjectKind = set_info.kind[: -len("-set")]  # type: ignore[assignment]
        info = self.add(
            member_path,
            kind=member_kind,
            parents=[set_sha],
            command="focus",
            args=[member],
            suggested_name=member,
            advance_head=False,
        )
        return info.sha

    def set_label(self, ref: str, label: str) -> None:
        if not refs_mod.is_valid_label(label):
            raise ProjectError(f"invalid label: {label!r}")
        sha = self.resolve(ref)
        refs_mod.write_ref(self.dot_ctac, label, sha)
        self.manifest.labels[label] = sha
        write_manifest(self.manifest, self.dot_ctac)
        append_log(
            self.dot_ctac,
            LogEntry(
                ts=_iso_now(),
                command="label",
                args=(ref, label),
                result_sha=sha,
            ),
        )

    # -------------------------------------------------- internal helpers

    def _choose_friendly_name(
        self,
        suggested: str | None,
        command: str,
        kind: ObjectKind,
        sha: str,
        existing_names: list[str],
    ) -> str:
        """Pick a friendly name for the new object.

        Rules:
        - If ``suggested`` is given, use it (with collision suffix if a
          different sha already owns that name).
        - Otherwise derive from HEAD's most recently appended friendly
          name. Filesets get ``<stem>.<command>.split``; single-file
          kinds get ``<stem>.<command>.<ext>`` via :func:`auto_name`.
        - If no HEAD exists yet, fall back to ``base.<ext>`` (or
          ``base.<command>.split`` for filesets).
        """
        is_set = kind.endswith("-set")
        ext = _ext_for_kind(kind)
        if suggested is not None:
            base = suggested
        else:
            try:
                head_info = self.manifest.objects[self.head_sha] if self.manifest.head else None
            except (FileNotFoundError, KeyError):
                head_info = None
            parent_name = (
                head_info.names[-1]
                if head_info is not None and head_info.names
                else None
            )
            # Use the most recently appended HEAD name as the basis: when
            # an idempotent command (rw on a fixed point) extended an
            # existing object's alias list, follow-on commands should
            # chain off the new alias (`in.rw.tac`) rather than the
            # original (`in.tac`), preserving pipeline provenance in
            # the filename.
            if parent_name is None:
                base = f"base.{command}.split" if is_set else f"base.{ext}"
            elif is_set:
                base = auto_set_name(parent_name, command)
            else:
                base = auto_name(parent_name, command, ext)
        return self._dedupe_name(base, sha, existing_names)

    def _dedupe_name(
        self, candidate: str, target_sha: str, existing_names: list[str]
    ) -> str:
        """If ``candidate`` is already a project-root symlink to a different sha,
        suffix it. If it points at ``target_sha`` already (or at no entry yet),
        return as-is.
        """
        link_sha = store_mod.friendly_name_target_sha(self.root, candidate)
        if link_sha is None or link_sha == target_sha:
            # Either free or already pointing at us.
            if candidate in existing_names:
                return candidate
            link_path = self.root / candidate
            if not link_path.exists() or link_sha == target_sha:
                return candidate
        n = 2
        while True:
            alt = collision_suffix(candidate, n)
            alt_sha = store_mod.friendly_name_target_sha(self.root, alt)
            if alt_sha is None and not (self.root / alt).exists():
                return alt
            if alt_sha == target_sha:
                return alt
            n += 1


def _looks_like_sha(s: str) -> bool:
    return len(s) == 64 and all(c in "0123456789abcdef" for c in s)


def _looks_like_short_sha(s: str) -> bool:
    return 4 <= len(s) <= 64 and all(c in "0123456789abcdef" for c in s)


def _kind_from_extension(path: Path, *, default: ObjectKind = "tac") -> ObjectKind:
    suffix = path.suffix.lower().lstrip(".")
    if suffix == "tac":
        return "tac"
    if suffix == "htac":
        return "htac"
    if suffix in ("smt2", "smt"):
        return "smt"
    return default


def _ext_for_kind(kind: ObjectKind) -> str:
    if kind == "tac" or kind == "tac-set":
        return "tac"
    if kind == "htac" or kind == "htac-set":
        return "htac"
    if kind == "smt" or kind == "smt-set":
        return "smt2"
    return "bin"


def _iso_now() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _rmtree(p: Path) -> None:
    """Remove a directory tree that may contain read-only object files.

    Object-store leaves are stored 0o444 (read-only) so editing them in
    place doesn't silently desync the sha. ``shutil.rmtree`` doesn't
    need write on the file itself (only on the parent directory) on
    POSIX, so this is mostly defensive — but we keep dir bits at
    0o755 throughout to avoid losing traverse on subdirectories.
    """
    import os
    import shutil

    if not (p.is_dir() and not p.is_symlink()):
        return
    for root, dirs, files in os.walk(p):
        for d in dirs:
            try:
                os.chmod(os.path.join(root, d), 0o755)
            except OSError:
                pass
        for f in files:
            try:
                os.chmod(os.path.join(root, f), 0o644)
            except OSError:
                pass
    shutil.rmtree(p)


def _dir_size_bytes(p: Path) -> int:
    total = 0
    for child in p.rglob("*"):
        if child.is_file() and not child.is_symlink():
            try:
                total += child.stat().st_size
            except OSError:
                pass
    return total
