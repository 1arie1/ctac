"""Content-addressed object store: ``.ctac/objects/<sha[:2]>/<sha[2:]>``.

Files are stored by their full sha256 in a two-char prefix layout
(matching git's loose-object scheme). Filesets are stored as
directories under the same path.

This module is intentionally low-level: it owns the file/dir layout
inside ``objects/`` but does not know anything about the manifest,
HEAD, or friendly-name symlinks. Higher-level orchestration is in
:mod:`ctac.project.core`.
"""

from __future__ import annotations

import os
import shutil
from pathlib import Path

from ctac.project.hashing import sha256_file, sha256_fileset


_PREFIX_LEN = 2


def _split(sha: str) -> tuple[str, str]:
    if len(sha) <= _PREFIX_LEN:
        raise ValueError(f"sha too short: {sha!r}")
    return sha[:_PREFIX_LEN], sha[_PREFIX_LEN:]


def object_path(dot_ctac: Path, sha: str) -> Path:
    pfx, rest = _split(sha)
    return dot_ctac / "objects" / pfx / rest


def has_object(dot_ctac: Path, sha: str) -> bool:
    p = object_path(dot_ctac, sha)
    return p.exists()


def store_file(dot_ctac: Path, src: Path) -> tuple[str, Path, bool]:
    """Hash and copy ``src`` into the object store.

    Returns ``(sha, stored_path, was_new)``. If an object with the
    same sha is already present, ``src`` is not copied and
    ``was_new`` is False. The store is read-only after a write —
    files are made non-writable to discourage in-place edits (the
    canonical bytes must match the sha at all times).
    """
    sha = sha256_file(src)
    target = object_path(dot_ctac, sha)
    if target.exists():
        return sha, target, False
    target.parent.mkdir(parents=True, exist_ok=True)
    tmp = target.with_suffix(target.suffix + ".tmp")
    shutil.copyfile(src, tmp)
    os.chmod(tmp, 0o444)
    tmp.replace(target)
    return sha, target, True


def store_fileset(dot_ctac: Path, src_dir: Path) -> tuple[str, Path, bool]:
    """Hash and copy a directory tree into the object store.

    Returns ``(sha, stored_path, was_new)``. Existing objects are
    preserved unmodified.
    """
    if not src_dir.is_dir():
        raise ValueError(f"store_fileset: not a directory: {src_dir}")
    sha = sha256_fileset(src_dir)
    target = object_path(dot_ctac, sha)
    if target.exists():
        return sha, target, False
    target.parent.mkdir(parents=True, exist_ok=True)
    tmp = target.with_name(target.name + ".tmp")
    shutil.copytree(src_dir, tmp)
    tmp.rename(target)
    return sha, target, True


def relink_friendly_name(
    project_root: Path, dot_ctac: Path, name: str, sha: str
) -> Path:
    """Create / refresh a project-root symlink ``<root>/<name>`` -> the object.

    If ``<root>/<name>`` already exists and points at the right
    object (same target path), it's left alone. If it exists and
    points elsewhere, it's replaced atomically.
    """
    if "/" in name or "\\" in name:
        raise ValueError(f"friendly name must be a basename: {name!r}")
    target = object_path(dot_ctac, sha)
    if not target.exists():
        raise FileNotFoundError(f"object not in store: {sha}")
    link = project_root / name
    rel_target = os.path.relpath(target, project_root)
    if link.is_symlink():
        try:
            current = os.readlink(link)
        except OSError:
            current = None
        if current == rel_target:
            return link
        link.unlink()
    elif link.exists():
        raise FileExistsError(
            f"friendly-name path exists and is not a symlink: {link}"
        )
    link.symlink_to(rel_target)
    return link


def friendly_name_target_sha(project_root: Path, name: str) -> str | None:
    """Read the symlink ``<root>/<name>`` and return its target sha, if any.

    Returns None if the path doesn't exist or isn't a symlink into
    ``objects/<pfx>/<rest>``.
    """
    link = project_root / name
    if not link.is_symlink():
        return None
    try:
        target = os.readlink(link)
    except OSError:
        return None
    parts = Path(target).parts
    # Expect ``... /.ctac/objects/<pfx>/<rest>``.
    try:
        idx = parts.index("objects")
    except ValueError:
        return None
    if idx + 2 >= len(parts):
        return None
    pfx, rest = parts[idx + 1], parts[idx + 2]
    if len(pfx) != _PREFIX_LEN:
        return None
    return pfx + rest
