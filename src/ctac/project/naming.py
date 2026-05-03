"""Auto-naming of project files.

The friendly-name in the project root is built mechanically from the
parent's name, the command, and the desired extension:

    auto_name("base.tac",       "rw",  "tac")  -> "base.rw.tac"
    auto_name("base.rw.tac",    "ua",  "tac")  -> "base.rw.ua.tac"
    auto_name("base.rw.ua.tac", "smt", "smt2") -> "base.rw.ua.smt2"

Lexical only — no parsing of the dotted history. The trailing
extension on the parent is stripped if present; otherwise the parent
name is treated as the stem. Collision suffixing is applied by the
caller (project core), since it depends on what's already on disk.
"""

from __future__ import annotations


def auto_name(parent_name: str, command: str, ext: str) -> str:
    """Derive a friendly name for ``command``'s output from a parent name.

    ``parent_name`` is a basename (e.g. ``base.rw.tac``); ``ext`` is the
    new extension without a leading dot. Two cases:

    - **Same extension** (e.g. parent ``.tac``, new ``.tac``): insert
      the command name into the chain → ``base.rw.tac`` + ``ua`` →
      ``base.rw.ua.tac``.
    - **Different extension** (e.g. parent ``.tac``, new ``.smt2``):
      swap the extension on the parent's stem → ``base.rw.ua.tac``
      + ``smt`` → ``base.rw.ua.smt2``. The new extension is itself
      command-distinctive, so the command name doesn't need to
      appear in the filename.

    If the parent has no recognized extension, the new command + ext
    are simply appended.
    """
    if "/" in parent_name or "\\" in parent_name:
        raise ValueError(f"auto_name expects a basename, got: {parent_name!r}")
    if not command:
        raise ValueError("auto_name: command must be non-empty")
    if not ext:
        raise ValueError("auto_name: ext must be non-empty")
    parent_ext = _detect_known_ext(parent_name)
    if parent_ext is None:
        return f"{parent_name}.{command}.{ext}"
    stem = parent_name[: -len(parent_ext) - 1]
    if parent_ext == ext:
        return f"{stem}.{command}.{ext}"
    return f"{stem}.{ext}"


def auto_set_name(parent_name: str, command: str) -> str:
    """Friendly name for a fileset object.

    Filesets are directories of TAC/htac/smt files; the directory
    itself doesn't carry a ``.tac``-style extension. The convention
    is ``<parent-stem>.<command>.split`` — the trailing ``.split``
    marks the result as a fileset regardless of which command
    produced it (today: ``pin --split`` and ``ua --strategy split``).
    """
    if "/" in parent_name or "\\" in parent_name:
        raise ValueError(f"auto_set_name expects a basename, got: {parent_name!r}")
    if not command:
        raise ValueError("auto_set_name: command must be non-empty")
    parent_ext = _detect_known_ext(parent_name)
    if parent_ext is None:
        stem = parent_name
        # If parent is itself a `.split` fileset, drop that suffix so
        # we don't accumulate `.split.cmd.split`.
        if stem.endswith(".split"):
            stem = stem[: -len(".split")]
    else:
        stem = parent_name[: -len(parent_ext) - 1]
    return f"{stem}.{command}.split"


def collision_suffix(name: str, n: int) -> str:
    """Insert ``.<n>`` before the extension: ``foo.tac`` -> ``foo.2.tac``.

    When ``name`` looks like a fileset (ends in ``.split``), the suffix
    is appended *after* ``split`` so the marker stays at the tail:
    ``foo.split`` -> ``foo.split.2`` (not ``foo.2.split``).
    """
    if n < 2:
        raise ValueError("collision_suffix: n must be >= 2")
    if name.endswith(".split"):
        return f"{name}.{n}"
    if "." not in name:
        return f"{name}.{n}"
    stem, _, ext = name.rpartition(".")
    return f"{stem}.{n}.{ext}"


_KNOWN_EXTS = (
    "tac",
    "htac",
    "smt2",
    "smt",
)


def _detect_known_ext(name: str) -> str | None:
    """Return the known extension at the end of ``name`` (no leading dot), or None."""
    for ext in _KNOWN_EXTS:
        if name.endswith(f".{ext}"):
            return ext
    return None
