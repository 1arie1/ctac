"""Content hashing for project objects.

Files are hashed by sha256 of their bytes. Filesets (directories)
are hashed git-tree-style: sha256 over sorted ``<sha> <name>\n``
lines, where each member's ``<sha>`` is itself this same recursive
hash. The newline-separated list is encoded as UTF-8 bytes.
"""

from __future__ import annotations

import hashlib
from pathlib import Path


_CHUNK = 1 << 20  # 1 MiB read window


def sha256_file(path: Path) -> str:
    """Hex sha256 digest of a file's contents."""
    h = hashlib.sha256()
    with path.open("rb") as f:
        while True:
            chunk = f.read(_CHUNK)
            if not chunk:
                break
            h.update(chunk)
    return h.hexdigest()


def sha256_fileset(path: Path) -> str:
    """Recursive (git-tree-style) hex sha256 digest of a directory.

    Members are sorted by name. Each member contributes one line:
    ``<sha> <name>\\n``. Subdirectories recurse with the same scheme.
    Symlinks are not followed — they're hashed by the bytes of their
    target string (rare in practice for project objects).
    """
    if not path.is_dir():
        raise ValueError(f"sha256_fileset: not a directory: {path}")
    return _hash_dir(path)


def _hash_dir(path: Path) -> str:
    entries = sorted(path.iterdir(), key=lambda p: p.name)
    h = hashlib.sha256()
    for ent in entries:
        if ent.is_symlink():
            target = ent.readlink()
            sub = hashlib.sha256(str(target).encode("utf-8")).hexdigest()
        elif ent.is_dir():
            sub = _hash_dir(ent)
        else:
            sub = sha256_file(ent)
        h.update(f"{sub} {ent.name}\n".encode("utf-8"))
    return h.hexdigest()


def short_sha(sha: str, *, width: int = 8) -> str:
    """First ``width`` characters of a full sha. Default 8 = git's default."""
    if len(sha) < width:
        raise ValueError(f"sha shorter than requested short width {width}: {sha!r}")
    return sha[:width]
