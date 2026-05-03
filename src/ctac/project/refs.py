"""HEAD and ``refs/<label>`` read/write.

A ref file is a single line containing one sha. ``HEAD`` may also
hold ``ref: <label>`` to indirect through ``refs/<label>``. Phase 1
only writes raw shas (the ``ref:`` form is a phase 4 hook).
"""

from __future__ import annotations

import re
from pathlib import Path


_LABEL_RE = re.compile(r"^[A-Za-z0-9_][A-Za-z0-9_./-]*$")


def is_valid_label(label: str) -> bool:
    return bool(_LABEL_RE.match(label))


def _atomic_write_line(target: Path, line: str) -> None:
    target.parent.mkdir(parents=True, exist_ok=True)
    tmp = target.with_suffix(target.suffix + ".tmp")
    tmp.write_text(line + "\n", encoding="utf-8")
    tmp.replace(target)


def write_head(dot_ctac: Path, sha: str) -> None:
    _atomic_write_line(dot_ctac / "HEAD", sha)


def read_head(dot_ctac: Path) -> str:
    """Return the sha HEAD points at, resolving one level of ``ref:``."""
    head = dot_ctac / "HEAD"
    if not head.is_file():
        raise FileNotFoundError(f"HEAD not found: {head}")
    text = head.read_text(encoding="utf-8").strip()
    if text.startswith("ref:"):
        label = text[len("ref:"):].strip()
        return read_ref(dot_ctac, label)
    return text


def write_ref(dot_ctac: Path, label: str, sha: str) -> None:
    if not is_valid_label(label):
        raise ValueError(f"invalid ref label: {label!r}")
    _atomic_write_line(dot_ctac / "refs" / label, sha)


def read_ref(dot_ctac: Path, label: str) -> str:
    if not is_valid_label(label):
        raise ValueError(f"invalid ref label: {label!r}")
    p = dot_ctac / "refs" / label
    if not p.is_file():
        raise FileNotFoundError(f"ref not found: {label}")
    return p.read_text(encoding="utf-8").strip()


def list_refs(dot_ctac: Path) -> dict[str, str]:
    refs_dir = dot_ctac / "refs"
    if not refs_dir.is_dir():
        return {}
    out: dict[str, str] = {}
    for p in sorted(refs_dir.rglob("*")):
        if not p.is_file():
            continue
        rel = p.relative_to(refs_dir).as_posix()
        out[rel] = p.read_text(encoding="utf-8").strip()
    return out


def remove_ref(dot_ctac: Path, label: str) -> None:
    if not is_valid_label(label):
        raise ValueError(f"invalid ref label: {label!r}")
    p = dot_ctac / "refs" / label
    if p.is_file():
        p.unlink()
