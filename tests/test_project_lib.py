from __future__ import annotations

import json
import os
from pathlib import Path

import pytest

from ctac.project import DOT_CTAC, Project, ProjectError
from ctac.project.hashing import sha256_file, short_sha
from ctac.project.log import read_log
from ctac.project.manifest import read_manifest
from ctac.project.naming import auto_name, collision_suffix
from ctac.project.refs import is_valid_label, read_head, read_ref


def _write_tac(p: Path, content: str = "hello tac\n") -> Path:
    p.write_text(content, encoding="utf-8")
    return p


# ----------------------------------------------------------- naming


def test_auto_name_simple() -> None:
    assert auto_name("base.tac", "rw", "tac") == "base.rw.tac"
    assert auto_name("base.rw.tac", "ua", "tac") == "base.rw.ua.tac"
    assert auto_name("base.rw.ua.tac", "smt", "smt2") == "base.rw.ua.smt2"


def test_auto_name_unknown_extension_kept() -> None:
    # Nothing in _KNOWN_EXTS matches → stem stays as-is.
    assert auto_name("base.bin", "rw", "tac") == "base.bin.rw.tac"


def test_auto_name_rejects_path_components() -> None:
    with pytest.raises(ValueError):
        auto_name("dir/base.tac", "rw", "tac")
    with pytest.raises(ValueError):
        auto_name("base.tac", "", "tac")
    with pytest.raises(ValueError):
        auto_name("base.tac", "rw", "")


def test_collision_suffix() -> None:
    assert collision_suffix("base.rw.tac", 2) == "base.rw.2.tac"
    assert collision_suffix("base", 3) == "base.3"
    with pytest.raises(ValueError):
        collision_suffix("base", 1)


# ------------------------------------------------------------ refs


def test_is_valid_label() -> None:
    assert is_valid_label("base")
    assert is_valid_label("v1.2")
    assert is_valid_label("review/p1")
    assert not is_valid_label("")
    assert not is_valid_label("/abs")
    assert not is_valid_label("bad space")


# ----------------------------------------------------- init / open


def test_init_creates_layout(tmp_path: Path) -> None:
    base = _write_tac(tmp_path / "in.tac")
    prj_dir = tmp_path / "mytac"
    prj = Project.init(prj_dir, base)

    dot = prj_dir / DOT_CTAC
    assert dot.is_dir()
    assert (dot / "HEAD").is_file()
    assert (dot / "refs" / "base").is_file()
    assert (dot / "manifest.json").is_file()
    assert (dot / "log.jsonl").is_file()
    objs_dir = dot / "objects"
    assert objs_dir.is_dir()
    # Exactly one stored object (the base) — the prefix dir + leaf.
    leaves = [p for p in objs_dir.rglob("*") if p.is_file()]
    assert len(leaves) == 1

    # HEAD sha matches the file's sha256.
    expected_sha = sha256_file(base)
    assert read_head(dot) == expected_sha
    assert prj.head_sha == expected_sha
    assert read_ref(dot, "base") == expected_sha

    # Friendly symlink in the project root points at the object.
    link = prj_dir / "in.tac"
    assert link.is_symlink()
    target = os.readlink(link)
    assert "objects" in target
    assert target.endswith(expected_sha[2:])


def test_init_idempotent_force(tmp_path: Path) -> None:
    base = _write_tac(tmp_path / "in.tac")
    prj_dir = tmp_path / "mytac"
    Project.init(prj_dir, base)
    with pytest.raises(ProjectError):
        Project.init(prj_dir, base)
    # With force=True, init succeeds.
    prj2 = Project.init(prj_dir, base, force=True)
    assert prj2.head_sha == sha256_file(base)


def test_open_roundtrips(tmp_path: Path) -> None:
    base = _write_tac(tmp_path / "in.tac")
    prj_dir = tmp_path / "mytac"
    prj1 = Project.init(prj_dir, base)
    prj2 = Project.open(prj_dir)
    assert prj1.head_sha == prj2.head_sha
    assert prj1.head.kind == prj2.head.kind
    assert prj2.head.names == ("in.tac",)


def test_is_project(tmp_path: Path) -> None:
    base = _write_tac(tmp_path / "in.tac")
    prj_dir = tmp_path / "mytac"
    Project.init(prj_dir, base)
    assert Project.is_project(prj_dir)
    assert not Project.is_project(tmp_path)
    assert not Project.is_project(prj_dir / DOT_CTAC)


def test_open_missing_raises(tmp_path: Path) -> None:
    with pytest.raises(ProjectError):
        Project.open(tmp_path)


def test_init_rejects_missing_base(tmp_path: Path) -> None:
    prj_dir = tmp_path / "mytac"
    with pytest.raises(ProjectError):
        Project.init(prj_dir, tmp_path / "nope.tac")


# -------------------------------------------------------- resolve


def test_resolve_by_full_sha(tmp_path: Path) -> None:
    base = _write_tac(tmp_path / "in.tac")
    prj = Project.init(tmp_path / "mytac", base)
    sha = prj.head_sha
    assert prj.resolve(sha) == sha


def test_resolve_by_short_sha(tmp_path: Path) -> None:
    base = _write_tac(tmp_path / "in.tac")
    prj = Project.init(tmp_path / "mytac", base)
    sha = prj.head_sha
    assert prj.resolve(short_sha(sha, width=8)) == sha
    # 4-char prefix is the minimum.
    assert prj.resolve(sha[:4]) == sha


def test_resolve_by_label(tmp_path: Path) -> None:
    base = _write_tac(tmp_path / "in.tac")
    prj = Project.init(tmp_path / "mytac", base)
    assert prj.resolve("base") == prj.head_sha


def test_resolve_by_friendly_name(tmp_path: Path) -> None:
    base = _write_tac(tmp_path / "in.tac")
    prj = Project.init(tmp_path / "mytac", base)
    assert prj.resolve("in.tac") == prj.head_sha


def test_resolve_unknown_raises(tmp_path: Path) -> None:
    base = _write_tac(tmp_path / "in.tac")
    prj = Project.init(tmp_path / "mytac", base)
    with pytest.raises(ProjectError):
        prj.resolve("nope")


# ----------------------------------------------------- add idempotent


def test_add_same_content_is_idempotent(tmp_path: Path) -> None:
    base = _write_tac(tmp_path / "in.tac")
    prj = Project.init(tmp_path / "mytac", base)
    sha0 = prj.head_sha
    # Re-add the exact same bytes — should not create a new object.
    info2 = prj.add(
        base,
        kind="tac",
        parents=[],
        command="init",
        args=[],
        suggested_name="in.tac",
    )
    assert info2.sha == sha0
    leaves = [p for p in (prj.dot_ctac / "objects").rglob("*") if p.is_file()]
    assert len(leaves) == 1


def test_add_same_content_new_alias(tmp_path: Path) -> None:
    base = _write_tac(tmp_path / "in.tac")
    prj = Project.init(tmp_path / "mytac", base)
    sha0 = prj.head_sha
    info2 = prj.add(
        base,
        kind="tac",
        parents=[],
        command="init",
        args=[],
        suggested_name="aliased.tac",
    )
    assert info2.sha == sha0
    assert "in.tac" in info2.names
    assert "aliased.tac" in info2.names
    assert (prj.root / "aliased.tac").is_symlink()


def test_add_collision_suffixes(tmp_path: Path) -> None:
    """Adding different content with a name that's already taken should
    suffix automatically (foo.tac -> foo.2.tac)."""
    base = _write_tac(tmp_path / "in.tac", "first\n")
    prj = Project.init(tmp_path / "mytac", base)
    other = tmp_path / "other.tac"
    other.write_text("second\n", encoding="utf-8")
    info2 = prj.add(
        other,
        kind="tac",
        parents=[prj.head_sha],
        command="rw",
        args=[],
        suggested_name="in.tac",  # already taken
    )
    assert info2.sha != prj.head_sha
    assert info2.names == ("in.2.tac",)
    assert (prj.root / "in.2.tac").is_symlink()


# --------------------------------------------------------- log + manifest


def test_log_records_init_and_add(tmp_path: Path) -> None:
    base = _write_tac(tmp_path / "in.tac")
    prj = Project.init(tmp_path / "mytac", base)
    other = tmp_path / "other.tac"
    other.write_text("xyz\n", encoding="utf-8")
    prj.add(
        other,
        kind="tac",
        parents=[prj.head_sha],
        command="rw",
        args=["--report"],
        advance_head=True,
    )
    entries = read_log(prj.dot_ctac)
    assert len(entries) >= 2
    cmds = [e.command for e in entries]
    assert "init" in cmds
    assert "rw" in cmds
    rw = next(e for e in entries if e.command == "rw")
    assert rw.advance_head is True
    assert rw.parents == (prj.manifest.objects[prj.head_sha].parents[0],)


def test_manifest_roundtrips_through_disk(tmp_path: Path) -> None:
    base = _write_tac(tmp_path / "in.tac")
    prj = Project.init(tmp_path / "mytac", base)
    m_disk = read_manifest(prj.dot_ctac)
    assert m_disk.head == prj.head_sha
    assert prj.head_sha in m_disk.objects


def test_manifest_json_stable(tmp_path: Path) -> None:
    """Two inits with the same content land on the same sha and the
    manifest is sorted-keyed (deterministic for diffs)."""
    base = _write_tac(tmp_path / "in.tac")
    Project.init(tmp_path / "a", base)
    Project.init(tmp_path / "b", base)
    a = json.loads((tmp_path / "a" / DOT_CTAC / "manifest.json").read_text())
    b = json.loads((tmp_path / "b" / DOT_CTAC / "manifest.json").read_text())
    # Same head sha (timestamps differ — strip those for comparison).
    a_sha = a["head"]
    b_sha = b["head"]
    assert a_sha == b_sha


# --------------------------------------------------------- set_head + label


def test_set_head_advances(tmp_path: Path) -> None:
    base = _write_tac(tmp_path / "in.tac", "first\n")
    prj = Project.init(tmp_path / "mytac", base)
    sha0 = prj.head_sha
    other = tmp_path / "other.tac"
    other.write_text("second\n", encoding="utf-8")
    info2 = prj.add(
        other, kind="tac", parents=[sha0], command="rw", args=[], advance_head=True
    )
    assert prj.head_sha == info2.sha
    prj.set_head("base")  # via label — back to base
    assert prj.head_sha == sha0


def test_set_label_writes_ref(tmp_path: Path) -> None:
    base = _write_tac(tmp_path / "in.tac")
    prj = Project.init(tmp_path / "mytac", base)
    prj.set_label(prj.head_sha, "v1")
    assert read_ref(prj.dot_ctac, "v1") == prj.head_sha
    assert prj.resolve("v1") == prj.head_sha
