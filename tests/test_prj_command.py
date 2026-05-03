from __future__ import annotations

from pathlib import Path

from typer.testing import CliRunner

from ctac.project import Project
from ctac.tool.main import app


def _write_tac(p: Path, content: str = "hello tac\n") -> Path:
    p.write_text(content, encoding="utf-8")
    return p


def test_prj_init_smoke(tmp_path: Path) -> None:
    base = _write_tac(tmp_path / "in.tac")
    prj_dir = tmp_path / "mytac"
    runner = CliRunner()
    res = runner.invoke(
        app, ["prj", "init", str(base), "-o", str(prj_dir), "--plain"]
    )
    assert res.exit_code == 0, res.stdout
    assert "head:" in res.stdout
    assert "label: base" in res.stdout
    # Project was actually created.
    assert Project.is_project(prj_dir)


def test_prj_init_force(tmp_path: Path) -> None:
    base = _write_tac(tmp_path / "in.tac")
    prj_dir = tmp_path / "mytac"
    runner = CliRunner()
    runner.invoke(app, ["prj", "init", str(base), "-o", str(prj_dir), "--plain"])
    # Second init without --force should fail.
    res = runner.invoke(
        app, ["prj", "init", str(base), "-o", str(prj_dir), "--plain"]
    )
    assert res.exit_code == 1
    assert "project error" in res.stdout
    # With --force it succeeds.
    res2 = runner.invoke(
        app,
        ["prj", "init", str(base), "-o", str(prj_dir), "--plain", "--force"],
    )
    assert res2.exit_code == 0


def test_prj_init_custom_label(tmp_path: Path) -> None:
    base = _write_tac(tmp_path / "in.tac")
    prj_dir = tmp_path / "mytac"
    runner = CliRunner()
    res = runner.invoke(
        app,
        [
            "prj",
            "init",
            str(base),
            "-o",
            str(prj_dir),
            "--label",
            "v1",
            "--plain",
        ],
    )
    assert res.exit_code == 0
    assert "label: v1" in res.stdout
    prj = Project.open(prj_dir)
    assert "v1" in prj.manifest.labels


def test_prj_list_smoke(tmp_path: Path) -> None:
    base = _write_tac(tmp_path / "in.tac")
    prj_dir = tmp_path / "mytac"
    runner = CliRunner()
    runner.invoke(app, ["prj", "init", str(base), "-o", str(prj_dir), "--plain"])
    res = runner.invoke(app, ["prj", "list", str(prj_dir), "--plain"])
    assert res.exit_code == 0
    # HEAD marker, the friendly name, and the label all appear.
    assert "HEAD" in res.stdout
    assert "in.tac" in res.stdout
    assert "labels:" in res.stdout
    assert "base ->" in res.stdout


def test_prj_info_recursive_two_objects(tmp_path: Path) -> None:
    base = _write_tac(tmp_path / "in.tac", "first\n")
    prj_dir = tmp_path / "mytac"
    # Create the project then hand-add a derived object via the library.
    prj = Project.init(prj_dir, base)
    derived = tmp_path / "derived.tac"
    derived.write_text("second\n", encoding="utf-8")
    prj.add(
        derived,
        kind="tac",
        parents=[prj.head_sha],
        command="rw",
        args=[],
        advance_head=True,
    )

    runner = CliRunner()
    res = runner.invoke(
        app, ["prj", "info", str(prj_dir), "base", "--recursive", "--plain"]
    )
    assert res.exit_code == 0
    # One section per ancestor — base only here (it has no parents).
    assert res.stdout.count("sha:") == 1

    # From the new HEAD, recursive walk hits both objects.
    res2 = runner.invoke(
        app,
        ["prj", "info", str(prj_dir), prj.head_sha, "--recursive", "--plain"],
    )
    assert res2.exit_code == 0
    assert res2.stdout.count("sha:") == 2


def test_prj_info_unknown_ref(tmp_path: Path) -> None:
    base = _write_tac(tmp_path / "in.tac")
    prj_dir = tmp_path / "mytac"
    runner = CliRunner()
    runner.invoke(app, ["prj", "init", str(base), "-o", str(prj_dir), "--plain"])
    res = runner.invoke(
        app, ["prj", "info", str(prj_dir), "doesnotexist", "--plain"]
    )
    assert res.exit_code == 1
    assert "resolve error" in res.stdout


def test_prj_set_head_label(tmp_path: Path) -> None:
    base = _write_tac(tmp_path / "in.tac", "first\n")
    prj_dir = tmp_path / "mytac"
    runner = CliRunner()
    runner.invoke(app, ["prj", "init", str(base), "-o", str(prj_dir), "--plain"])
    # Add a second object via library, advance HEAD off it, then set-head back.
    prj = Project.open(prj_dir)
    other = tmp_path / "other.tac"
    other.write_text("second\n", encoding="utf-8")
    prj.add(
        other, kind="tac", parents=[prj.head_sha], command="rw", args=[], advance_head=True
    )
    res = runner.invoke(app, ["prj", "set-head", str(prj_dir), "base", "--plain"])
    assert res.exit_code == 0, res.stdout
    prj2 = Project.open(prj_dir)
    assert "in.tac" in prj2.head.names


def test_prj_set_head_focus_member(tmp_path: Path) -> None:
    """End-to-end: ingest a fileset via the library, then `prj set-head <set>:<member>`."""
    base = _write_tac(tmp_path / "in.tac")
    prj_dir = tmp_path / "mytac"
    runner = CliRunner()
    runner.invoke(app, ["prj", "init", str(base), "-o", str(prj_dir), "--plain"])
    prj = Project.open(prj_dir)
    # Build a fileset directly via the library (CLI ingestion comes
    # later in this phase via `pin --split` / `ua --split`).
    src = tmp_path / "fset"
    src.mkdir()
    (src / "case_1.tac").write_text("c1\n", encoding="utf-8")
    (src / "case_2.tac").write_text("c2\n", encoding="utf-8")
    prj.add(
        src,
        kind="tac-set",
        parents=[prj.head_sha],
        command="ua-split",
        args=[],
        suggested_name="in.split",
        advance_head=True,
    )
    res = runner.invoke(
        app,
        ["prj", "set-head", str(prj_dir), "in.split:case_1.tac", "--plain"],
    )
    assert res.exit_code == 0, res.stdout
    prj2 = Project.open(prj_dir)
    assert prj2.head.kind == "tac"
    assert "case_1.tac" in prj2.head.names


def test_prj_set_head_member_not_found(tmp_path: Path) -> None:
    base = _write_tac(tmp_path / "in.tac")
    prj_dir = tmp_path / "mytac"
    runner = CliRunner()
    runner.invoke(app, ["prj", "init", str(base), "-o", str(prj_dir), "--plain"])
    prj = Project.open(prj_dir)
    src = tmp_path / "fset"
    src.mkdir()
    (src / "only.tac").write_text("x\n", encoding="utf-8")
    prj.add(
        src,
        kind="tac-set",
        parents=[prj.head_sha],
        command="ua-split",
        args=[],
        suggested_name="in.split",
        advance_head=True,
    )
    res = runner.invoke(
        app,
        ["prj", "set-head", str(prj_dir), "in.split:nope.tac", "--plain"],
    )
    assert res.exit_code == 1
    assert "set-head error" in res.stdout


def test_prj_list_fileset_lists_members(tmp_path: Path) -> None:
    """`prj list <DIR> <fileset-ref>` shows the fileset's metadata
    plus its directory members and a hint to use `prj set-head`."""
    base = _write_tac(tmp_path / "in.tac")
    prj_dir = tmp_path / "mytac"
    runner = CliRunner()
    runner.invoke(app, ["prj", "init", str(base), "-o", str(prj_dir), "--plain"])
    prj = Project.open(prj_dir)
    src = tmp_path / "fset"
    src.mkdir()
    (src / "case_1.tac").write_text("first\n", encoding="utf-8")
    (src / "case_2.tac").write_text("second\n", encoding="utf-8")
    prj.add(
        src,
        kind="tac-set",
        parents=[prj.head_sha],
        command="ua-split",
        args=[],
        suggested_name="in.split",
        advance_head=True,
    )
    res = runner.invoke(app, ["prj", "list", str(prj_dir), "in.split", "--plain"])
    assert res.exit_code == 0, res.stdout
    assert "members (2):" in res.stdout
    assert "case_1.tac" in res.stdout
    assert "case_2.tac" in res.stdout
    assert "set-head" in res.stdout


def test_prj_label(tmp_path: Path) -> None:
    base = _write_tac(tmp_path / "in.tac")
    prj_dir = tmp_path / "mytac"
    runner = CliRunner()
    runner.invoke(app, ["prj", "init", str(base), "-o", str(prj_dir), "--plain"])
    res = runner.invoke(app, ["prj", "label", str(prj_dir), "base", "v1", "--plain"])
    assert res.exit_code == 0, res.stdout
    assert "label: v1" in res.stdout
    prj = Project.open(prj_dir)
    assert "v1" in prj.manifest.labels
    # The new label resolves the same object as `base`.
    assert prj.resolve("v1") == prj.resolve("base")


def test_prj_label_unknown_obj(tmp_path: Path) -> None:
    base = _write_tac(tmp_path / "in.tac")
    prj_dir = tmp_path / "mytac"
    runner = CliRunner()
    runner.invoke(app, ["prj", "init", str(base), "-o", str(prj_dir), "--plain"])
    res = runner.invoke(
        app, ["prj", "label", str(prj_dir), "nope", "v1", "--plain"]
    )
    assert res.exit_code == 1
    assert "label error" in res.stdout


def test_prj_export_path_default_head(tmp_path: Path) -> None:
    base = _write_tac(tmp_path / "in.tac")
    prj_dir = tmp_path / "mytac"
    runner = CliRunner()
    runner.invoke(app, ["prj", "init", str(base), "-o", str(prj_dir), "--plain"])
    res = runner.invoke(app, ["prj", "export-path", str(prj_dir)])
    assert res.exit_code == 0, res.stdout
    out = res.stdout.strip()
    # One line, undecorated, points at the resolved object content.
    assert "\n" not in out
    assert Path(out).is_file()
    prj = Project.open(prj_dir)
    assert Path(out) == prj.head_path().resolve()


def test_prj_export_path_named_ref(tmp_path: Path) -> None:
    base = _write_tac(tmp_path / "in.tac")
    prj_dir = tmp_path / "mytac"
    runner = CliRunner()
    runner.invoke(app, ["prj", "init", str(base), "-o", str(prj_dir), "--plain"])
    res = runner.invoke(app, ["prj", "export-path", str(prj_dir), "base"])
    assert res.exit_code == 0
    prj = Project.open(prj_dir)
    assert Path(res.stdout.strip()) == prj.head_path().resolve()


def test_prj_export_path_unknown(tmp_path: Path) -> None:
    base = _write_tac(tmp_path / "in.tac")
    prj_dir = tmp_path / "mytac"
    runner = CliRunner()
    runner.invoke(app, ["prj", "init", str(base), "-o", str(prj_dir), "--plain"])
    res = runner.invoke(app, ["prj", "export-path", str(prj_dir), "nope"])
    assert res.exit_code == 1


def test_prj_archive_then_clone(tmp_path: Path) -> None:
    """archive + clone round-trip: archive produces a tar.gz, clone
    extracts and rebuilds friendly symlinks."""
    base = _write_tac(tmp_path / "in.tac")
    prj_dir = tmp_path / "src"
    runner = CliRunner()
    runner.invoke(app, ["prj", "init", str(base), "-o", str(prj_dir), "--plain"])

    arc = tmp_path / "snap.tar.gz"
    res = runner.invoke(
        app, ["prj", "archive", str(prj_dir), "-o", str(arc), "--plain"]
    )
    assert res.exit_code == 0, res.stdout
    assert arc.is_file()
    assert arc.stat().st_size > 0

    dst = tmp_path / "restored"
    res = runner.invoke(
        app, ["prj", "clone", str(arc), "-o", str(dst), "--plain"]
    )
    assert res.exit_code == 0, res.stdout
    assert Project.is_project(dst)
    # Restored project has the same HEAD sha and a re-created friendly symlink.
    src_prj = Project.open(prj_dir)
    dst_prj = Project.open(dst)
    assert dst_prj.head_sha == src_prj.head_sha
    link = dst / "in.tac"
    assert link.is_symlink()


def test_prj_clone_dir_to_dir(tmp_path: Path) -> None:
    base = _write_tac(tmp_path / "in.tac")
    src = tmp_path / "src"
    runner = CliRunner()
    runner.invoke(app, ["prj", "init", str(base), "-o", str(src), "--plain"])
    dst = tmp_path / "dst"
    res = runner.invoke(
        app, ["prj", "clone", str(src), "-o", str(dst), "--plain"]
    )
    assert res.exit_code == 0, res.stdout
    assert Project.is_project(dst)
    assert (dst / "in.tac").is_symlink()


def test_prj_clone_existing_destination(tmp_path: Path) -> None:
    base = _write_tac(tmp_path / "in.tac")
    src = tmp_path / "src"
    runner = CliRunner()
    runner.invoke(app, ["prj", "init", str(base), "-o", str(src), "--plain"])
    dst = tmp_path / "dst"
    runner.invoke(app, ["prj", "init", str(base), "-o", str(dst), "--plain"])
    # Without --force, clone refuses.
    res = runner.invoke(
        app, ["prj", "clone", str(src), "-o", str(dst), "--plain"]
    )
    assert res.exit_code == 1
    assert "clone error" in res.stdout
    # With --force, clone succeeds.
    res2 = runner.invoke(
        app, ["prj", "clone", str(src), "-o", str(dst), "--plain", "--force"]
    )
    assert res2.exit_code == 0


def test_prj_archive_uncompressed(tmp_path: Path) -> None:
    """`-o foo.tar` (no .gz) produces an uncompressed tarball."""
    base = _write_tac(tmp_path / "in.tac")
    src = tmp_path / "src"
    runner = CliRunner()
    runner.invoke(app, ["prj", "init", str(base), "-o", str(src), "--plain"])
    arc = tmp_path / "snap.tar"
    res = runner.invoke(
        app, ["prj", "archive", str(src), "-o", str(arc), "--plain"]
    )
    assert res.exit_code == 0, res.stdout
    # Plain tar starts with a USTAR header at offset 257; we don't need
    # to assert that exactly, but the file should at least be larger
    # than the gzipped equivalent (uncompressed for one tiny object is
    # tar's 512-byte block alignment).
    assert arc.is_file()
    assert arc.stat().st_size >= 512
    # And it's not gzipped.
    assert arc.read_bytes()[:2] != b"\x1f\x8b"


def test_prj_clone_preserves_provenance(tmp_path: Path) -> None:
    """A clone should carry over manifest, labels, and the object graph."""
    base = _write_tac(tmp_path / "in.tac")
    src_dir = tmp_path / "src"
    runner = CliRunner()
    runner.invoke(app, ["prj", "init", str(base), "-o", str(src_dir), "--plain"])
    src_prj = Project.open(src_dir)
    other = tmp_path / "other.tac"
    other.write_text("xyz\n", encoding="utf-8")
    src_prj.add(
        other, kind="tac", parents=[src_prj.head_sha], command="rw", args=[],
        advance_head=True,
    )
    src_prj.set_label(src_prj.head_sha, "tip")

    dst = tmp_path / "dst"
    res = runner.invoke(
        app, ["prj", "clone", str(src_dir), "-o", str(dst), "--plain"]
    )
    assert res.exit_code == 0, res.stdout
    dst_prj = Project.open(dst)
    assert len(dst_prj.manifest.objects) == len(src_prj.manifest.objects)
    assert dst_prj.manifest.labels == src_prj.manifest.labels
    assert dst_prj.head_sha == src_prj.head_sha


def test_prj_list_one_object(tmp_path: Path) -> None:
    """`prj list <DIR> <OBJ_ID>` falls through to per-object info."""
    base = _write_tac(tmp_path / "in.tac")
    prj_dir = tmp_path / "mytac"
    runner = CliRunner()
    runner.invoke(app, ["prj", "init", str(base), "-o", str(prj_dir), "--plain"])
    res = runner.invoke(
        app, ["prj", "list", str(prj_dir), "base", "--plain"]
    )
    assert res.exit_code == 0
    assert "kind: tac" in res.stdout
    assert "command: init" in res.stdout
