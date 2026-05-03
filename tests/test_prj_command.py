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
