"""Integration tests for project-aware existing TAC commands (phase 2).

These exercise the contract that a project directory is a drop-in
replacement for a TAC path on the existing commands' positional
argument: HEAD is read for input, and outputs are ingested into the
project automatically when ``-o`` is omitted.
"""

from __future__ import annotations

from pathlib import Path

from typer.testing import CliRunner

from ctac.project import Project
from ctac.tool.main import app


# Single-assert TAC that survives `rw` (the simplification pipeline)
# essentially unchanged but still triggers a real round-trip.
TAC_SIMPLE = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tb:bool
}
Program {
\tBlock entry Succ [ok, bad] {
\t\tAssignExpCmd b true
\t\tJumpiCmd ok bad b
\t}
\tBlock ok Succ [] {
\t\tAssertCmd b "must hold"
\t}
\tBlock bad Succ [] {
\t\tAssumeExpCmd false
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""


def _init_project(tmp_path: Path, tac_text: str = TAC_SIMPLE) -> tuple[Path, Project]:
    base = tmp_path / "in.tac"
    base.write_text(tac_text, encoding="utf-8")
    prj_dir = tmp_path / "mytac"
    runner = CliRunner()
    res = runner.invoke(
        app, ["prj", "init", str(base), "-o", str(prj_dir), "--plain"]
    )
    assert res.exit_code == 0, res.stdout
    return prj_dir, Project.open(prj_dir)


def test_rw_advances_head(tmp_path: Path) -> None:
    prj_dir, prj0 = _init_project(tmp_path)
    head0 = prj0.head_sha
    runner = CliRunner()
    res = runner.invoke(app, ["rw", str(prj_dir), "--plain"])
    assert res.exit_code == 0, res.stdout
    prj1 = Project.open(prj_dir)
    # The rw output replaces HEAD (it might be the same sha if rw is a
    # no-op on this input, but the friendly name `in.rw.tac` should
    # exist regardless).
    new_link = prj_dir / "in.rw.tac"
    assert new_link.is_symlink(), f"expected friendly symlink in.rw.tac, got {sorted(p.name for p in prj_dir.iterdir())}"
    # If the simplifier actually changed something the head moved.
    if prj1.head_sha != head0:
        assert "in.rw.tac" in prj1.head.names


def test_rw_explicit_output_does_not_advance_head(tmp_path: Path) -> None:
    prj_dir, prj0 = _init_project(tmp_path)
    head0 = prj0.head_sha
    out_path = tmp_path / "explicit.tac"
    runner = CliRunner()
    res = runner.invoke(
        app, ["rw", str(prj_dir), "-o", str(out_path), "--plain"]
    )
    assert res.exit_code == 0, res.stdout
    assert out_path.exists()
    # HEAD did not move; no in.rw.tac symlink in the project either.
    prj1 = Project.open(prj_dir)
    assert prj1.head_sha == head0
    assert not (prj_dir / "in.rw.tac").exists()


def test_rw_records_provenance(tmp_path: Path) -> None:
    prj_dir, prj0 = _init_project(tmp_path)
    head0 = prj0.head_sha
    runner = CliRunner()
    runner.invoke(app, ["rw", str(prj_dir), "--plain"])
    prj1 = Project.open(prj_dir)
    rw_obj = prj1.head
    # rw output's provenance points back to the base.
    assert rw_obj.command == "rw"
    assert head0 in rw_obj.parents


# ----------------------------------------------------------- ua


# Multi-assert TAC so `ua` actually does work (single-assert is a no-op).
TAC_MULTI_ASSERT = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tb:bool
}
Program {
\tBlock entry Succ [ok] {
\t\tAssignExpCmd b true
\t\tJumpCmd ok
\t}
\tBlock ok Succ [exit] {
\t\tAssertCmd b "first"
\t\tJumpCmd exit
\t}
\tBlock exit Succ [] {
\t\tAssertCmd b "second"
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""


# Two asserts on a havoc-driven boolean — rw can't prove either away.
TAC_MULTI_ASSERT_NONTRIVIAL = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tb:bool
}
Program {
\tBlock entry Succ [ok] {
\t\tAssignHavocCmd b
\t\tJumpCmd ok
\t}
\tBlock ok Succ [exit] {
\t\tAssertCmd b "first"
\t\tJumpCmd exit
\t}
\tBlock exit Succ [] {
\t\tAssertCmd b "second"
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""


def test_ua_advances_head(tmp_path: Path) -> None:
    prj_dir, prj0 = _init_project(tmp_path, TAC_MULTI_ASSERT)
    head0 = prj0.head_sha
    runner = CliRunner()
    res = runner.invoke(app, ["ua", str(prj_dir), "--plain"])
    assert res.exit_code == 0, res.stdout
    prj1 = Project.open(prj_dir)
    assert prj1.head_sha != head0
    assert (prj_dir / "in.ua.tac").is_symlink()
    assert prj1.head.command == "ua"
    assert head0 in prj1.head.parents


def test_ua_pipeline_after_rw(tmp_path: Path) -> None:
    """rw → ua pipeline produces base.rw.tac and base.rw.ua.tac."""
    prj_dir, _ = _init_project(tmp_path, TAC_MULTI_ASSERT)
    runner = CliRunner()
    r1 = runner.invoke(app, ["rw", str(prj_dir), "--plain"])
    assert r1.exit_code == 0, r1.stdout
    r2 = runner.invoke(app, ["ua", str(prj_dir), "--plain"])
    assert r2.exit_code == 0, r2.stdout
    assert (prj_dir / "in.rw.tac").is_symlink()
    assert (prj_dir / "in.rw.ua.tac").is_symlink()
    prj = Project.open(prj_dir)
    assert "in.rw.ua.tac" in prj.head.names


def test_ua_split_in_project_requires_explicit_output(tmp_path: Path) -> None:
    """Split produces a fileset; phase 2 doesn't ingest those, so the
    user must pass -o explicitly."""
    prj_dir, _ = _init_project(tmp_path, TAC_MULTI_ASSERT)
    runner = CliRunner()
    res = runner.invoke(app, ["ua", str(prj_dir), "--strategy", "split", "--plain"])
    assert res.exit_code == 1
    assert "phase 3" in res.stdout


# ----------------------------------------------------------- pp


def test_pp_registers_htac_without_advancing_head(tmp_path: Path) -> None:
    prj_dir, prj0 = _init_project(tmp_path)
    head0 = prj0.head_sha
    runner = CliRunner()
    res = runner.invoke(app, ["pp", str(prj_dir), "--plain"])
    assert res.exit_code == 0, res.stdout
    prj1 = Project.open(prj_dir)
    # HEAD did not move.
    assert prj1.head_sha == head0
    # An htac sibling was registered.
    htac_link = prj_dir / "in.htac"
    assert htac_link.is_symlink()
    htac_objs = [o for o in prj1.list_objects() if o.kind == "htac"]
    assert len(htac_objs) == 1
    assert htac_objs[0].command == "pp"
    assert head0 in htac_objs[0].parents


def test_pp_explicit_output_skips_project(tmp_path: Path) -> None:
    prj_dir, _ = _init_project(tmp_path)
    out = tmp_path / "explicit.htac"
    runner = CliRunner()
    res = runner.invoke(app, ["pp", str(prj_dir), "-o", str(out), "--plain"])
    assert res.exit_code == 0
    assert out.exists()
    prj = Project.open(prj_dir)
    htac_objs = [o for o in prj.list_objects() if o.kind == "htac"]
    assert htac_objs == []


# ----------------------------------------------------------- smt


def test_smt_registers_smt2_without_advancing_head(tmp_path: Path) -> None:
    prj_dir, prj0 = _init_project(tmp_path)
    head0 = prj0.head_sha
    runner = CliRunner()
    res = runner.invoke(app, ["smt", str(prj_dir), "--plain"])
    assert res.exit_code == 0, res.stdout
    prj1 = Project.open(prj_dir)
    assert prj1.head_sha == head0
    assert (prj_dir / "in.smt2").is_symlink()
    smt_objs = [o for o in prj1.list_objects() if o.kind == "smt"]
    assert len(smt_objs) == 1
    assert smt_objs[0].command == "smt"
    assert head0 in smt_objs[0].parents


def test_full_pipeline_rw_ua_smt(tmp_path: Path) -> None:
    """The headline workflow: rw → ua → smt, all driven by `mytac`.

    Uses :data:`TAC_MULTI_ASSERT_NONTRIVIAL` so the simplifier can't
    prove the asserts away into a zero-assert program."""
    prj_dir, _ = _init_project(tmp_path, TAC_MULTI_ASSERT_NONTRIVIAL)
    runner = CliRunner()
    assert runner.invoke(app, ["rw", str(prj_dir), "--plain"]).exit_code == 0
    assert runner.invoke(app, ["ua", str(prj_dir), "--plain"]).exit_code == 0
    assert runner.invoke(app, ["smt", str(prj_dir), "--plain"]).exit_code == 0
    # All four expected friendly names should be present.
    names = {p.name for p in prj_dir.iterdir() if p.is_symlink()}
    assert "in.tac" in names
    assert "in.rw.tac" in names
    assert "in.rw.ua.tac" in names
    assert "in.rw.ua.smt2" in names
    prj = Project.open(prj_dir)
    # HEAD ends on the .ua.tac (smt is non-HEAD-advancing).
    assert "in.rw.ua.tac" in prj.head.names
    # smt object's parent is HEAD (the .ua.tac).
    smt_objs = [o for o in prj.list_objects() if o.kind == "smt"]
    assert len(smt_objs) == 1
    assert prj.head_sha in smt_objs[0].parents


def test_rw_idempotent_rerun(tmp_path: Path) -> None:
    """Running `rw` twice on a project where the simplifier converges
    should not multiply HEAD-advancing entries — same content sha
    reuses the same object."""
    prj_dir, _ = _init_project(tmp_path)
    runner = CliRunner()
    res1 = runner.invoke(app, ["rw", str(prj_dir), "--plain"])
    assert res1.exit_code == 0
    prj1 = Project.open(prj_dir)
    head1 = prj1.head_sha
    nobjs1 = len(prj1.list_objects())

    res2 = runner.invoke(app, ["rw", str(prj_dir), "--plain"])
    assert res2.exit_code == 0
    prj2 = Project.open(prj_dir)
    # If rw is a fixed point on this input, head stays put and no new
    # object is added.
    if prj2.head_sha == head1:
        assert len(prj2.list_objects()) == nobjs1
