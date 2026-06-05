"""End-to-end test for the rewrite-trail / model-replay pipeline.

Builds a tiny program where ``HavocEquateSubst`` eliminates a havoc'd
variable R via ``R == X``, then exercises:

1. ``ctac rw --trail`` emits a JSON sidecar.
2. ``ctac run --model M --trail T`` on the original recovers R from the
   trail (no sentinel fallback).
3. Project-mode auto-discovery: ``ctac rw`` on a project ingests the
   trail; ``ctac run`` on the same project picks it up automatically.
"""

from __future__ import annotations

import json
from pathlib import Path

from typer.testing import CliRunner

from ctac.tool.main import app


def _wrap(body: str, *, syms: str) -> str:
    return f"""TACSymbolTable {{
\tUserDefined {{
\t}}
\tBuiltinFunctions {{
\t}}
\tUninterpretedFunctions {{
\t}}
\t{syms}
}}
Program {{
{body}
}}
Axioms {{
}}
Metas {{
  "0": []
}}
"""


# R is a dummy havoc (only used in assumes including the equality
# to X). X is havoc'd with a non-assume use (Y = X), so it's not a
# dummy. HavocEquate{Subst} eliminates R, recording R -> X. After
# rewrite + DCE only X survives in the rewritten program; a model
# from the rewrite has X but not R.
TRAIL_FIXTURE_TAC = _wrap(
    "\tBlock e Succ [exit] {\n"
    "\t\tAssignHavocCmd X\n"
    "\t\tAssignHavocCmd R\n"
    "\t\tAssumeExpCmd Le(R 0x10)\n"
    "\t\tAssumeExpCmd Eq(R X)\n"
    "\t\tAssignExpCmd Y X\n"
    "\t\tAssertCmd Le(Y 0x10000)\n"
    "\t\tJumpCmd exit\n"
    "\t}\n"
    "\tBlock exit Succ [] {\n"
    "\t\tNoSuchCmd\n"
    "\t}\n",
    syms="R:bv256\n\tX:bv256\n\tY:bv256",
)


def test_rw_emits_trail_json(tmp_path: Path) -> None:
    """`ctac rw --trail PATH` writes a JSON sidecar with the
    R -> X substitution recorded by HavocEquate{Fold,Subst}."""
    src = tmp_path / "in.tac"
    src.write_text(TRAIL_FIXTURE_TAC)
    out = tmp_path / "out.tac"
    trail = tmp_path / "out.trail.json"

    runner = CliRunner()
    res = runner.invoke(
        app,
        ["rw", str(src), "-o", str(out), "--trail", str(trail), "--plain"],
    )
    assert res.exit_code == 0, res.output
    assert trail.exists()
    data = json.loads(trail.read_text())
    assert data["version"] == 1
    vars_recorded = {s["var"] for s in data["substitutions"]}
    assert "R" in vars_recorded
    # Replacement is over a surviving var (X).
    r_entry = next(s for s in data["substitutions"] if s["var"] == "R")
    assert "X" in r_entry["replacement"]


def test_run_uses_trail_to_recover_eliminated_havoc(tmp_path: Path) -> None:
    """`ctac run --model M --trail T` resolves a havoc'd R that the
    model lacks by evaluating R's trail-replacement expression. The
    `model havoc:` summary shows a nonzero trail_hits."""
    src = tmp_path / "in.tac"
    src.write_text(TRAIL_FIXTURE_TAC)
    out = tmp_path / "out.tac"
    trail = tmp_path / "out.trail.json"

    runner = CliRunner()
    rw_res = runner.invoke(
        app,
        ["rw", str(src), "-o", str(out), "--trail", str(trail), "--plain"],
    )
    assert rw_res.exit_code == 0, rw_res.output

    # Hand-write a model that defines X (the survivor) but NOT R.
    model_path = tmp_path / "m.txt"
    model_path.write_text("sat\n(\n  (define-fun X () Int 5)\n)\n")

    run_res = runner.invoke(
        app,
        [
            "run",
            str(src),
            "--model",
            str(model_path),
            "--trail",
            str(trail),
            "--plain",
        ],
    )
    assert run_res.exit_code in (0, 2, 3), run_res.output
    # Trail loaded.
    assert "trail:" in run_res.output
    # R was recovered via the trail (not the sentinel).
    assert "trail_hits=1" in run_res.output


def test_run_without_trail_falls_back_to_sentinel(tmp_path: Path) -> None:
    """Confirms the baseline that motivates the trail: without
    --trail, R defaults to the sentinel and trips its range assume."""
    src = tmp_path / "in.tac"
    src.write_text(TRAIL_FIXTURE_TAC)

    model_path = tmp_path / "m.txt"
    model_path.write_text("sat\n(\n  (define-fun X () Int 5)\n)\n")

    runner = CliRunner()
    res = runner.invoke(
        app,
        [
            "run",
            str(src),
            "--model",
            str(model_path),
            "--plain",
        ],
    )
    # No trail: sentinel fallback fires.
    assert "sentinel_fallback=1" in res.output


def test_file_inside_project_auto_discovers_trail(tmp_path: Path) -> None:
    """Pass the friendly-name symlink for the original .tac (not the
    project directory). Auto-discovery should walk up to ``.ctac/`` and
    use the file's object-store SHA as the lineage anchor — the trail
    parented to the rw'd object applies because base is its ancestor."""
    src = tmp_path / "in.tac"
    src.write_text(TRAIL_FIXTURE_TAC)
    prj = tmp_path / "mytac"

    runner = CliRunner()
    res = runner.invoke(app, ["prj", "init", str(src), "-o", str(prj), "--plain"])
    assert res.exit_code == 0, res.output
    res = runner.invoke(app, ["rw", str(prj), "--plain"])
    assert res.exit_code == 0, res.output

    # The original .tac as a friendly-name symlink inside the project.
    in_tac = prj / "base.tac"
    assert in_tac.is_symlink()

    model_path = tmp_path / "m.txt"
    model_path.write_text("sat\n(\n  (define-fun X () Int 5)\n)\n")

    res = runner.invoke(
        app,
        ["run", str(in_tac), "--model", str(model_path), "--plain"],
    )
    assert res.exit_code in (0, 2, 3), res.output
    assert "trail:" in res.output
    assert "trail_hits=1" in res.output


def test_loose_file_outside_project_has_no_trail(tmp_path: Path) -> None:
    """Sanity: a plain .tac file that's not a friendly-name symlink
    inside a project doesn't trigger auto-discovery — only --trail
    PATH or project-dir input do."""
    src = tmp_path / "in.tac"
    src.write_text(TRAIL_FIXTURE_TAC)
    model_path = tmp_path / "m.txt"
    model_path.write_text("sat\n(\n  (define-fun X () Int 5)\n)\n")

    runner = CliRunner()
    res = runner.invoke(
        app,
        ["run", str(src), "--model", str(model_path), "--plain"],
    )
    assert "trail:" not in res.output


def test_project_mode_auto_emits_and_consumes_trail(tmp_path: Path) -> None:
    """Project workflow: prj init + rw auto-emits the trail; run on
    the same project picks it up automatically without --trail."""
    src = tmp_path / "in.tac"
    src.write_text(TRAIL_FIXTURE_TAC)
    prj = tmp_path / "mytac"

    runner = CliRunner()
    res = runner.invoke(app, ["prj", "init", str(src), "-o", str(prj), "--plain"])
    assert res.exit_code == 0, res.output

    res = runner.invoke(app, ["rw", str(prj), "--plain"])
    assert res.exit_code == 0, res.output
    # Trail object was emitted into the project.
    trail_friendly = prj / "base.rw.trail.json"
    assert trail_friendly.exists()

    # Move HEAD back to base; trail should still auto-apply via the
    # lineage walk (trail's parent is the rw'd object, whose ancestor
    # is base).
    res = runner.invoke(app, ["prj", "set-head", str(prj), "base", "--plain"])
    assert res.exit_code == 0, res.output

    model_path = tmp_path / "m.txt"
    model_path.write_text("sat\n(\n  (define-fun X () Int 5)\n)\n")

    res = runner.invoke(
        app,
        ["run", str(prj), "--model", str(model_path), "--plain"],
    )
    assert res.exit_code in (0, 2, 3), res.output
    assert "trail:" in res.output
    assert "trail_hits=1" in res.output
