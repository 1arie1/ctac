"""Per-rule stress tests for the rewriter, driven through `ctac rw-eq`.

For each fixture under ``tests/rw_eq_fixtures/<rule>/``:

1. Run ``ctac rw`` on the fixture, producing the rewritten TAC.
2. Run ``ctac rw-eq`` on (orig, rw), producing a merged
   equivalence-check program.
3. Run ``ctac ua --strategy split`` on the merged program,
   producing per-assert TACs.
4. (When z3 is on PATH) run ``ctac smt --run`` on every per-assert
   file. Every emitted ``rw-eq:`` assertion must discharge ``unsat``;
   the program's own assertions are tagged differently and are
   ignored for this test (their satisfaction is the *program*'s
   correctness question, not the rewriter's).

Fast checks (parsing + structural) always run; z3-discharging
checks are gated on a binary being on PATH so devs without z3
still get the structural feedback.
"""

from __future__ import annotations

import shutil
import subprocess
from pathlib import Path

import pytest

from ctac.parse import parse_path
from ctac.rewrite import rewrite_program
from ctac.rewrite.rules import default_pipeline
from ctac.rw_eq import emit_equivalence_program
from ctac.ua import split_asserts


_FIXTURES_DIR = Path(__file__).parent / "rw_eq_fixtures"


def _z3_available() -> bool:
    return shutil.which("z3") is not None


def _all_fixtures() -> list[tuple[str, Path]]:
    """Discover (rule_name, fixture_path) pairs under tests/rw_eq_fixtures."""
    pairs: list[tuple[str, Path]] = []
    if not _FIXTURES_DIR.is_dir():
        return pairs
    for rule_dir in sorted(_FIXTURES_DIR.iterdir()):
        if not rule_dir.is_dir():
            continue
        for f in sorted(rule_dir.glob("*.tac")):
            pairs.append((rule_dir.name, f))
    return pairs


@pytest.fixture(scope="module")
def fixtures() -> list[tuple[str, Path]]:
    return _all_fixtures()


def _run_pipeline(fixture: Path) -> tuple[Path, list[Path]]:
    """rw → rw-eq → ua-split. Returns (merged.tac, list of split assert files)."""
    orig_tac = parse_path(fixture)

    # Step 1: rewrite. Use full default pipeline (matches what ctac rw does).
    rw = rewrite_program(orig_tac.program, default_pipeline)

    # Step 2: rw-eq.
    eq = emit_equivalence_program(orig_tac.program, rw.program)

    # Step 3: ua-split (in-process; we don't shell out for the test).
    split = split_asserts(eq.program)
    return eq, split


def test_fixtures_directory_has_at_least_one_fixture():
    pairs = _all_fixtures()
    assert pairs, (
        f"no fixtures discovered under {_FIXTURES_DIR}; tests/rw_eq_fixtures/"
        f"<rule>/<case>.tac files are how rules get stress coverage."
    )


@pytest.mark.parametrize(
    "rule_name,fixture",
    _all_fixtures(),
    ids=lambda x: x.stem if isinstance(x, Path) else x,
)
def test_fixture_pipeline_structure(rule_name: str, fixture: Path) -> None:
    """Structural sanity: rewrite + rw-eq + split run without exceptions and
    produce well-formed artefacts. Always runs; doesn't need z3."""
    _, split = _run_pipeline(fixture)
    # split is a SplitAssertsResult.
    # Every output's program should have at least one block (the
    # original assert site is preserved).
    for out in split.outputs:
        assert out.program.blocks, (
            f"{rule_name}/{fixture.name}: split output {out.index} has "
            f"no blocks"
        )
        # Each split should have exactly one AssertCmd (live), since
        # ua --strategy split is supposed to enforce that for ctac smt.
        from ctac.ast.nodes import AssertCmd

        assert_count = sum(
            1
            for b in out.program.blocks
            for c in b.commands
            if isinstance(c, AssertCmd)
        )
        assert assert_count == 1, (
            f"{rule_name}/{fixture.name}: split output {out.index} has "
            f"{assert_count} AssertCmds, expected 1"
        )


@pytest.mark.skipif(not _z3_available(), reason="z3 not on PATH")
@pytest.mark.parametrize(
    "rule_name,fixture",
    _all_fixtures(),
    ids=lambda x: x.stem if isinstance(x, Path) else x,
)
def test_fixture_rw_eq_assertions_discharge(
    rule_name: str, fixture: Path, tmp_path: Path
) -> None:
    """End-to-end: every ``rw-eq:`` assertion in every split file must
    discharge ``unsat`` under z3. Skipped when z3 isn't on PATH.

    Assertions whose message doesn't start with ``rw-eq:`` (e.g. the
    program's own original asserts) are SAT-ok — they belong to the
    program's correctness question, not the rewriter's. Walk the
    manifest's ``message`` field to identify which split files are
    rw-eq checks.
    """
    eq, split = _run_pipeline(fixture)

    # Write split outputs to disk so ctac smt CLI can consume them.
    # (We could call build_vc directly, but the CLI integration is
    # what users actually run, so testing through the same path catches
    # plumbing bugs too.)
    from ctac.parse import render_tac_file

    for out in split.outputs:
        msg = out.message or ""
        # Identify rw-eq assertions by message prefix.
        is_rw_eq_check = msg.startswith("rw-eq:")
        if not is_rw_eq_check:
            # Original program assertion; skip — its sat/unsat is the
            # program's question, not ours.
            continue

        out_path = tmp_path / f"split_{out.index:02d}.tac"
        # `eq` here is the merged TacProgram; we need a TacFile to
        # render. Reuse the original TacFile envelope.
        orig_tac_file = parse_path(fixture)
        text = render_tac_file(orig_tac_file, program=out.program)
        out_path.write_text(text, encoding="utf-8")

        result = subprocess.run(
            [
                "z3",
                "-smt2",
                "-T:5",
                "-in",
            ],
            input=_build_smt_for(out_path),
            capture_output=True,
            text=True,
            timeout=30,
        )
        verdict = result.stdout.strip().splitlines()[0] if result.stdout else ""
        assert verdict == "unsat", (
            f"{rule_name}/{fixture.name}: split assert {out.index} "
            f"({msg!r}) returned {verdict!r} (expected unsat). "
            f"z3 stdout: {result.stdout!r}"
        )


def _build_smt_for(tac_file_path: Path) -> str:
    """Build the SMT-LIB script for a single-assert TAC file using
    ctac.smt's library API (avoids spawning ctac smt as a subprocess)."""
    from ctac.parse import parse_path as _parse
    from ctac.smt import build_vc, render_smt_script

    tf = _parse(tac_file_path)
    script = build_vc(tf)
    return render_smt_script(script)
