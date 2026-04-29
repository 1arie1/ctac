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
from ctac.rewrite.framework import RewriteResult
from ctac.rewrite.rules import chain_recognition_pipeline, cse_pipeline, default_pipeline
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


def _run_default_two_phase(orig_program, symbol_sorts) -> RewriteResult:
    """Drive ``ctac rw``'s rewrite pipeline through chain-recognition,
    early CSE, and general simplification. Mirrors what the CLI does
    pre-DCE / pre-purify (those later phases aren't relevant to the
    rule-fired structural check). CSE runs in its own dedicated phase
    so its per-iteration RHS index is a real snapshot — no rule
    alongside it mutates a registered RHS mid-iter and shifts canon
    equivalence."""
    phase0 = rewrite_program(
        orig_program, chain_recognition_pipeline, symbol_sorts=symbol_sorts
    )
    phase_cse = rewrite_program(
        phase0.program, cse_pipeline, symbol_sorts=symbol_sorts
    )
    phase1 = rewrite_program(
        phase_cse.program, default_pipeline, symbol_sorts=symbol_sorts
    )
    # Merge hit counts so callers see firings from all phases.
    from collections import Counter

    merged_hits: Counter[str] = Counter(phase0.hits_by_rule)
    merged_hits.update(phase_cse.hits_by_rule)
    merged_hits.update(phase1.hits_by_rule)
    return RewriteResult(
        program=phase1.program,
        hits=phase0.hits + phase_cse.hits + phase1.hits,
        hits_by_rule=dict(merged_hits),
        iterations=phase0.iterations + phase_cse.iterations + phase1.iterations,
        extra_symbols=(
            phase0.extra_symbols
            + phase_cse.extra_symbols
            + phase1.extra_symbols
        ),
    )


_DIR_TO_RULE_NAME: dict[str, str] = {
    # Directory names follow the Python constant (e.g. CP_ALIAS); the
    # rewriter's `Rule.name` attribute follows a different convention
    # for some rules (e.g. "CP", "IteCondFold"). Map explicitly so the
    # framework stays correct as either side gets renamed.
    "CP_ALIAS": "CP",
    "ITE_COND_FOLD": "IteCondFold",
    "R4A": "R4a",
}


def _expected_rules_for(rule_dir_name: str) -> set[str]:
    """Return the set of rule names that MUST fire on every fixture in
    a rule directory under default-pipeline runs.

    The directory name is the canonical rule slug; we expect that rule
    (under its registered ``Rule.name``) to fire on its own fixtures,
    with documented exceptions for cases where the fixture is a
    NEGATIVE test (rule should NOT fire) — those fixtures use the
    ``unsound_*`` or ``negative_*`` filename prefix convention.

    This catches rule-interaction regressions: if a future rewrite
    rule pre-empts the canonical rule's pattern, the runner reports
    "rule X did not fire on its own fixture" loud and clear instead
    of silently passing because the equivalence still happens to hold.

    The ``REGRESSION/`` directory is special: fixtures there are
    end-to-end regression cases minimised from real corpora, where
    the salient property is "rw + rw-eq + smt produces no SAT CHK"
    rather than any specific rule firing. No expected-rule check
    runs for them.
    """
    if rule_dir_name == "REGRESSION":
        return set()
    return {_DIR_TO_RULE_NAME.get(rule_dir_name, rule_dir_name)}


def _is_negative_fixture(fixture: Path) -> bool:
    """Fixtures that intentionally make the rule NOT fire (testing the
    gate's rejection path) are named ``unsound_*`` or ``negative_*``."""
    name = fixture.stem
    return name.startswith("unsound_") or name.startswith("negative_")


def _run_pipeline(fixture: Path) -> tuple:
    """rw → rw-eq → ua-split. Returns (rw_result, equivalence_result, split_result)."""
    orig_tac = parse_path(fixture)
    rw = _run_default_two_phase(orig_tac.program, orig_tac.symbol_sorts)
    eq = emit_equivalence_program(orig_tac.program, rw.program)
    split = split_asserts(eq.program)
    return rw, eq, split


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
    produce well-formed artefacts. Always runs; doesn't need z3.

    Also asserts that the canonical rule for the fixture's directory
    actually fires under the default pipeline. This catches
    rule-interaction regressions (e.g. a new distribution rule
    pre-empting R6's chain pattern) loud and early."""
    rw, _, split = _run_pipeline(fixture)
    if not _is_negative_fixture(fixture):
        expected = _expected_rules_for(rule_name)
        fired = set(rw.hits_by_rule.keys())
        missing = expected - fired
        assert not missing, (
            f"{rule_name}/{fixture.name}: expected rules {expected} to fire "
            f"but {missing} did not. rule_hits={dict(rw.hits_by_rule)}. "
            f"This indicates a rule-interaction regression — another rule "
            f"may have pre-empted {missing}'s pattern under the default "
            f"two-phase pipeline."
        )
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
    _, _, split = _run_pipeline(fixture)

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
        # Reuse the original TacFile envelope (symbol table, axioms)
        # to render each per-assert program back to .tac text.
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


# R6 needs a restricted pipeline: the default pipeline's bool / Ite
# simplification rules pre-empt the chain pattern (rewriting X1 into a
# bool temporary), preventing R6 from matching. The existing R6 unit
# test in test_rewrite_ceildiv.py uses (N1, N2, N3, N4, R6) for this
# reason. We do the same here so the rule actually fires and rw-eq
# stresses *its* soundness rather than the surrounding rules'.


@pytest.mark.skipif(not _z3_available(), reason="z3 not on PATH")
def test_r6_stress_with_restricted_pipeline(tmp_path: Path) -> None:
    """R6 (ceildiv chain collapse) stress-tested via the bit-op-only
    pipeline that lets the rule actually fire. Exercises rw-eq's rule
    6 (rehavoc window) on a non-trivial multi-assume admission — R6
    is the most algebraically intricate rewrite the rewriter does
    today, and the one with the largest soundness surface."""
    from ctac.rewrite.rules import (
        N1_SHIFTED_BWAND,
        N2_LOW_MASK,
        N3_HIGH_MASK,
        N4_SHR_CONST,
        R6_CEILDIV,
    )

    fixture = _FIXTURES_DIR / "R6" / "ceildiv_chain.tac"
    orig_tac = parse_path(fixture)
    # Pinned to the legacy emission (havoc + polynomial bounds) so this
    # test continues to assert on the rehavoc-window path. The new
    # IntCeilDiv emission is exercised by a sibling test below.
    rw = rewrite_program(
        orig_tac.program,
        (N1_SHIFTED_BWAND, N2_LOW_MASK, N3_HIGH_MASK, N4_SHR_CONST, R6_CEILDIV),
        use_int_ceil_div=False,
    )
    # Confirm R6 actually fired — otherwise this test isn't doing what
    # it claims and the failure mode (rule didn't match) needs a
    # diagnostic, not a silent pass.
    assert rw.hits_by_rule.get("R6", 0) >= 1, (
        f"R6 didn't fire on the chain fixture: rule_hits={rw.hits_by_rule}"
    )

    eq = emit_equivalence_program(orig_tac.program, rw.program)
    # Rule 6 (rehavoc) should have been admitted at least once.
    assert eq.rehavoc_sites, (
        "rule 6 (rehavoc window) didn't fire — R6's rewrite is the "
        "canonical rehavoc, so this is unexpected."
    )

    split = split_asserts(eq.program)
    from ctac.ast.nodes import AssertCmd
    from ctac.parse import render_tac_file

    rw_eq_assert_count = 0
    for out in split.outputs:
        msg = out.message or ""
        if not msg.startswith("rw-eq:"):
            continue
        rw_eq_assert_count += 1
        out_path = tmp_path / f"r6_split_{out.index:02d}.tac"
        text = render_tac_file(orig_tac, program=out.program)
        out_path.write_text(text, encoding="utf-8")
        smt_text = _build_smt_for(out_path)
        result = subprocess.run(
            ["z3", "-smt2", "-T:30", "-in"],
            input=smt_text,
            capture_output=True,
            text=True,
            timeout=60,
        )
        verdict = result.stdout.strip().splitlines()[0] if result.stdout else ""
        # Sanity that we exercise an AssertCmd in the split.
        assert any(
            isinstance(c, AssertCmd) for b in out.program.blocks for c in b.commands
        ), "no AssertCmd in split output"
        assert verdict == "unsat", (
            f"R6 stress: split assert {out.index} ({msg!r}) returned "
            f"{verdict!r} (expected unsat). z3 stdout: {result.stdout!r}"
        )

    assert rw_eq_assert_count >= 1, (
        "no rw-eq assertions were emitted by the merged program — "
        "rule 6 should have produced at least the rehavoc-close eq check."
    )


@pytest.mark.skipif(not _z3_available(), reason="z3 not on PATH")
def test_r6_stress_with_int_ceil_div(tmp_path: Path) -> None:
    """R6 in the new ``IntCeilDiv``-emitting mode stress-tested via
    rw-eq end-to-end. With ``use_int_ceil_div=True`` (default in this
    test):

    - The rewriter emits ``Apply(safe_math_narrow_bv256:bif
      IntCeilDiv(R_num, R_den))`` for the chain-final assignment.
    - The rw-eq walker sees no rule-6 (rehavoc) trigger — the rw side
      has an ordinary AssignExpCmd, not ``havoc X`` — so
      ``eq.rehavoc_sites`` is empty.
    - Every emitted equivalence assertion must discharge ``unsat``
      under z3, confirming the IntCeilDiv axiom plus the orig
      program's existing range assumes are sufficient. No
      rewriter-injected helper assumes are emitted on this path.
    """
    from ctac.ast.nodes import ApplyExpr, AssertCmd, AssignExpCmd, SymbolRef
    from ctac.parse import render_tac_file
    from ctac.rewrite.rules import (
        N1_SHIFTED_BWAND,
        N2_LOW_MASK,
        N3_HIGH_MASK,
        N4_SHR_CONST,
        R6_CEILDIV,
    )

    fixture = _FIXTURES_DIR / "R6" / "ceildiv_chain.tac"
    orig_tac = parse_path(fixture)
    rw = rewrite_program(
        orig_tac.program,
        (N1_SHIFTED_BWAND, N2_LOW_MASK, N3_HIGH_MASK, N4_SHR_CONST, R6_CEILDIV),
        use_int_ceil_div=True,
    )
    assert rw.hits_by_rule.get("R6", 0) >= 1, (
        f"R6 didn't fire on the chain fixture: rule_hits={rw.hits_by_rule}"
    )

    # The new path emits an IntCeilDiv ApplyExpr somewhere in the rw program.
    def _has_int_ceil_div(e):
        if isinstance(e, ApplyExpr):
            if e.op == "IntCeilDiv":
                return True
            return any(_has_int_ceil_div(a) for a in e.args)
        return False

    found = False
    for b in rw.program.blocks:
        for c in b.commands:
            if isinstance(c, AssignExpCmd) and _has_int_ceil_div(c.rhs):
                found = True
                break
        if found:
            break
    assert found, "expected IntCeilDiv in rw output but didn't find it"

    eq = emit_equivalence_program(orig_tac.program, rw.program)
    # The new path triggers no rule-6 rehavoc window (the rw side has
    # an ordinary assignment, not ``havoc R_ceil``).
    assert eq.rehavoc_sites == (), (
        f"unexpected rehavoc sites under the new IntCeilDiv path: "
        f"{eq.rehavoc_sites}"
    )

    split = split_asserts(eq.program)
    rw_eq_assert_count = 0
    for out in split.outputs:
        msg = out.message or ""
        if not msg.startswith("rw-eq:"):
            continue
        rw_eq_assert_count += 1
        out_path = tmp_path / f"r6_intceildiv_split_{out.index:02d}.tac"
        text = render_tac_file(orig_tac, program=out.program)
        out_path.write_text(text, encoding="utf-8")
        smt_text = _build_smt_for(out_path)
        result = subprocess.run(
            ["z3", "-smt2", "-T:30", "-in"],
            input=smt_text,
            capture_output=True,
            text=True,
            timeout=60,
        )
        verdict = result.stdout.strip().splitlines()[0] if result.stdout else ""
        # Sanity that we exercise an AssertCmd in the split.
        assert any(
            isinstance(c, AssertCmd) for b in out.program.blocks for c in b.commands
        ), "no AssertCmd in split output"
        assert verdict == "unsat", (
            f"R6 IntCeilDiv stress: split assert {out.index} ({msg!r}) "
            f"returned {verdict!r} (expected unsat). z3 stdout: "
            f"{result.stdout!r}"
        )

    assert rw_eq_assert_count >= 1, (
        "no rw-eq assertions were emitted by the merged program — "
        "the rule-2 step that rewrites R_ceil's RHS should have produced "
        "at least one equivalence check."
    )

    # Suppress unused-import lint hints.
    _ = SymbolRef
