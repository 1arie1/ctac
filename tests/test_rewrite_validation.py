"""Tests for `ctac rw-valid` — per-rule SMT soundness specs."""

from __future__ import annotations

import json
import shutil
import subprocess

import pytest
from typer.testing import CliRunner

from ctac.rewrite.rules import (
    ADD_BV_MAX_TO_ITE_CASES,
    R1_CASES,
    R4_CASES,
    R4A_CASES,
    R6_CASES,
    validation_cases,
)
from ctac.tool.main import app


def test_registry_holds_expected_cases():
    """R4 has 5 operator variants; R4A, R6 each have base + signed;
    R1 and ADD_BV_MAX_TO_ITE each have a single case."""
    cases_by_name = {(vc.name, vc.case) for vc in validation_cases}
    assert {("R4", c) for c in ("Lt", "Le", "Gt", "Ge", "Eq")} <= cases_by_name
    assert ("R4a", "") in cases_by_name
    assert ("R4a", "signed") in cases_by_name
    assert ("R6", "") in cases_by_name
    assert ("R6", "signed") in cases_by_name
    assert ("R1", "") in cases_by_name
    assert ("ADD_BV_MAX_TO_ITE", "") in cases_by_name
    # The flat-envelope (algebraic) rules sum to a fixed count; the
    # gadget-family / EqSubZero / neg_s128 cases are added on top.
    assert len(validation_cases) >= (
        len(R1_CASES)
        + len(R4_CASES)
        + len(R4A_CASES)
        + len(R6_CASES)
        + len(ADD_BV_MAX_TO_ITE_CASES)
    )


def test_every_smt2_script_is_a_negated_soundness_check():
    """Every emitted script carries the common shape: set-logic, decls,
    a trailing `(check-sat)`, and the soundness claim negated. The flat
    (algebraic) rules use a single `(assert (not (= X Y)))`; the
    gadget-family lemmas conjoin several equivalences under one negated
    assertion (`(not (and ...))`) or the equivalent disjunction of
    negations (`(or (not ...) ...)`). Either way the check is: no model
    makes the claim false."""
    for vc in validation_cases:
        s = vc.smt2_text
        assert "(set-logic " in s
        assert "(declare-const " in s
        assert "(check-sat)" in s.splitlines()[-1] or s.rstrip().endswith("(check-sat)")
        # The claim is negated, so `unsat` means sound. Flat rules use
        # `(assert (not (= X Y)))`; gadget lemmas conjoin equivalences
        # under `(not (and ...))` or `(or (not ...) ...)`.
        assert "(not " in s, vc.file_stem


def test_file_stem_combines_name_and_case():
    assert {vc.file_stem for vc in R4_CASES} == {
        "R4_Lt",
        "R4_Le",
        "R4_Gt",
        "R4_Ge",
        "R4_Eq",
    }
    assert {vc.file_stem for vc in R4A_CASES} == {"R4a", "R4a_signed"}
    assert {vc.file_stem for vc in R6_CASES} == {"R6", "R6_signed"}


@pytest.mark.skipif(shutil.which("z3") is None, reason="z3 not on PATH")
def test_every_validation_case_discharges_unsat():
    """Run z3 on every registered spec: each must be `unsat` (the rule
    is sound). This is the independent check that the validation
    module's lemmas hold — the gadget-family / EqSubZero / neg_s128
    cases as well as the algebraic R1/R4/R4a/R6 ones."""
    for vc in validation_cases:
        proc = subprocess.run(
            ["z3", "-smt2", "-T:20", "-in"],
            input=vc.smt2_text, capture_output=True, text=True, timeout=60,
        )
        assert proc.stdout.strip() == vc.expected, (vc.file_stem, proc.stdout)


def test_cli_emits_scripts_and_manifest(tmp_path):
    runner = CliRunner()
    out = tmp_path / "rwv"
    result = runner.invoke(app, ["rw-valid", "-o", str(out), "--plain"])
    assert result.exit_code == 0, result.output

    # Scripts exist for every registered case.
    for vc in validation_cases:
        assert (out / f"{vc.file_stem}.smt2").is_file()

    # Manifest is valid JSON and records each case.
    manifest = json.loads((out / "manifest.json").read_text())
    assert len(manifest["rules"]) == len(validation_cases)
    assert set(manifest["missing"]) >= {"R2", "R3", "N1", "N2", "N3", "N4"}
    # Every entry has the expected keys.
    for entry in manifest["rules"]:
        assert set(entry) == {"rule", "case", "smt2", "expected", "description"}
        assert entry["expected"] == "unsat"


def test_cli_rule_filter_restricts_output(tmp_path):
    runner = CliRunner()
    out = tmp_path / "rwv"
    result = runner.invoke(
        app, ["rw-valid", "-o", str(out), "--rule", "R4a", "--plain"]
    )
    assert result.exit_code == 0, result.output
    smt_files = sorted(p.name for p in out.glob("*.smt2"))
    assert smt_files == ["R4a.smt2", "R4a_signed.smt2"]


def test_cli_empty_selection_exits_nonzero(tmp_path):
    runner = CliRunner()
    out = tmp_path / "rwv"
    result = runner.invoke(
        app, ["rw-valid", "-o", str(out), "--rule", "NoSuchRule", "--plain"]
    )
    assert result.exit_code != 0, result.output
    assert "no validation cases match" in result.output.lower()
