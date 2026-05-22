"""End-to-end regression for the u128 lift / ceil-div reconstruction
rules using the kvault ``check_shares_to_burn_lemma`` TAC fixture.

Why this fixture: it's the concrete real-world target the rewrites
were developed against (carry-add lift, u128 decrement, chunk
merge, muldiv → Div(V), Mod-identity CP, drop-range-redundant
assumes). Every rule was validated against this TAC via
``ctac rw → rw-eq → ua-split → smt`` cycles during development;
this test bakes that loop into the suite so any regression in the
rule set or pipeline ordering surfaces immediately.

Pipeline tested (the same one used during development):

  ctac rw --no-purify-div --no-simplify-div-in-cmp <fixture>
  ctac rw-eq <fixture> <rw_out>
  ctac ua --strategy split <eq>
  ctac smt --plain --run <split_assert_NN>  (every split)

Every emitted rw-eq CHK plus the original assertion must
discharge ``unsat``. The fixture is the production rule's TAC; the
original assertion is the safety property that's expected to hold,
so it discharges unsat too — same total count as observed during
development (currently 21).

Skipped when z3 isn't on PATH (the same gate other end-to-end
rw-eq tests use). The full pipeline + 20+ z3 invocations takes
~25-30 seconds; that's the cost of validating every rule's
soundness through the actual VC.
"""

from __future__ import annotations

import shutil
from pathlib import Path

import pytest
from typer.testing import CliRunner

from ctac.tool.main import app


_FIXTURE = (
    Path(__file__).parent.parent
    / "examples"
    / "kvault"
    / "csb_lemma"
    / "csb_lemma.tac"
)


def _z3_available() -> bool:
    return shutil.which("z3") is not None


@pytest.mark.skipif(not _FIXTURE.is_file(), reason="csb_lemma fixture missing")
@pytest.mark.skipif(not _z3_available(), reason="z3 not on PATH")
def test_csb_lemma_full_pipeline_rw_eq_all_unsat(tmp_path: Path) -> None:
    """rw → rw-eq → ua-split → smt on the full csb_lemma TAC. Every
    discharged verdict must be ``unsat``. Failure means some rule in
    the u128 lift / chunk-merge / drop-redundant chain has gone
    unsound or the pipeline order broke the invariants the rules
    depend on."""
    runner = CliRunner()

    rw_out = tmp_path / "rw.tac"
    rw_result = runner.invoke(
        app,
        [
            "rw",
            str(_FIXTURE),
            "-o",
            str(rw_out),
            "--no-purify-div",
            "--no-simplify-div-in-cmp",
            "--plain",
        ],
    )
    assert rw_result.exit_code == 0, rw_result.output

    eq_out = tmp_path / "eq.tac"
    eq_result = runner.invoke(
        app,
        [
            "rw-eq",
            str(_FIXTURE),
            str(rw_out),
            "-o",
            str(eq_out),
            "--plain",
        ],
    )
    assert eq_result.exit_code == 0, eq_result.output

    split_dir = tmp_path / "split"
    ua_result = runner.invoke(
        app,
        [
            "ua",
            str(eq_out),
            "--strategy",
            "split",
            "-o",
            str(split_dir),
            "--plain",
        ],
    )
    assert ua_result.exit_code == 0, ua_result.output

    asserts = sorted(split_dir.glob("assert_*.tac"))
    assert asserts, (
        f"ua --strategy split produced no asserts under {split_dir}"
    )

    for assert_path in asserts:
        smt_result = runner.invoke(
            app,
            [
                "smt",
                str(assert_path),
                "--plain",
                "--run",
                "--timeout",
                "30",
            ],
        )
        assert smt_result.exit_code == 0, smt_result.output
        verdict = smt_result.output.strip().splitlines()[-1]
        assert verdict == "unsat", (
            f"{assert_path.name}: expected ``unsat``, got {verdict!r}. "
            f"Full smt output:\n{smt_result.output}"
        )
