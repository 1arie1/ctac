"""Regression test for the ``CeilToMultiple`` rule + the rw-eq symbol-
table merge fix, using the kvault ``shares_to_burn_consistency``
fixture.

What's checked here is structural, fast, and doesn't depend on z3:

  1. ``ctac rw --no-purify-div --no-simplify-div-in-cmp`` fires
     ``CeilToMultiple`` exactly twice (one per parallel chain).
  2. ``ctac rw-eq`` carries rw's fresh ``TB<N>:bool`` symbols (emitted
     by ITE_PURIFY) into the merged TAC's symbol table — without that,
     the stricter ``sea`` encoder rejects with a sort mismatch.
  3. ``ctac smt --encoding sea`` parses every split-assert without
     ``sort mismatch`` errors.

The end-to-end ``smt --run`` verdicts (every split must close
``unsat``) were verified manually with z3 4.17; that loop is too
sensitive to local z3 performance to gate CI on.
"""

from __future__ import annotations

from pathlib import Path

import pytest
from typer.testing import CliRunner

from ctac.tool.main import app


_FIXTURE = (
    Path(__file__).parent.parent
    / "examples"
    / "kvault"
    / "shares_to_burn_consistency"
    / "PresolverRule-rule_shares_to_burn_consistency-#assert_3.tac"
)


@pytest.mark.skipif(not _FIXTURE.is_file(), reason="stbc fixture missing")
def test_stbc_rule_fires_and_rweq_symbol_table_complete(
    tmp_path: Path,
) -> None:
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
            "--report",
            "--plain",
        ],
    )
    assert rw_result.exit_code == 0, rw_result.output
    # Both ceil-to-multiple chains must lift in a single rw pass.
    assert "CeilToMultiple: 2" in rw_result.output, rw_result.output

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

    # The rw-eq merge must carry over rw's fresh symbols (TB<N>:bool
    # emitted by ITE_PURIFY). Pre-fix, the merged TAC referenced TB0
    # in commands but never declared it — sea (stricter encoder)
    # rejected with a sort mismatch.
    eq_text = eq_out.read_text()
    assert "TB0:bool" in eq_text, "rw-eq dropped TB0:bool from symbol table"
    assert "TB1:bool" in eq_text, "rw-eq dropped TB1:bool from symbol table"

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

    # Every split-assert must parse + encode under sea without sort
    # mismatches. (sea_vc was already working before the rw-eq fix
    # because it lazily infers sorts; sea is the careful one.)
    asserts = sorted(split_dir.glob("assert_*.tac"))
    assert asserts, "ua --strategy split produced no asserts"
    for assert_path in asserts:
        out_smt = tmp_path / f"{assert_path.stem}.smt2"
        smt_result = runner.invoke(
            app,
            [
                "smt",
                "--encoding",
                "sea",
                str(assert_path),
                "-o",
                str(out_smt),
                "--plain",
            ],
        )
        # sea may reject IntCeilDiv as unsupported (pre-existing
        # gap — sea_vc has the axiom, sea doesn't). That's fine for
        # this test; what we're guarding against is the sort-mismatch
        # class of error, which would name a specific symbol.
        if smt_result.exit_code != 0:
            assert "sort mismatch" not in smt_result.output, (
                f"{assert_path.name}: sort mismatch — "
                f"rw-eq symbol-table regression?\n{smt_result.output}"
            )
