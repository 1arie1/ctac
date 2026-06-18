import json

from typer.testing import CliRunner

import ttac_fixtures as fx
from ctac.ttac.cli import app

runner = CliRunner()


def _write(tmp_path, src):
    f = tmp_path / "prog.ttac"
    f.write_text(src)
    return str(f)


def test_parse_reports_summary(tmp_path):
    result = runner.invoke(app, ["parse", _write(tmp_path, fx.CORE), "--plain"])
    assert result.exit_code == 0
    assert "4 block(s)" in result.stdout
    assert "entry: entry" in result.stdout
    assert "exit: exit" in result.stdout


def test_parse_reports_error_with_position(tmp_path):
    result = runner.invoke(app, ["parse", _write(tmp_path, "entry:\n  x @ y\n")])
    assert result.exit_code == 1


def test_pp_round_trips(tmp_path):
    pretty_out = runner.invoke(app, ["pp", _write(tmp_path, fx.MUT_BORROW_SURFACE)])
    assert pretty_out.exit_code == 0
    # Feeding the pretty output back through parse succeeds.
    reparse = runner.invoke(app, ["parse", _write(tmp_path, pretty_out.stdout)])
    assert reparse.exit_code == 0


def test_missing_file():
    result = runner.invoke(app, ["parse", "/nonexistent/path.ttac"])
    assert result.exit_code == 2


def test_df_reports_valid_dsa(tmp_path):
    result = runner.invoke(app, ["df", _write(tmp_path, fx.CORE), "--plain"])
    assert result.exit_code == 0
    assert "dsa: valid" in result.stdout


def test_df_invalid_dsa_exits_nonzero(tmp_path):
    src = "entry:\n  x := havoc\n  x := havoc\n  halt\n"
    result = runner.invoke(app, ["df", _write(tmp_path, src), "--plain"])
    assert result.exit_code == 1
    assert "dsa: invalid" in result.stdout


def test_types_total_program(tmp_path):
    result = runner.invoke(app, ["types", _write(tmp_path, fx.CORE), "--plain"])
    assert result.exit_code == 0
    assert "bytemap | M" in result.stdout
    assert "bool | c" in result.stdout


def test_types_show_filter(tmp_path):
    result = runner.invoke(
        app, ["types", _write(tmp_path, fx.CORE), "--show", "bytemap", "--plain"]
    )
    assert result.exit_code == 0
    assert "bytemap | M" in result.stdout
    assert "bool | c" not in result.stdout


def test_types_untyped_program_exits_nonzero(tmp_path):
    src = "entry:\n  x := havoc\n  halt\n"
    result = runner.invoke(app, ["types", _write(tmp_path, src), "--plain"])
    assert result.exit_code == 1


def test_ua_merge_prints_single_assert_program(tmp_path):
    result = runner.invoke(app, ["ua", _write(tmp_path, fx.TWO_ASSERTS), "--plain"])
    assert result.exit_code == 0
    assert result.stdout.count("assert ") == 1
    assert "__UA_ERROR:" in result.stdout


def test_ua_split_creates_files_and_manifest(tmp_path):
    out = tmp_path / "out"
    result = runner.invoke(
        app,
        ["ua", _write(tmp_path, fx.BRANCH_ASSERTS), "--strategy", "split", "-o", str(out)],
    )
    assert result.exit_code == 0
    assert (out / "assert_00.ttac").is_file()
    assert (out / "assert_01.ttac").is_file()
    manifest = json.loads((out / "manifest.json").read_text())
    assert manifest["strategy"] == "split"
    assert manifest["asserts_before"] == 2
    assert len(manifest["outputs"]) == 2


def test_ua_split_requires_output_dir(tmp_path):
    result = runner.invoke(
        app, ["ua", _write(tmp_path, fx.BRANCH_ASSERTS), "--strategy", "split"]
    )
    assert result.exit_code == 2


def test_ua_unknown_strategy(tmp_path):
    result = runner.invoke(
        app, ["ua", _write(tmp_path, fx.TWO_ASSERTS), "--strategy", "bogus"]
    )
    assert result.exit_code == 2


def test_vcgen_prints_smt(tmp_path):
    result = runner.invoke(app, ["vcgen", _write(tmp_path, fx.CORE), "--plain"])
    assert result.exit_code == 0
    assert "(check-sat)" in result.stdout
    assert "(set-logic QF_UFNIA)" in result.stdout


def test_vcgen_multi_assert_prints_merge_note(tmp_path):
    result = runner.invoke(app, ["vcgen", _write(tmp_path, fx.TWO_ASSERTS), "--plain"])
    assert result.exit_code == 0
    assert "merged 2 assertions" in result.output


def test_vcgen_reference_program_exits_nonzero(tmp_path):
    result = runner.invoke(app, ["vcgen", _write(tmp_path, fx.MUT_BORROW_SURFACE)])
    assert result.exit_code == 1


def test_vcgen_writes_output_file(tmp_path):
    out = tmp_path / "vc.smt2"
    result = runner.invoke(
        app, ["vcgen", _write(tmp_path, fx.CORE), "-o", str(out)]
    )
    assert result.exit_code == 0
    assert "(check-sat)" in out.read_text()


def test_desugar_removes_borrow_commands(tmp_path):
    result = runner.invoke(app, ["desugar", _write(tmp_path, fx.MUT_BORROW_SURFACE)])
    assert result.exit_code == 0
    assert "borrow" not in result.output
    assert "r__value" in result.output


def test_desugar_pipes_into_vcgen(tmp_path):
    desugared = runner.invoke(app, ["desugar", _write(tmp_path, fx.MUT_BORROW_SURFACE)])
    assert desugared.exit_code == 0
    chained = runner.invoke(app, ["vcgen", "-", "--plain"], input=desugared.output)
    assert chained.exit_code == 0
    assert "(check-sat)" in chained.output


def test_stats_prints_capability(tmp_path):
    result = runner.invoke(app, ["stats", _write(tmp_path, fx.CORE), "--plain"])
    assert result.exit_code == 0
    assert "capability" in result.output
    assert "bytemap-rw" in result.output


def test_stats_json(tmp_path):
    result = runner.invoke(app, ["stats", _write(tmp_path, fx.BORROW_SURFACE), "--json"])
    assert result.exit_code == 0
    data = json.loads(result.output)
    assert data["overview.blocks"] == 1
    assert data["references.reference_free"] == "false"


def test_run_reports_asserts(tmp_path):
    src = "entry:\n  x := havoc\n  y := x + 1\n  ok := y == 1\n  assert ok\n  halt\n"
    result = runner.invoke(app, ["run", _write(tmp_path, src)])
    assert result.exit_code == 0
    assert "assert_ok: 1" in result.output
    assert "status: done" in result.output


def test_run_trace(tmp_path):
    src = "entry:\n  x := havoc\n  y := x + 1\n  ok := y == 1\n  assert ok\n  halt\n"
    result = runner.invoke(app, ["run", _write(tmp_path, src), "--trace"])
    assert result.exit_code == 0
    assert "y := x + 1" in result.output


def test_run_assume_stop_exits_2(tmp_path):
    src = "entry:\n  b := havoc\n  assume b\n  halt\n"
    result = runner.invoke(app, ["run", _write(tmp_path, src)])
    assert result.exit_code == 2
