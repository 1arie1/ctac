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
