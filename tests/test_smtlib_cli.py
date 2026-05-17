"""Tests for `ctac smtlib` CLI subcommands."""
from __future__ import annotations

from pathlib import Path

from typer.testing import CliRunner

from ctac.tool.main import app


SAMPLE = """; preamble
(set-logic QF_UFNIA)
(declare-const x Int)
(declare-const y Int)
(define-fun M0 ((idx Int)) Int (ite (= idx x) 1 0))
(assert (! (> x 0) :named pos))
(assert (< y 10))
(check-sat)
"""


def _write(tmp: Path) -> Path:
    p = tmp / 'f.smt2'
    p.write_text(SAMPLE)
    return p


# ---- slice -----------------------------------------------------------------


def test_slice_kinds_filters_to_asserts(tmp_path: Path) -> None:
    f = _write(tmp_path)
    r = CliRunner().invoke(
        app, ['smtlib', 'slice', str(f), '--kinds', 'Assert', '--plain'])
    assert r.exit_code == 0, r.stdout
    lines = [ln for ln in r.stdout.splitlines() if ln.strip()]
    assert all(ln.startswith('(assert') for ln in lines)
    assert ':named pos' in r.stdout
    assert '(< y 10)' in r.stdout


def test_slice_range_inclusive(tmp_path: Path) -> None:
    f = _write(tmp_path)
    # Statements (0-indexed):
    # 0: Comment, 1: SetLogic, 2: DeclareConst x, 3: DeclareConst y,
    # 4: DefineFun M0, 5: Assert pos, 6: Assert lt, 7: CheckSat
    r = CliRunner().invoke(
        app, ['smtlib', 'slice', str(f), '--range', '2-4', '--plain'])
    assert r.exit_code == 0, r.stdout
    assert '(declare-const x Int)' in r.stdout
    assert '(declare-const y Int)' in r.stdout
    assert '(define-fun M0' in r.stdout
    assert '(set-logic' not in r.stdout
    assert '(check-sat)' not in r.stdout


def test_slice_combined_filters(tmp_path: Path) -> None:
    f = _write(tmp_path)
    # Keep only Asserts in stmt 0..5 → just the :named pos assert.
    r = CliRunner().invoke(
        app, ['smtlib', 'slice', str(f),
              '--kinds', 'Assert', '--range', '0-5', '--plain'])
    assert r.exit_code == 0, r.stdout
    assert ':named pos' in r.stdout
    assert '(< y 10)' not in r.stdout


def test_slice_unknown_kind_rejected(tmp_path: Path) -> None:
    f = _write(tmp_path)
    r = CliRunner().invoke(
        app, ['smtlib', 'slice', str(f), '--kinds', 'Foo', '--plain'])
    assert r.exit_code != 0
    assert 'unknown --kinds' in r.stdout or 'unknown --kinds' in (r.stderr or '')


def test_slice_no_comments_drops_top_level_comment(tmp_path: Path) -> None:
    f = _write(tmp_path)
    r = CliRunner().invoke(
        app, ['smtlib', 'slice', str(f),
              '--kinds', 'Comment', '--no-comments', '--plain'])
    assert r.exit_code == 0, r.stdout
    # Comment was the only matching kind, and --no-comments drops it → empty.
    assert r.stdout.strip() == ''


def test_slice_output_file(tmp_path: Path) -> None:
    f = _write(tmp_path)
    out = tmp_path / 'out.smt2'
    r = CliRunner().invoke(
        app, ['smtlib', 'slice', str(f), '--kinds', 'Assert',
              '-o', str(out), '--plain'])
    assert r.exit_code == 0, r.stdout
    body = out.read_text()
    assert '(assert' in body
    assert ':named pos' in body


# ---- stats / pp / roundtrip smoke (light) ----------------------------------


def test_stats_smoke(tmp_path: Path) -> None:
    f = _write(tmp_path)
    r = CliRunner().invoke(app, ['smtlib', 'stats', str(f), '--plain'])
    assert r.exit_code == 0, r.stdout
    assert 'command_kinds:' in r.stdout
    assert 'Assert: 2' in r.stdout


def test_roundtrip_byte_identical(tmp_path: Path) -> None:
    f = _write(tmp_path)
    r = CliRunner().invoke(app, ['smtlib', 'roundtrip', str(f), '--plain'])
    assert r.exit_code == 0, r.stdout
    assert 'byte-identical' in r.stdout


def test_agent_guide_routes_to_smtlib(tmp_path: Path) -> None:
    # ctac smtlib stats --agent should return the smtlib namespace guide,
    # not the (existing) TAC `stats` guide.
    r = CliRunner().invoke(app, ['smtlib', 'stats', '--agent'])
    assert r.exit_code == 0, r.stdout
    assert 'ctac smtlib --agent' in r.stdout
    # Sanity: shouldn't be the TAC `stats` guide.
    assert 'FIRST LOOK on any unknown TAC/SBF file' not in r.stdout
