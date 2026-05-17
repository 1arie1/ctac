"""Tests for cover Phase 2 — subgoal + certificate data models, rerun.sh
emitters, and the `ctac verify-cover` re-verifier."""
from __future__ import annotations

import json
import shutil
import textwrap
from pathlib import Path

import pytest
from typer.testing import CliRunner

from ctac.cover import (
    ActionSuggestion,
    ClusterRecord,
    CompletenessProof,
    Decomposition,
    HardnessDiagnosis,
    ProgramReplayPlan,
    SatCertificate,
    SourceAnchor,
    SubProof,
    Subgoal,
    UnsatCertificate,
    emit_sat_rerun_sh,
    emit_unsat_rerun_sh,
    load_certificate,
    save_certificate,
    write_rerun_sh,
)
from ctac.cover.verify import verify
from ctac.tool.main import app


def _z3_available() -> bool:
    return shutil.which('z3') is not None


# ============================== subgoal roundtrip ============================


def test_subgoal_roundtrip_full() -> None:
    s = Subgoal(
        id='cluster_0',
        kind='cfg-cluster',
        smt2='cluster_0/v.smt2',
        tac='cluster_0/pinned.tac',
        rw_tac='cluster_0/pinned.rw.tac',
        parent_vc='in.tac',
        source_anchors=(
            SourceAnchor(function='foo', file='a.sol', line_start=10,
                          line_end=20),
            SourceAnchor(sbf_address_range=(0x100, 0x180)),
        ),
        hardness=HardnessDiagnosis(
            label='nlsat-bottleneck', confidence=0.9,
            signature={'nlsat-stages': 1500.0}, rationale='steady nlsat'),
        suggested_actions=(
            ActionSuggestion(label='retry seeds',
                              command='ctac z3 v.smt2 --seeds 0-7',
                              expected_payoff='may close'),
        ),
        rerun_cmd='ctac smt cluster_0/v.smt2 --run',
    )
    s2 = Subgoal.from_json_dict(s.to_json_dict())
    assert s == s2


def test_subgoal_roundtrip_minimal() -> None:
    """A subgoal with only required fields still roundtrips."""
    s = Subgoal(
        id='alpha_3',
        kind='alpha-commit',
        smt2='alpha_3/v.smt2',
        parent_vc='in.smt2',
        rerun_cmd='ctac z3 alpha_3/v.smt2',
    )
    assert Subgoal.from_json_dict(s.to_json_dict()) == s


def test_source_anchor_partial_fields() -> None:
    """Each SourceAnchor field is independently optional."""
    a = SourceAnchor(function='only_func')
    a2 = SourceAnchor.from_json_dict(a.to_json_dict())
    assert a == a2

    b = SourceAnchor(sbf_address_range=(100, 200))
    b2 = SourceAnchor.from_json_dict(b.to_json_dict())
    assert b == b2


# ============================ certificate roundtrip ==========================


def _make_sat_cert() -> SatCertificate:
    return SatCertificate(
        sat_smt2='cluster_3/v.smt2',
        z3_model={'R0': '42', 'R1': '0'},
        z3_invocation=('z3', '-T:30', '-smt2', 'cluster_3/v.smt2'),
        program_replay=ProgramReplayPlan(
            tac_path='cluster_3/pinned.tac',
            model_text_path='cluster_3/model.smt',
        ),
        rerun_sh='rerun.sh',
        witness_cluster='cluster_3',
        wall_s=1.2,
    )


def _make_unsat_cert() -> UnsatCertificate:
    return UnsatCertificate(
        decomposition=Decomposition(
            kind='cfg-cluster',
            clusters=(
                ClusterRecord(id='cluster_0', keep_blocks=('B1', 'B2'),
                                paths_covered=4),
                ClusterRecord(id='cluster_1', keep_blocks=('B1', 'B3'),
                                paths_covered=3),
            ),
        ),
        sub_proofs=(
            SubProof(sub_id='cluster_0', smt2='cluster_0/v.smt2',
                      z3_invocation=('z3', '-T:30', '-smt2', 'cluster_0/v.smt2'),
                      wall_s=2.5),
            SubProof(sub_id='cluster_1', smt2='cluster_1/v.smt2',
                      z3_invocation=('z3', '-T:30', '-smt2', 'cluster_1/v.smt2'),
                      wall_s=3.1),
        ),
        completeness_proof=CompletenessProof(
            probe_smt2='completeness/probe_final.smt2',
            z3_invocation=('z3', '-T:30', '-smt2',
                            'completeness/probe_final.smt2'),
            wall_s=0.05,
        ),
        rerun_sh='rerun.sh',
    )


def test_sat_certificate_roundtrip() -> None:
    c = _make_sat_cert()
    assert SatCertificate.from_json_dict(c.to_json_dict()) == c


def test_unsat_certificate_roundtrip() -> None:
    c = _make_unsat_cert()
    assert UnsatCertificate.from_json_dict(c.to_json_dict()) == c


def test_load_certificate_dispatches_on_kind(tmp_path: Path) -> None:
    sat_p = tmp_path / 'sat.json'
    save_certificate(_make_sat_cert(), sat_p)
    loaded = load_certificate(sat_p)
    assert isinstance(loaded, SatCertificate)

    unsat_p = tmp_path / 'unsat.json'
    save_certificate(_make_unsat_cert(), unsat_p)
    loaded = load_certificate(unsat_p)
    assert isinstance(loaded, UnsatCertificate)


def test_load_certificate_rejects_unknown_kind(tmp_path: Path) -> None:
    p = tmp_path / 'bad.json'
    p.write_text(json.dumps({'kind': 'lemur', 'schema_version': 1}))
    with pytest.raises(ValueError, match='unknown certificate kind'):
        load_certificate(p)


# ============================== rerun.sh shape ==============================


def test_sat_rerun_sh_includes_both_checks() -> None:
    text = emit_sat_rerun_sh(_make_sat_cert())
    assert 'z3 SAT confirm' in text
    assert 'sat cluster_3/v.smt2' in text or 'cluster_3/v.smt2' in text
    assert 'ctac run' in text
    assert 'assert_fail' in text
    assert text.startswith('#!/usr/bin/env bash')


def test_unsat_rerun_sh_one_check_per_subproof_plus_probe() -> None:
    text = emit_unsat_rerun_sh(_make_unsat_cert())
    assert text.count('run_check ') == 3  # 2 subs + 1 probe
    assert 'sub cluster_0' in text
    assert 'sub cluster_1' in text
    assert 'completeness probe' in text


def test_write_rerun_sh_marks_executable(tmp_path: Path) -> None:
    p = tmp_path / 'rerun.sh'
    write_rerun_sh(_make_sat_cert(), p)
    assert p.exists()
    mode = p.stat().st_mode
    assert mode & 0o111, 'rerun.sh should be executable'


# ============================ verify against real z3 =========================


_TRIVIAL_UNSAT_SMT2 = textwrap.dedent("""\
    (set-logic QF_UF)
    (assert false)
    (check-sat)
""")

_TRIVIAL_SAT_SMT2 = textwrap.dedent("""\
    (set-logic QF_UF)
    (declare-const x Bool)
    (assert x)
    (check-sat)
""")


@pytest.mark.skipif(not _z3_available(), reason='z3 not on PATH')
def test_verify_unsat_against_real_z3(tmp_path: Path) -> None:
    """Hand-craft a 2-subproof UNSAT cert pointing at trivial smt2's;
    verify should re-confirm UNSAT on each."""
    z3_path = shutil.which('z3')
    (tmp_path / 'cluster_0').mkdir()
    (tmp_path / 'cluster_1').mkdir()
    (tmp_path / 'completeness').mkdir()
    (tmp_path / 'cluster_0' / 'v.smt2').write_text(_TRIVIAL_UNSAT_SMT2)
    (tmp_path / 'cluster_1' / 'v.smt2').write_text(_TRIVIAL_UNSAT_SMT2)
    (tmp_path / 'completeness' / 'probe.smt2').write_text(_TRIVIAL_UNSAT_SMT2)

    cert = UnsatCertificate(
        decomposition=Decomposition(
            kind='cfg-cluster',
            clusters=(
                ClusterRecord(id='cluster_0', keep_blocks=('B1',)),
                ClusterRecord(id='cluster_1', keep_blocks=('B2',)),
            ),
        ),
        sub_proofs=(
            SubProof(sub_id='cluster_0', smt2='cluster_0/v.smt2',
                      z3_invocation=(z3_path, '-T:10', '-smt2',
                                      'cluster_0/v.smt2')),
            SubProof(sub_id='cluster_1', smt2='cluster_1/v.smt2',
                      z3_invocation=(z3_path, '-T:10', '-smt2',
                                      'cluster_1/v.smt2')),
        ),
        completeness_proof=CompletenessProof(
            probe_smt2='completeness/probe.smt2',
            z3_invocation=(z3_path, '-T:10', '-smt2',
                            'completeness/probe.smt2'),
        ),
        rerun_sh='rerun.sh',
    )
    cert_path = tmp_path / 'cover.json'
    save_certificate(cert, cert_path)

    report = verify(cert_path, timeout_s=10)
    assert report.passed, f'expected pass, got: {report.summary()}\n' + \
        '\n'.join(f'{c.label}: {c.got} ({c.detail})' for c in report.checks)
    assert len(report.checks) == 3


@pytest.mark.skipif(not _z3_available(), reason='z3 not on PATH')
def test_verify_unsat_detects_tampered_subproof(tmp_path: Path) -> None:
    """If a sub-smt2 returns SAT instead of UNSAT, verify must FAIL."""
    z3_path = shutil.which('z3')
    (tmp_path / 'cluster_0').mkdir()
    (tmp_path / 'completeness').mkdir()
    # Tampered: this sub claims to be UNSAT but the file is SAT.
    (tmp_path / 'cluster_0' / 'v.smt2').write_text(_TRIVIAL_SAT_SMT2)
    (tmp_path / 'completeness' / 'probe.smt2').write_text(_TRIVIAL_UNSAT_SMT2)

    cert = UnsatCertificate(
        decomposition=Decomposition(
            kind='cfg-cluster',
            clusters=(ClusterRecord(id='cluster_0', keep_blocks=()),),
        ),
        sub_proofs=(
            SubProof(sub_id='cluster_0', smt2='cluster_0/v.smt2',
                      z3_invocation=(z3_path, '-T:10', '-smt2',
                                      'cluster_0/v.smt2')),
        ),
        completeness_proof=CompletenessProof(
            probe_smt2='completeness/probe.smt2',
            z3_invocation=(z3_path, '-T:10', '-smt2',
                            'completeness/probe.smt2'),
        ),
        rerun_sh='rerun.sh',
    )
    cert_path = tmp_path / 'cover.json'
    save_certificate(cert, cert_path)

    report = verify(cert_path, timeout_s=10)
    assert not report.passed
    # The cluster_0 check should be the one that fails (got=sat).
    failing = [c for c in report.checks if not c.passed]
    assert len(failing) == 1
    assert 'cluster_0' in failing[0].label
    assert failing[0].got == 'sat'


@pytest.mark.skipif(not _z3_available(), reason='z3 not on PATH')
def test_verify_unsat_detects_tampered_completeness(tmp_path: Path) -> None:
    """If the completeness probe returns SAT, verify must FAIL — this is
    the most important soundness check (a SAT probe means some path
    escaped every cluster)."""
    z3_path = shutil.which('z3')
    (tmp_path / 'cluster_0').mkdir()
    (tmp_path / 'completeness').mkdir()
    (tmp_path / 'cluster_0' / 'v.smt2').write_text(_TRIVIAL_UNSAT_SMT2)
    # Tampered completeness probe: SAT instead of UNSAT.
    (tmp_path / 'completeness' / 'probe.smt2').write_text(_TRIVIAL_SAT_SMT2)

    cert = UnsatCertificate(
        decomposition=Decomposition(
            kind='cfg-cluster',
            clusters=(ClusterRecord(id='cluster_0', keep_blocks=()),),
        ),
        sub_proofs=(
            SubProof(sub_id='cluster_0', smt2='cluster_0/v.smt2',
                      z3_invocation=(z3_path, '-T:10', '-smt2',
                                      'cluster_0/v.smt2')),
        ),
        completeness_proof=CompletenessProof(
            probe_smt2='completeness/probe.smt2',
            z3_invocation=(z3_path, '-T:10', '-smt2',
                            'completeness/probe.smt2'),
        ),
        rerun_sh='rerun.sh',
    )
    cert_path = tmp_path / 'cover.json'
    save_certificate(cert, cert_path)

    report = verify(cert_path, timeout_s=10)
    assert not report.passed
    failing = [c for c in report.checks if not c.passed]
    assert len(failing) == 1
    assert 'completeness probe' in failing[0].label


# =============================== CLI exit codes =============================


@pytest.mark.skipif(not _z3_available(), reason='z3 not on PATH')
def test_verify_cover_cli_exit_0_on_pass(tmp_path: Path) -> None:
    z3_path = shutil.which('z3')
    (tmp_path / 'cluster_0').mkdir()
    (tmp_path / 'completeness').mkdir()
    (tmp_path / 'cluster_0' / 'v.smt2').write_text(_TRIVIAL_UNSAT_SMT2)
    (tmp_path / 'completeness' / 'probe.smt2').write_text(_TRIVIAL_UNSAT_SMT2)

    cert = UnsatCertificate(
        decomposition=Decomposition(
            kind='cfg-cluster',
            clusters=(ClusterRecord(id='cluster_0', keep_blocks=()),),
        ),
        sub_proofs=(
            SubProof(sub_id='cluster_0', smt2='cluster_0/v.smt2',
                      z3_invocation=(z3_path, '-T:10', '-smt2',
                                      'cluster_0/v.smt2')),
        ),
        completeness_proof=CompletenessProof(
            probe_smt2='completeness/probe.smt2',
            z3_invocation=(z3_path, '-T:10', '-smt2',
                            'completeness/probe.smt2'),
        ),
        rerun_sh='rerun.sh',
    )
    save_certificate(cert, tmp_path / 'cover.json')

    r = CliRunner().invoke(
        app, ['verify-cover', str(tmp_path / 'cover.json'),
              '-T', '10', '--plain'])
    assert r.exit_code == 0, r.stdout
    assert 'VERIFY OK' in r.stdout or 'OK' in r.stdout


@pytest.mark.skipif(not _z3_available(), reason='z3 not on PATH')
def test_verify_cover_cli_exit_1_on_fail(tmp_path: Path) -> None:
    z3_path = shutil.which('z3')
    (tmp_path / 'cluster_0').mkdir()
    (tmp_path / 'completeness').mkdir()
    # Tampered.
    (tmp_path / 'cluster_0' / 'v.smt2').write_text(_TRIVIAL_SAT_SMT2)
    (tmp_path / 'completeness' / 'probe.smt2').write_text(_TRIVIAL_UNSAT_SMT2)

    cert = UnsatCertificate(
        decomposition=Decomposition(
            kind='cfg-cluster',
            clusters=(ClusterRecord(id='cluster_0', keep_blocks=()),),
        ),
        sub_proofs=(
            SubProof(sub_id='cluster_0', smt2='cluster_0/v.smt2',
                      z3_invocation=(z3_path, '-T:10', '-smt2',
                                      'cluster_0/v.smt2')),
        ),
        completeness_proof=CompletenessProof(
            probe_smt2='completeness/probe.smt2',
            z3_invocation=(z3_path, '-T:10', '-smt2',
                            'completeness/probe.smt2'),
        ),
        rerun_sh='rerun.sh',
    )
    save_certificate(cert, tmp_path / 'cover.json')

    r = CliRunner().invoke(
        app, ['verify-cover', str(tmp_path / 'cover.json'),
              '-T', '10', '--plain'])
    assert r.exit_code == 1
    assert 'FAILED' in r.stdout
