"""Tests for cover Phase 2 — subgoal + certificate data models, rerun.sh
emitters, and the `ctac verify-cover` re-verifier."""
from __future__ import annotations

import json
import shutil
from pathlib import Path

import pytest

from ctac.cover import (
    ActionSuggestion,
    ClusterRecord,
    CompletenessProof,
    CoverMetadata,
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


_META = CoverMetadata(
    input_tac='/abs/path/in.tac',
    z3_bin='/usr/bin/z3',
    z3_version='Z3 version 4.17.0',
    rw_flags=('--interval-select',),
    smt_flags=('--encoding', 'sea', '--cfg-encoding', 'fwd-edg',
                 '--inline-scalars'),
)


def _make_sat_cert() -> SatCertificate:
    return SatCertificate(
        metadata=_META,
        sat_smt2='cluster_3/v.smt2',
        winner_drops=('B4', 'B5'),
        z3_model={'R0': '42', 'R1': '0'},
        z3_args=('-st', 'smt.random_seed=0', 'sat.random_seed=0'),
        program_replay=ProgramReplayPlan(
            tac_path=_META.input_tac,
            model_text_path='cluster_3/model.smt',
        ),
        rerun_sh='rerun.sh',
        witness_cluster='cluster_3',
        wall_s=1.2,
    )


def _make_unsat_cert() -> UnsatCertificate:
    return UnsatCertificate(
        metadata=_META,
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
                      drops=('B3', 'B4'),
                      z3_args=('-st', 'smt.random_seed=0'),
                      wall_s=2.5),
            SubProof(sub_id='cluster_1', smt2='cluster_1/v.smt2',
                      drops=('B2', 'B5'),
                      z3_args=('-st', 'smt.random_seed=0'),
                      wall_s=3.1),
        ),
        completeness_proof=CompletenessProof(
            probe_smt2='completeness/probe_final.smt2',
            z3_args=('-st',),
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
    assert text.startswith('#!/usr/bin/env bash')
    # Re-derivation chain
    assert 'rederive_cluster' in text
    assert '"$CTAC" pin' in text or 'ctac pin' in text
    # Verdict + replay
    assert 'z3 SAT confirm' in text
    assert 'cluster_3/v.smt2' in text
    assert '"$CTAC" run' in text or 'ctac run' in text
    assert 'assert_fail' in text
    # Replay targets INPUT_TAC
    assert 'INPUT_TAC' in text
    # Metadata baked in
    assert 'EXPECTED_Z3_VERSION' in text


def test_unsat_rerun_sh_one_check_per_subproof_plus_probe() -> None:
    text = emit_unsat_rerun_sh(_make_unsat_cert())
    # Re-derivation + verdict checks: 2 subs + 1 probe.
    assert text.count('rederive_cluster ') == 2
    assert text.count('check_verdict "sub') == 2
    assert 'sub cluster_0' in text
    assert 'sub cluster_1' in text
    assert text.count('check_verdict "completeness probe"') == 1
    # Drops baked into rederive calls
    assert 'B3,B4' in text
    assert 'B2,B5' in text


def test_unsat_rerun_sh_bakes_input_tac_and_version() -> None:
    text = emit_unsat_rerun_sh(_make_unsat_cert())
    assert _META.input_tac in text
    assert _META.z3_version in text
    # rw / smt flags also baked in for re-derivation
    assert '--interval-select' in text
    assert 'sea' in text and 'fwd-edg' in text


def test_write_rerun_sh_marks_executable(tmp_path: Path) -> None:
    p = tmp_path / 'rerun.sh'
    write_rerun_sh(_make_sat_cert(), p)
    assert p.exists()
    mode = p.stat().st_mode
    assert mode & 0o111, 'rerun.sh should be executable'


