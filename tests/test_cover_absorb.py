"""Unit tests for the absorption-probe verdict handling.

`materialize_cluster` and `_short_solve` are monkeypatched so the
tests exercise only try_absorb's own logic: cluster selection and
the definitive-vs-fall-through verdict split.
"""
from __future__ import annotations

from pathlib import Path

import pytest

import ctac.cover.cfg.absorb as absorb_mod
from ctac.cover.cfg.absorb import try_absorb
from ctac.cover.cfg.cluster import Cluster
from ctac.cover.cfg.materialize import ClusterArtifacts
from ctac.cover.cfg.run import ClusterState


def _state(keep: frozenset[str]) -> ClusterState:
    arts = ClusterArtifacts(
        cluster_dir=Path('orig'),
        pinned_tac=Path('orig/pinned.tac'),
        rw_tac=Path('orig/pinned.rw.tac'),
        smt2=Path('orig/v.smt2'),
        drops=(),
        keep=tuple(sorted(keep)),
    )
    return ClusterState(
        cluster=Cluster(id='cluster_0', members=(0,), medoid=0, keep_union=keep),
        artifacts=arts,
        verdict='unsat',
    )


def _patch_materialize(monkeypatch, tmp_path: Path) -> None:
    def fake_materialize(*, input_tac, cluster_dir, keep, universe, ctac_bin):
        return ClusterArtifacts(
            cluster_dir=cluster_dir,
            pinned_tac=cluster_dir / 'pinned.tac',
            rw_tac=cluster_dir / 'pinned.rw.tac',
            smt2=cluster_dir / 'v.smt2',
            drops=(),
            keep=tuple(sorted(keep)),
        )

    monkeypatch.setattr(absorb_mod, 'materialize_cluster', fake_materialize)


def _try_absorb(states, verdict, monkeypatch, tmp_path):
    _patch_materialize(monkeypatch, tmp_path)
    monkeypatch.setattr(
        absorb_mod, '_short_solve', lambda *a, **kw: (verdict, 1.0, ['z3']))
    return try_absorb(
        states=states,
        escape=['B1', 'B2', 'B3'],
        absorb_threshold=5,
        absorb_budget_s=8,
        universe=['B1', 'B2', 'B3', 'B4'],
        input_tac=Path('in.tac'),
        output_dir=tmp_path,
        ctac_bin='ctac',
        z3_bin=Path('z3'),
    )


@pytest.mark.parametrize('verdict', ['unknown', 'timeout', 'error'])
def test_non_definitive_verdict_falls_through(verdict, monkeypatch, tmp_path):
    state = _state(frozenset({'B1', 'B2'}))
    result = _try_absorb([state], verdict, monkeypatch, tmp_path)
    assert result is None
    # The cluster must be untouched: no widening, no verdict change.
    assert state.cluster.keep_union == frozenset({'B1', 'B2'})
    assert state.verdict == 'unsat'


@pytest.mark.parametrize('verdict', ['sat', 'unsat'])
def test_definitive_verdict_widens_in_place(verdict, monkeypatch, tmp_path):
    state = _state(frozenset({'B1', 'B2'}))
    result = _try_absorb([state], verdict, monkeypatch, tmp_path)
    assert result is state
    assert state.verdict == verdict
    assert state.cluster.keep_union == frozenset({'B1', 'B2', 'B3'})


def test_no_cluster_within_threshold(monkeypatch, tmp_path):
    state = _state(frozenset({'B9'}))
    _patch_materialize(monkeypatch, tmp_path)
    monkeypatch.setattr(
        absorb_mod, '_short_solve', lambda *a, **kw: ('unsat', 1.0, ['z3']))
    result = try_absorb(
        states=[state],
        escape=['B1', 'B2', 'B3'],
        absorb_threshold=2,
        absorb_budget_s=8,
        universe=['B1', 'B2', 'B3', 'B9'],
        input_tac=Path('in.tac'),
        output_dir=tmp_path,
        ctac_bin='ctac',
        z3_bin=Path('z3'),
    )
    assert result is None
