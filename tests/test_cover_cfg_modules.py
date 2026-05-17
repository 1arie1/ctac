"""Unit tests for `ctac.cover.cfg.*` modules. z3-independent."""
from __future__ import annotations

from pathlib import Path

import networkx as nx
import pytest

from ctac.cover.cfg.cfg_graph import (
    CfgError,
    CfgInfo,
    blocks_on_entry_to_assert_paths,
    load_cfg,
    reachable_to_assert,
)
from ctac.cover.cfg.cluster import (
    auto_k,
    cluster_paths,
    hamming_set_distance,
)
from ctac.cover.cfg.completeness import (
    derive_path_from_model,
    edge_var,
    emit_probe,
    parse_edge_var,
    parse_true_edge_vars,
)
from ctac.cover.cfg.core_blocks import (
    core_blocks_from_stdout,
    core_to_blocks,
    parse_core,
)
from ctac.cover.cfg.sampling import (
    path_through_block,
    random_path,
    sample_paths,
    saturate_paths,
    uncovered_blocks,
)


# --------------------------------- fixtures ---------------------------------


_DIAMOND_TAC = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tx:bv256
\tc:bool
\tok:bool
}
Program {
\tBlock entry Succ [left, right] {
\t\tAssignExpCmd x 0x5
\t\tAssignExpCmd c true
\t\tJumpiCmd left right c
\t}
\tBlock left Succ [join] {
\t\tAssignExpCmd x 0x5
\t\tJumpCmd join
\t}
\tBlock right Succ [join] {
\t\tAssignExpCmd x 0x5
\t\tJumpCmd join
\t}
\tBlock join Succ [] {
\t\tAssignExpCmd ok true
\t\tAssertCmd ok "always-true"
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""


def _write_tac(tmp_path: Path, name: str = 'f.tac',
                 text: str = _DIAMOND_TAC) -> Path:
    p = tmp_path / name
    p.write_text(text)
    return p


def _fake_info(g: nx.DiGraph, entry: str, assert_b: str) -> CfgInfo:
    """A minimal CfgInfo for tests that don't need the TacFile."""
    import types
    fake_tac = types.SimpleNamespace(
        program=types.SimpleNamespace(blocks=[]),
    )
    return CfgInfo(graph=g, entry=entry, assert_block=assert_b,
                    tac=fake_tac)


# --------------------------------- cfg_graph --------------------------------


def test_load_cfg_diamond(tmp_path: Path) -> None:
    info = load_cfg(_write_tac(tmp_path))
    assert info.entry == 'entry'
    assert info.assert_block == 'join'
    assert info.graph.number_of_nodes() == 4
    assert info.graph.has_edge('entry', 'left')
    assert info.graph.has_edge('entry', 'right')
    assert info.graph.has_edge('left', 'join')
    assert info.graph.has_edge('right', 'join')


def test_load_cfg_rejects_no_assert(tmp_path: Path) -> None:
    # Strip the AssertCmd.
    no_assert = _DIAMOND_TAC.replace(
        '\t\tAssertCmd ok "always-true"\n', '')
    p = _write_tac(tmp_path, text=no_assert)
    with pytest.raises(CfgError, match='no AssertCmd'):
        load_cfg(p)


def test_load_cfg_rejects_two_asserts(tmp_path: Path) -> None:
    two = _DIAMOND_TAC.replace(
        '\t\tAssignExpCmd x 0x5\n\t\tJumpCmd join\n',
        '\t\tAssignExpCmd x 0x5\n\t\tAssertCmd ok "extra"\n\t\tJumpCmd join\n',
        1,
    )
    p = _write_tac(tmp_path, text=two)
    with pytest.raises(CfgError, match='AssertCmd blocks'):
        load_cfg(p)


def test_reachable_to_assert(tmp_path: Path) -> None:
    info = load_cfg(_write_tac(tmp_path))
    r = reachable_to_assert(info)
    assert r == {'entry', 'left', 'right', 'join'}


def test_blocks_on_entry_to_assert_paths(tmp_path: Path) -> None:
    info = load_cfg(_write_tac(tmp_path))
    s = blocks_on_entry_to_assert_paths(info)
    assert s == {'entry', 'left', 'right', 'join'}


# --------------------------------- sampling ---------------------------------


def test_random_path_visits_assert() -> None:
    g = nx.DiGraph()
    g.add_edges_from([('e', 'a'), ('e', 'b'), ('a', 'c'), ('b', 'c')])
    info = _fake_info(g, 'e', 'c')
    p = random_path(info, seed=0)
    assert p is not None
    assert p[0] == 'e' and p[-1] == 'c'
    # No repeats (DAG semantics).
    assert len(set(p)) == len(p)


def test_random_path_distinct_seeds_can_differ() -> None:
    g = nx.DiGraph()
    g.add_edges_from([('e', 'a'), ('e', 'b'), ('a', 'c'), ('b', 'c')])
    info = _fake_info(g, 'e', 'c')
    seen = {tuple(random_path(info, seed=s) or ()) for s in range(20)}
    assert len(seen) >= 2  # at least both branches sampled


def test_path_through_block() -> None:
    g = nx.DiGraph()
    g.add_edges_from([('e', 'a'), ('a', 'b'), ('b', 'c'),
                       ('e', 'x'), ('x', 'b')])
    info = _fake_info(g, 'e', 'c')
    p = path_through_block(info, 'x')
    assert p is not None
    assert 'x' in p
    assert p[0] == 'e' and p[-1] == 'c'


def test_sample_paths_dedupes() -> None:
    g = nx.DiGraph()
    # Only one possible path entry → a → b — dedupe makes sample list size=1.
    g.add_edges_from([('e', 'a'), ('a', 'b')])
    info = _fake_info(g, 'e', 'b')
    paths = sample_paths(info, n=5, seed=0)
    assert len(paths) == 1
    assert paths[0] == ['e', 'a', 'b']


def test_uncovered_blocks_and_saturate() -> None:
    g = nx.DiGraph()
    # Two paths e→a→c and e→b→c. Sample only one; the other is uncovered.
    g.add_edges_from([('e', 'a'), ('a', 'c'), ('e', 'b'), ('b', 'c')])
    info = _fake_info(g, 'e', 'c')
    paths = [['e', 'a', 'c']]
    assert uncovered_blocks(info, paths) == ['b']
    paths2 = saturate_paths(info, paths)
    blocks_after = set().union(*paths2)
    assert 'b' in blocks_after


# ---------------------------------- cluster ---------------------------------


def test_auto_k() -> None:
    """auto_k is singleton-per-path by default — every sampled path is
    its own cluster. The strategy doc's old heuristic (max(3, N/4)) is
    deprecated in favor of bottom-up: solve paths, harvest cores."""
    assert auto_k(0) == 0
    assert auto_k(4) == 4
    assert auto_k(40) == 40


def test_hamming_set_distance() -> None:
    assert hamming_set_distance(frozenset('abc'), frozenset('abc')) == 0
    assert hamming_set_distance(frozenset('abc'), frozenset('abd')) == 2
    assert hamming_set_distance(frozenset(), frozenset('abc')) == 3


def test_cluster_paths_basic() -> None:
    # Two well-separated groups; k=2 should split them cleanly.
    paths = [
        ['e', 'a', 'b', 'c'],
        ['e', 'a', 'b', 'c'],
        ['e', 'x', 'y', 'z'],
        ['e', 'x', 'y', 'z'],
    ]
    clusters = cluster_paths(paths, k=2, seed=1)
    assert len(clusters) == 2
    sizes = sorted(len(c.members) for c in clusters)
    assert sizes == [2, 2]


def test_cluster_paths_empty() -> None:
    assert cluster_paths([], k=3) == []
    # k=0 is also empty.
    assert cluster_paths([['a']], k=0) == []


# ------------------------------- completeness -------------------------------


def test_edge_var_roundtrip() -> None:
    assert edge_var('0_0_1', '4_2_3') == 'e_0_0_1__TO__4_2_3'
    pair = parse_edge_var('e_0_0_1__TO__4_2_3')
    assert pair == ('0_0_1', '4_2_3')
    assert parse_edge_var('BLK_x') is None


def test_emit_probe_well_formed() -> None:
    g = nx.DiGraph()
    g.add_edges_from([('e', 'a'), ('a', 'c'), ('e', 'b'), ('b', 'c')])
    info = _fake_info(g, 'e', 'c')

    probe = emit_probe(info)
    # All blocks declared.
    for b in ('e', 'a', 'b', 'c'):
        assert f'(declare-const BLK_{b} Bool)' in probe.smt2
    # Entry and assert pinned.
    assert '(assert BLK_e)' in probe.smt2
    assert '(assert BLK_c)' in probe.smt2
    # Edge vars present.
    assert 'e_e__TO__a' in probe.smt2
    assert 'e_a__TO__c' in probe.smt2
    # Logic set.
    assert '(set-logic ALL)' in probe.smt2


def test_emit_probe_with_clusters() -> None:
    g = nx.DiGraph()
    g.add_edges_from([('e', 'a'), ('a', 'c'), ('e', 'b'), ('b', 'c')])
    info = _fake_info(g, 'e', 'c')
    keep_A = frozenset({'e', 'a', 'c'})
    probe = emit_probe(info, cluster_keeps=[keep_A])
    # Drop set = {b} → escape constraint on BLK_b.
    assert 'at-least 1' in probe.smt2
    assert 'BLK_b' in probe.smt2


def test_parse_true_edge_vars() -> None:
    model = """sat
(model
  (define-fun BLK_e () Bool true)
  (define-fun BLK_a () Bool true)
  (define-fun e_e__TO__a () Bool true)
  (define-fun e_a__TO__c () Bool true)
  (define-fun e_e__TO__b () Bool false)
)
"""
    edges = parse_true_edge_vars(model)
    assert edges == {('e', 'a'), ('a', 'c')}


def test_derive_path_from_model() -> None:
    g = nx.DiGraph()
    g.add_edges_from([('e', 'a'), ('a', 'c'), ('e', 'b'), ('b', 'c')])
    info = _fake_info(g, 'e', 'c')
    model = (
        '(model'
        ' (define-fun e_e__TO__a () Bool true)'
        ' (define-fun e_a__TO__c () Bool true)'
        ' (define-fun e_e__TO__b () Bool false)'
        ')'
    )
    p = derive_path_from_model(info, model)
    assert p == ['e', 'a', 'c']


# -------------------------------- core_blocks -------------------------------


def test_parse_core_basic() -> None:
    out = (
        'unsat\n'
        '(\n'
        '  _0_0_0_0_0_0__1_assume\n'
        '  _4_2_1_0_0_0__9_lemma\n'
        '  bytemap_select_range_3\n'
        ')\n'
    )
    names = parse_core(out)
    assert names == [
        '_0_0_0_0_0_0__1_assume',
        '_4_2_1_0_0_0__9_lemma',
        'bytemap_select_range_3',
    ]


def test_core_to_blocks_skips_universal() -> None:
    blocks = core_to_blocks([
        '_0_0_0_0_0_0__1_assume',
        'bytemap_select_range_3',
        'dynamic_def_0',
        '_4_2_1_0_0_0__9_lemma',
    ])
    assert blocks == {'0_0_0_0_0_0', '4_2_1_0_0_0'}


def test_core_blocks_from_stdout() -> None:
    out = (
        'unsat\n'
        '(_3_0_0_0_0_0__1_assume bytemap_select_range_5)\n'
    )
    assert core_blocks_from_stdout(out) == {'3_0_0_0_0_0'}
