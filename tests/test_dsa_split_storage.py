"""Tests for the DSA-aware split storage adapter."""

from __future__ import annotations

from ctac.analysis.abs_int.storage import (
    DsaSplitState,
    DsaSplitStorage,
    Lattice,
)
from ctac.analysis.model import DsaDynamicAssignment, DsaResult


# A toy lattice over `frozenset[int]`: meet=intersection, join=union.
# Concrete enough to test routing without depending on the interval
# domain itself.
_TOP: frozenset[int] = frozenset()  # empty set acts as TOP for these tests


def _meet(a: frozenset[int], b: frozenset[int]) -> frozenset[int]:
    if a == _TOP:
        return b
    if b == _TOP:
        return a
    return a & b


def _join(a: frozenset[int], b: frozenset[int]) -> frozenset[int]:
    if a == _TOP or b == _TOP:
        return _TOP
    return a | b


_LATTICE: Lattice[frozenset[int]] = Lattice(top=_TOP, meet=_meet, join=_join)


def _dsa(dynamic: list[str]) -> DsaResult:
    """Synthesize a DsaResult flagging the given symbols as DSA-dynamic."""
    assignments = tuple(
        DsaDynamicAssignment(
            symbol=sym,
            block_id="B?",
            cmd_index=0,
            cmd_kind="AssignHavocCmd",
            raw=f"AssignHavocCmd {sym}",
            sibling_defs=("B?:0",),
        )
        for sym in dynamic
    )
    return DsaResult(issues=(), dynamic_assignments=assignments)


def _storage(dynamic: list[str]) -> DsaSplitStorage[frozenset[int]]:
    return DsaSplitStorage(_dsa(dynamic), _LATTICE)


def test_lookup_returns_top_for_unknown_var() -> None:
    storage = _storage([])
    state = storage.initial_state()
    assert storage.get(state, "X") == _TOP


def test_lookup_local_takes_precedence_over_static() -> None:
    storage = _storage([])
    state = storage.initial_state()
    state.static["X"] = frozenset({1, 2, 3})
    state.local["X"] = frozenset({1})
    assert storage.get(state, "X") == frozenset({1})


def test_lookup_falls_through_to_static() -> None:
    storage = _storage([])
    state = storage.initial_state()
    state.static["X"] = frozenset({1, 2, 3})
    assert storage.get(state, "X") == frozenset({1, 2, 3})


def test_write_def_routes_dsa_static_to_static_map() -> None:
    storage = _storage([])  # X is DSA-static
    state = storage.initial_state()
    storage.write_def(state, "X", frozenset({7}))
    assert state.static["X"] == frozenset({7})
    assert "X" not in state.local


def test_write_def_routes_dsa_dynamic_to_local() -> None:
    storage = _storage(["X"])
    state = storage.initial_state()
    storage.write_def(state, "X", frozenset({7}))
    assert state.local["X"] == frozenset({7})
    assert "X" not in state.static


def test_refine_does_not_mutate_static() -> None:
    """Crux of the contract — refining a DSA-static var must NOT change
    the universal value. The refinement is block-local."""
    storage = _storage([])  # X is DSA-static
    state = storage.initial_state()
    state.static["X"] = frozenset({1, 2, 3})
    storage.refine(state, "X", frozenset({1, 2}))
    assert state.static["X"] == frozenset({1, 2, 3})  # untouched
    assert state.local["X"] == frozenset({1, 2})  # tightened locally
    assert storage.get(state, "X") == frozenset({1, 2})  # local wins


def test_refine_intersects_with_existing_view() -> None:
    storage = _storage([])
    state = storage.initial_state()
    state.local["X"] = frozenset({1, 2, 3, 4})
    storage.refine(state, "X", frozenset({2, 3, 5}))
    assert state.local["X"] == frozenset({2, 3})


def test_propagate_carries_local_in_a_fresh_dict() -> None:
    """Edits to the destination's local must not leak back to the source."""
    storage = _storage([])
    src = storage.initial_state()
    src.local["X"] = frozenset({1, 2})
    dst = storage.propagate(src)
    assert dst.local == src.local
    assert dst.local is not src.local
    dst.local["Y"] = frozenset({9})
    assert "Y" not in src.local
    assert dst.static is src.static  # static stays shared


def test_propagate_carries_dsa_dynamic_values() -> None:
    storage = _storage(["X"])
    src = storage.initial_state()
    storage.write_def(src, "X", frozenset({7}))
    dst = storage.propagate(src)
    assert storage.get(dst, "X") == frozenset({7})


def test_join_lubs_local_entries_across_predecessors() -> None:
    storage = _storage([])
    p1 = storage.initial_state()
    p2 = storage.initial_state()
    p1.local["X"] = frozenset({1, 2})
    p2.local["X"] = frozenset({2, 3})
    joined = storage.join([p1, p2])
    assert joined.local["X"] == frozenset({1, 2, 3})


def test_join_when_only_one_pred_has_local_falls_through_to_static() -> None:
    storage = _storage([])
    p1 = storage.initial_state()
    p2 = storage.initial_state()
    # p1 refines X to {1, 2}; p2 has no local entry — falls through to
    # static["X"] = {1, 2, 3, 4}. Join: {1, 2} ∪ {1, 2, 3, 4} = {1..4}.
    p1.static["X"] = frozenset({1, 2, 3, 4})
    p1.local["X"] = frozenset({1, 2})
    joined = storage.join([p1, p2])
    assert joined.local["X"] == frozenset({1, 2, 3, 4})
    # Static stays untouched after join.
    assert joined.static is p1.static
    assert joined.static["X"] == frozenset({1, 2, 3, 4})


def test_join_with_unknown_in_one_pred_yields_top() -> None:
    """When one predecessor has no view at all (no local, no static),
    its contribution is TOP, and join with TOP gives TOP."""
    storage = _storage([])
    p1 = storage.initial_state()
    p2 = storage.initial_state()
    p1.local["X"] = frozenset({1, 2})
    # p2 has nothing — get(p2, "X") == TOP. Join({1,2}, TOP) = TOP.
    joined = storage.join([p1, p2])
    assert joined.local["X"] == _TOP


def test_join_singleton_returns_a_propagated_copy() -> None:
    """A single-predecessor join shouldn't share the local dict."""
    storage = _storage([])
    p = storage.initial_state()
    p.local["X"] = frozenset({1})
    joined = storage.join([p])
    assert joined.local == p.local
    assert joined.local is not p.local


def test_static_dict_shared_across_states() -> None:
    """Mutating static via one state is visible from any other state
    derived from the same storage — that's the universal-value
    contract."""
    storage = _storage([])
    s1 = storage.initial_state()
    s2 = storage.propagate(s1)
    storage.write_def(s1, "X", frozenset({42}))
    assert storage.get(s2, "X") == frozenset({42})


def test_is_dsa_dynamic_classification() -> None:
    storage = _storage(["A", "B"])
    assert storage.is_dsa_dynamic("A")
    assert storage.is_dsa_dynamic("B")
    assert not storage.is_dsa_dynamic("C")


def test_initial_state_has_empty_local() -> None:
    storage = _storage([])
    state = storage.initial_state()
    assert state.local == {}
    assert isinstance(state, DsaSplitState)
