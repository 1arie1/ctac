"""Tests for the ``MapChain`` data structure (Store-over-Store reduction
support; see ``src/ctac/smt/encoding/map_chain.py``)."""

from __future__ import annotations

from ctac.ast.nodes import ConstExpr, SymbolRef
from ctac.smt.encoding.map_chain import (
    KV,
    MapChain,
    NamedMap,
    OpaqueRef,
    chain_opaque_self,
    prune,
    reachable_named_targets,
    store,
)


def _const(v: str) -> ConstExpr:
    return ConstExpr(value=v)


def _sym(name: str) -> SymbolRef:
    return SymbolRef(name=name)


def test_chain_opaque_self_is_terminal_only() -> None:
    c = chain_opaque_self("M0")
    assert c.entries == (OpaqueRef("M0"),)
    assert c.active_keys == frozenset()
    assert c.has_symbolic_key is False
    assert c.terminal == OpaqueRef("M0")


def test_store_no_shadow_uses_named_map_tail() -> None:
    """First Store on a havoc leaf produces the canonical shared-sibling form."""
    registry: dict[str, MapChain] = {}
    registry["M0"] = chain_opaque_self("M0")
    m1 = store(registry["M0"], _const("0x10"), _const("0x42"), owner="M0", registry=registry)
    registry["M1"] = m1
    assert m1.entries == (KV(_const("0x10"), _const("0x42")), NamedMap("M0"))
    assert m1.active_keys == frozenset({"0x10"})
    assert m1.has_symbolic_key is False


def test_chained_stores_share_predecessor_by_name() -> None:
    """Linear no-shadow chain: each new chain references the previous via NamedMap."""
    registry: dict[str, MapChain] = {"M0": chain_opaque_self("M0")}
    registry["M1"] = store(registry["M0"], _const("0x10"), _const("1"), owner="M0", registry=registry)
    registry["M2"] = store(registry["M1"], _const("0x20"), _const("2"), owner="M1", registry=registry)
    registry["M3"] = store(registry["M2"], _const("0x30"), _const("3"), owner="M2", registry=registry)

    assert registry["M2"].entries == (KV(_const("0x20"), _const("2")), NamedMap("M1"))
    assert registry["M3"].entries == (KV(_const("0x30"), _const("3")), NamedMap("M2"))
    # Active keys propagate transitively through NamedMap.
    assert registry["M3"].active_keys == frozenset({"0x10", "0x20", "0x30"})


def test_store_at_same_key_prunes_and_inlines() -> None:
    """`M2 = M1[k := v_new]` where M1 has KV(k, v_old) drops the dead KV.
    M2 must not reference M1 (M1's KV was shadowed), but its tail can
    use either NamedMap(M0) or OpaqueRef(M0) — both render to ``(M0 idx)``
    at emit time. The short-circuited recursion in M0's chain keeps the
    NamedMap entry."""
    registry: dict[str, MapChain] = {"M0": chain_opaque_self("M0")}
    registry["M1"] = store(registry["M0"], _const("0x10"), _const("v1"), owner="M0", registry=registry)
    registry["M2"] = store(registry["M1"], _const("0x10"), _const("v_new"), owner="M1", registry=registry)
    assert registry["M2"].entries == (
        KV(_const("0x10"), _const("v_new")),
        NamedMap("M0"),
    )
    # Crucially, M2 does NOT reference M1.
    assert NamedMap("M1") not in registry["M2"].entries


def test_recursive_prune_through_named_map() -> None:
    """Pruning recurses through NamedMap when active_keys says k is present."""
    registry: dict[str, MapChain] = {"M0": chain_opaque_self("M0")}
    registry["M1"] = store(registry["M0"], _const("0x10"), _const("v1"), owner="M0", registry=registry)
    registry["M2"] = store(registry["M1"], _const("0x20"), _const("v2"), owner="M1", registry=registry)
    # M2 = [KV(0x20, v2), NamedMap(M1)]; M1 = [KV(0x10, v1), NamedMap(M0)].
    # Now M3 stores at 0x10 — shadowing M1's KV. M2 doesn't have 0x10
    # locally, but M1 (via NamedMap) does. Recursion finds it.
    registry["M3"] = store(registry["M2"], _const("0x10"), _const("v_new"), owner="M2", registry=registry)
    # After recursion, M1's pruned form is [NamedMap(M0)] (KV(0x10, v1)
    # dropped). M2's chain inlines that, giving:
    #   [KV(0x20, v2), NamedMap(M0)]
    # Then M3 = [KV(0x10, v_new), KV(0x20, v2), NamedMap(M0)].
    assert registry["M3"].entries == (
        KV(_const("0x10"), _const("v_new")),
        KV(_const("0x20"), _const("v2")),
        NamedMap("M0"),
    )


def test_active_keys_short_circuits_walk() -> None:
    """Constant k not in active_keys and no symbolic keys → prune returns self."""
    registry: dict[str, MapChain] = {"M0": chain_opaque_self("M0")}
    registry["M1"] = store(registry["M0"], _const("0x10"), _const("v1"), owner="M0", registry=registry)
    registry["M2"] = store(registry["M1"], _const("0x20"), _const("v2"), owner="M1", registry=registry)
    # 0x99 is not in active_keys; chain has no symbolic keys.
    pruned = prune(registry["M2"], _const("0x99"), registry=registry)
    assert pruned is registry["M2"]


def test_symbolic_key_does_not_prune() -> None:
    """Sym vs sym (different SymRefs) returns _key_relation == "unknown" → no prune."""
    registry: dict[str, MapChain] = {"M0": chain_opaque_self("M0")}
    registry["M1"] = store(registry["M0"], _sym("R_a"), _const("v1"), owner="M0", registry=registry)
    registry["M2"] = store(registry["M1"], _sym("R_b"), _const("v2"), owner="M1", registry=registry)
    # No pruning expected — R_a and R_b are different SymRefs (relation "unknown").
    assert registry["M2"].entries == (KV(_sym("R_b"), _const("v2")), NamedMap("M1"))


def test_symbolic_key_syntactic_equality_prunes() -> None:
    """Same SymRef on both sides → relation "eq" → prune. M2 must not
    reference M1 (M1's KV(R_a, v1) was shadowed)."""
    registry: dict[str, MapChain] = {"M0": chain_opaque_self("M0")}
    registry["M1"] = store(registry["M0"], _sym("R_a"), _const("v1"), owner="M0", registry=registry)
    registry["M2"] = store(registry["M1"], _sym("R_a"), _const("v_new"), owner="M1", registry=registry)
    assert registry["M2"].entries == (
        KV(_sym("R_a"), _const("v_new")),
        NamedMap("M0"),
    )
    assert NamedMap("M1") not in registry["M2"].entries


def test_constant_key_text_mismatch_does_not_prune() -> None:
    """`0x4` and `4` are textually distinct ConstExprs; `_key_relation`
    returns "neq" so they're treated as definitely-distinct, no prune."""
    registry: dict[str, MapChain] = {"M0": chain_opaque_self("M0")}
    registry["M1"] = store(registry["M0"], _const("0x4"), _const("v1"), owner="M0", registry=registry)
    registry["M2"] = store(registry["M1"], _const("4"), _const("v2"), owner="M1", registry=registry)
    # Two distinct ConstExpr.value texts → no shadow.
    assert registry["M2"].entries == (KV(_const("4"), _const("v2")), NamedMap("M1"))


def test_prune_with_symbolic_chain_walks_anyway() -> None:
    """When the chain has a symbolic KV, the active_keys short-circuit
    is bypassed and prune walks normally (only finds true syntactic-eq matches)."""
    registry: dict[str, MapChain] = {"M0": chain_opaque_self("M0")}
    registry["M1"] = store(registry["M0"], _sym("R_a"), _const("v1"), owner="M0", registry=registry)
    # Now ask to prune key 0x99 which isn't anywhere — but chain has
    # `has_symbolic_key=True`, so we walk. No KV matches "eq". Returns self.
    pruned = prune(registry["M1"], _const("0x99"), registry=registry)
    assert pruned is registry["M1"]


def test_active_keys_propagates_through_named_map() -> None:
    """Parent's active_keys ⊇ NamedMap-pointed-to chain's active_keys."""
    registry: dict[str, MapChain] = {"M0": chain_opaque_self("M0")}
    registry["M1"] = store(registry["M0"], _const("0x10"), _const("v1"), owner="M0", registry=registry)
    registry["M2"] = store(registry["M1"], _const("0x20"), _const("v2"), owner="M1", registry=registry)
    assert registry["M2"].active_keys == frozenset({"0x10", "0x20"})
    # M1's keys are reached via NamedMap recursion in the cache build.


def test_reachable_named_targets() -> None:
    registry: dict[str, MapChain] = {"M0": chain_opaque_self("M0")}
    registry["M1"] = store(registry["M0"], _const("0x10"), _const("v1"), owner="M0", registry=registry)
    targets = reachable_named_targets(registry["M1"])
    # M1 = [KV, NamedMap(M0)] — only M0 is named.
    assert targets == ("M0",)


def test_reachable_named_targets_after_inlining() -> None:
    """After pruning, M2's tail is the deeper survivor (not the
    immediate predecessor M1). `reachable_named_targets` reports both
    NamedMap and OpaqueRef entries uniformly."""
    registry: dict[str, MapChain] = {"M0": chain_opaque_self("M0")}
    registry["M1"] = store(registry["M0"], _const("0x10"), _const("v1"), owner="M0", registry=registry)
    registry["M2"] = store(registry["M1"], _const("0x10"), _const("v_new"), owner="M1", registry=registry)
    # M2's chain references M0 (not M1, because M1's KV was shadowed).
    assert reachable_named_targets(registry["M2"]) == ("M0",)
