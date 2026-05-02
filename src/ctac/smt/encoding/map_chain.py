"""Per-map chain data structures for sea_vc's Store-over-Store reduction.

A ``MapChain`` is an immutable list of entries that summarize how a
bytemap symbol was constructed by a sequence of ``Store`` operations
on top of some base map. Three entry types:

* ``KV(k, v)`` — a Store at key ``k`` of value ``v``.
* ``NamedMap(name)`` — a transparent reference: the rest of the chain
  is whatever ``MapChain[name]`` says. Pruning may recurse through
  this entry. At emit time it produces ``(name idx)``.
* ``OpaqueRef(name)`` — a terminal: the rest of the chain is whatever
  the SMT-level function ``name`` says, but we won't introspect.
  Used for havoc-leaf maps (self-reference), Ite-anchored maps, and
  DSA-dynamic merged maps. At emit time it produces ``(name idx)``.

Each chain ends in exactly one terminal (``NamedMap`` or
``OpaqueRef``); KVs only appear before the terminal.

Sharing is structural: ``[KV(k, v), NamedMap(M_old)]`` is the
canonical "shared sibling" form for ``M_new = Store(M_old, k, v)``
when no key was shadowed. At emit time this becomes
``(ite (= idx k) v (M_old idx))``. When pruning fires (``store(k, v)``
with ``k`` already in the predecessor chain), the entries are
inlined past the share boundary.

Soundness rests on the array Store/Select axiom:
    Select(Store(M, k, v), idx) = ite(idx == k, v, Select(M, idx))
Repeated application of this axiom (read top-down through a chain)
gives the same value regardless of whether the chain is referenced
by name or inlined; pruning by syntactic key-equality is also sound
because a later Store at the same key shadows any earlier value at
that key in any execution.

Pure / I/O-free. The ``registry: dict[str, MapChain]`` is passed to
recursive operations to avoid module-level state."""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Union

from ctac.ast.nodes import ConstExpr, TacExpr
from ctac.rewrite.rules.select_over_store import (
    _const_value,
    _key_relation,
)


@dataclass(frozen=True)
class KV:
    k: TacExpr
    v: TacExpr


@dataclass(frozen=True)
class NamedMap:
    name: str


@dataclass(frozen=True)
class OpaqueRef:
    name: str


Entry = Union[KV, NamedMap, OpaqueRef]


def _key_text(k: TacExpr) -> str | None:
    """Return a canonical text form for a constant key, or None if
    the key is symbolic. Two ConstExprs with different ``.value`` text
    (e.g. ``0x4`` vs ``4``) hash to different texts; we don't try to
    reason about their numeric equality here — :func:`_key_relation`
    handles that conservatively."""
    if not isinstance(k, ConstExpr):
        return None
    return _const_value(k)


@dataclass(frozen=True)
class MapChain:
    """Immutable chain. ``entries[-1]`` is always a terminal
    (``NamedMap`` or ``OpaqueRef``); the entries before it are
    ``KV``s.

    Caches:
    * ``active_keys`` — set of canonical const-key texts present in
      the chain's reachable KVs (following NamedMap recursively,
      stopping at OpaqueRef).
    * ``has_symbolic_key`` — whether any KV in the reachable chain
      has a non-constant key.

    The caches let ``prune(k)`` short-circuit when ``k`` is a
    constant whose text doesn't appear in ``active_keys`` and the
    chain has no symbolic keys — guaranteeing no entry could match
    by ``_key_relation == "eq"``."""

    entries: tuple[Entry, ...]
    active_keys: frozenset[str] = field(default_factory=frozenset)
    has_symbolic_key: bool = False

    @property
    def terminal(self) -> Entry:
        return self.entries[-1]

    def kvs(self) -> tuple[KV, ...]:
        return tuple(e for e in self.entries if isinstance(e, KV))


def chain_opaque_self(name: str) -> MapChain:
    """Build the opaque self-referential chain for a havoc-leaf,
    Ite-anchored, or DSA-dynamic map: ``[OpaqueRef(name)]``."""
    return MapChain(entries=(OpaqueRef(name),))


def _compute_caches(
    entries: tuple[Entry, ...], registry: dict[str, "MapChain"]
) -> tuple[frozenset[str], bool]:
    """Compute (active_keys, has_symbolic_key) over the reachable chain."""
    keys: set[str] = set()
    has_sym = False
    for e in entries:
        if isinstance(e, KV):
            t = _key_text(e.k)
            if t is None:
                has_sym = True
            else:
                keys.add(t)
        elif isinstance(e, NamedMap):
            sub = registry.get(e.name)
            if sub is None:
                # Forward reference — should not happen if chains are
                # constructed in source order. Treat conservatively
                # (could-be-anything) by flagging symbolic.
                has_sym = True
            else:
                keys.update(sub.active_keys)
                has_sym = has_sym or sub.has_symbolic_key
        # OpaqueRef contributes nothing.
    return frozenset(keys), has_sym


def _build(
    entries: tuple[Entry, ...], registry: dict[str, MapChain]
) -> MapChain:
    keys, has_sym = _compute_caches(entries, registry)
    return MapChain(entries=entries, active_keys=keys, has_symbolic_key=has_sym)


def prune(chain: MapChain, k: TacExpr, *, registry: dict[str, MapChain]) -> MapChain:
    """Return a new ``MapChain`` with every reachable KV whose key
    relates to ``k`` via ``_key_relation == "eq"`` removed.

    Returns ``chain`` itself (referential identity) when no entry was
    dropped — callers can detect "no shadow" with ``result is chain``.

    Recursion follows ``NamedMap`` entries; ``OpaqueRef`` is a hard
    boundary (no recursion). The ``active_keys`` cache short-circuits
    the walk when ``k`` is a constant provably not present in the
    reachable KVs."""
    # Quick reject: constant k not in active_keys, and no symbolic
    # KVs in the chain — provably no `_key_relation == "eq"` will
    # fire under the conservative comparison.
    k_text = _key_text(k)
    if k_text is not None and not chain.has_symbolic_key and k_text not in chain.active_keys:
        return chain

    new_entries: list[Entry] = []
    changed = False
    for entry in chain.entries:
        if isinstance(entry, KV):
            if _key_relation(entry.k, k) == "eq":
                changed = True
                continue
            new_entries.append(entry)
        elif isinstance(entry, NamedMap):
            sub = registry.get(entry.name)
            if sub is None:
                # Forward reference / unknown — keep entry conservatively.
                new_entries.append(entry)
                continue
            sub_pruned = prune(sub, k, registry=registry)
            if sub_pruned is sub:
                new_entries.append(entry)
            else:
                # Inline the pruned chain in place of the NamedMap.
                new_entries.extend(sub_pruned.entries)
                changed = True
        elif isinstance(entry, OpaqueRef):
            # Terminal boundary; pruning never recurses past it.
            new_entries.append(entry)
        else:  # pragma: no cover
            raise TypeError(f"unknown entry kind: {type(entry).__name__}")

    if not changed:
        return chain
    return _build(tuple(new_entries), registry)


def store(
    chain: MapChain,
    k: TacExpr,
    v: TacExpr,
    *,
    owner: str,
    registry: dict[str, MapChain],
) -> MapChain:
    """Build the chain for ``M_new = Store(M_old, k, v)`` where
    ``chain == registry[owner]`` is M_old's current chain.

    If ``prune(chain, k)`` returns ``chain`` (no shadow), the result is
    the canonical shared-sibling form ``[KV(k, v), NamedMap(owner)]``
    — sharing M_old by name. Otherwise the result inlines the pruned
    entries: ``[KV(k, v), <pruned entries>]``."""
    pruned = prune(chain, k, registry=registry)
    if pruned is chain:
        new_entries: tuple[Entry, ...] = (KV(k, v), NamedMap(owner))
    else:
        new_entries = (KV(k, v),) + pruned.entries
    return _build(new_entries, registry)


def reachable_named_targets(chain: MapChain) -> tuple[str, ...]:
    """Return the set of names referenced by a ``NamedMap`` or
    ``OpaqueRef`` entry in this chain. Used by the live-set closure
    in sea_vc's emission."""
    out: list[str] = []
    seen: set[str] = set()
    for entry in chain.entries:
        if isinstance(entry, (NamedMap, OpaqueRef)):
            if entry.name not in seen:
                seen.add(entry.name)
                out.append(entry.name)
    return tuple(out)
