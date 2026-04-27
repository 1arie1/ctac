"""DSA-aware split storage for non-relational abs_int domains.

Storage strategy 2 from `analysis/abs_int/__init__.py`'s ladder:

- ``static: dict[var, V]`` — every DSA-static var's universal value.
  One shared dict referenced by every block's state. Written once at
  the var's def site (any block), never mutated thereafter.
- ``local: dict[var, V]`` — per-block view, holding two kinds of
  entries that share the same lifecycle:
    * DSA-dynamic var values, written at the def site.
    * Refinements of any var (static or dynamic) from
      ``refine_assume`` at this block.
  Both kinds propagate, join, and look up identically — no need to
  separate them.

Lookup precedence at block B: ``local[var]`` → ``static[var]`` → top.

The DSA classification mirrors `ctac.rewrite.context.RewriteCtx`
(``src/ctac/rewrite/context.py:159``): a var is DSA-dynamic iff it
appears in ``DsaResult.dynamic_assignments``; otherwise (with at
least one definition) it's DSA-static.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass, field
from typing import Generic, TypeVar

from ctac.analysis.model import DsaResult

V = TypeVar("V")


@dataclass(frozen=True)
class Lattice(Generic[V]):
    """Per-domain operations the storage needs to merge / refine values."""

    top: V
    meet: Callable[[V, V], V]
    join: Callable[[V, V], V]


@dataclass
class DsaSplitState(Generic[V]):
    """One block's view: shared ``static`` dict + this block's ``local``.

    The framework's frontier holds one ``DsaSplitState`` per block. The
    ``static`` field is the *same dict object* across every state in
    the run — sharing is intentional because static is universal.
    Each block has its own ``local`` dict.
    """

    static: dict[str, V]
    local: dict[str, V] = field(default_factory=dict)


class DsaSplitStorage(Generic[V]):
    """Helpers the domain calls from `transfer` / `propagate` / `join`.

    The storage owns the static-vs-dynamic classification (built once
    from the program's ``DsaResult``) and the lattice ops (passed in
    as a ``Lattice``). All state mutations route through here so the
    domain code stays small and the static-not-mutated-by-refinement
    invariant is enforced in one place.
    """

    def __init__(
        self,
        dsa: DsaResult,
        lattice: Lattice[V],
    ) -> None:
        self._dsa_dynamic: frozenset[str] = frozenset(
            a.symbol for a in dsa.dynamic_assignments
        )
        self._lattice = lattice
        self._shared_static: dict[str, V] = {}

    @property
    def dsa_dynamic(self) -> frozenset[str]:
        return self._dsa_dynamic

    def is_dsa_dynamic(self, var: str) -> bool:
        return var in self._dsa_dynamic

    def initial_state(self) -> DsaSplitState[V]:
        """Produce the entry block's state. Subsequent states share the
        same ``static`` dict object (mutations are universally visible
        — which is the contract for static)."""
        return DsaSplitState(static=self._shared_static, local={})

    def get(self, state: DsaSplitState[V], var: str) -> V:
        """Look up ``var`` at the block this state represents.

        Precedence: ``local`` → ``static`` → ``top``.
        """
        if var in state.local:
            return state.local[var]
        if var in state.static:
            return state.static[var]
        return self._lattice.top

    def write_def(self, state: DsaSplitState[V], var: str, value: V) -> None:
        """Record a definition (from ``AssignExpCmd``/``AssignHavocCmd``).
        Routes by DSA classification: DSA-dynamic → ``local``,
        DSA-static → shared ``static``.
        """
        if var in self._dsa_dynamic:
            state.local[var] = value
        else:
            state.static[var] = value

    def refine(self, state: DsaSplitState[V], var: str, refinement: V) -> None:
        """Layer a refinement (from ``refine_assume``) at this block.

        Always writes to ``state.local[var]`` — never to ``static`` —
        so the universal value of a DSA-static var stays untouched even
        when a non-entry assume tightens it at one block. The stored
        value is the meet of the existing block-view and the refinement,
        so refinement is monotone."""
        current = self.get(state, var)
        state.local[var] = self._lattice.meet(current, refinement)

    def refine_static(self, state: DsaSplitState[V], var: str, refinement: V) -> None:
        """Meet a refinement into the shared ``static`` map.

        Caller's responsibility: only invoke when the refinement is
        *universally* true (e.g. when it arises in the entry block,
        which dominates every reachable block, on a DSA-static var).
        Promotes the fact out of per-block storage and into the
        universal value, which both saves storage (no duplication
        across downstream blocks) and gives a cleaner materialization
        output (universal facts emit once, at the entry's end).
        """
        current = state.static.get(var, self._lattice.top)
        state.static[var] = self._lattice.meet(current, refinement)

    def propagate(
        self, src: DsaSplitState[V], dst_local: dict[str, V] | None = None
    ) -> DsaSplitState[V]:
        """Carry state along an edge ``src -> dst``.

        Copies ``src.local`` (a fresh dict so the destination's later
        edits don't bleed back) and shares ``static``. ``dst_local``
        lets the caller seed extra entries before the copy (rarely
        needed; the typical call passes ``None``).
        """
        new_local: dict[str, V] = dict(src.local)
        if dst_local:
            new_local.update(dst_local)
        return DsaSplitState(static=src.static, local=new_local)

    def join(self, states: list[DsaSplitState[V]]) -> DsaSplitState[V]:
        """Merge multiple incoming states at a join point.

        ``static`` is shared (any of the inputs has the same dict
        reference). ``local`` is the lattice ``join`` over the inputs'
        local maps, evaluated at every var that appears in at least one
        input's local. For a var present in only some inputs, the
        absent inputs contribute the value the read-path would return
        (``static[var]`` if DSA-static, else ``top``) — that's exactly
        what the read-path yields and exactly what the convex-hull join
        needs.
        """
        if not states:
            return DsaSplitState(static=self._shared_static, local={})
        if len(states) == 1:
            return self.propagate(states[0])
        static = states[0].static
        joined_local: dict[str, V] = {}
        all_keys: set[str] = set()
        for s in states:
            all_keys.update(s.local.keys())
        for var in all_keys:
            acc: V | None = None
            for s in states:
                v = s.local.get(var)
                if v is None:
                    # Absent in this input — fall through to static or top.
                    v = s.static.get(var, self._lattice.top)
                acc = v if acc is None else self._lattice.join(acc, v)
            assert acc is not None
            joined_local[var] = acc
        return DsaSplitState(static=static, local=joined_local)
