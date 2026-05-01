"""Read-only context object that rules query to make rewriting decisions.

Provides:
    - ``is_static(var)``: ``var`` is DSA-static (has at least one definition and
      is not in the DSA-dynamic set). Holds for both ``AssignExpCmd`` and
      ``AssignHavocCmd`` unique defs.
    - ``definition(var)``: the RHS of ``var``'s unique ``AssignExpCmd`` definition,
      or ``None`` (havoc-defined or multiply-defined symbols return ``None``).
    - ``lookthrough(expr)``: if ``expr`` is a :class:`SymbolRef` with a static
      RHS-valued definition, replace with the definition.
    - ``range(var)``: integer interval inferred from range-assume facts that
      dominate the current position (set via :meth:`set_position`).

Dominance is block-level; same-block assumes only apply if they appear
strictly before the query's ``cmd_index``. Block-level dominance is computed
from the CFG via :func:`networkx.immediate_dominators` walking the idom tree.
"""

from __future__ import annotations

from collections import defaultdict
from collections.abc import Callable, Sequence
from dataclasses import dataclass, field, replace

import networkx as nx

from ctac.analysis.defuse import extract_def_use
from ctac.analysis.model import DefUseResult, DsaResult
from ctac.analysis.passes import analyze_dsa
from ctac.analysis.symbols import canonical_symbol
from ctac.ast.nodes import (
    ApplyExpr,
    AssignExpCmd,
    AssignHavocCmd,
    AssumeExpCmd,
    JumpCmd,
    JumpiCmd,
    SymbolRef,
    TacCmd,
    TacExpr,
)
from ctac.ast.range_constraints import (
    SymbolIntervalConstraint,
    SymbolRelationConstraint,
    match_symbol_interval_constraint,
    match_symbol_relation_constraint,
)
from ctac.graph import Cfg
from ctac.ir.models import TacProgram

_STRIP_SUFFIXES = True
_NARROW_PREFIX = "safe_math_narrow_bv"

# Flipping the orientation of a relational op: `a op b` <=> `b flipped(op) a`.
_FLIP_REL_OP = {"<": ">", "<=": ">=", "==": "==", ">=": "<=", ">": "<"}


def _is_safe_narrow_apply(expr: TacExpr) -> bool:
    """``Apply(safe_math_narrow_bvN:bif, E)`` — pipeline-guaranteed empty cast.

    Semantically a range-checked Int -> bvN coercion; in this pipeline the
    runtime check is guaranteed to pass, so rules treat it as identity.
    """
    if not isinstance(expr, ApplyExpr) or expr.op != "Apply" or len(expr.args) != 2:
        return False
    fn = expr.args[0]
    if not isinstance(fn, SymbolRef):
        return False
    core = fn.name[:-4] if fn.name.endswith(":bif") else fn.name
    return core.startswith(_NARROW_PREFIX)


def _compute_dominators(program: TacProgram) -> dict[str, frozenset[str]]:
    """Block-level dominator sets, derived from networkx immediate dominators.

    Assumes a single entry block (first block in file order); TAC programs from
    the Certora pipeline conform to this.
    """
    if not program.blocks:
        return {}
    entry = program.blocks[0].id
    digraph = Cfg(program).to_digraph()
    idom = nx.immediate_dominators(digraph, entry)
    # Walk the idom tree to materialize full dominator sets.
    dom: dict[str, frozenset[str]] = {}

    def dominators_of(node: str) -> frozenset[str]:
        if node in dom:
            return dom[node]
        parent = idom.get(node, node)
        if parent == node:
            result = frozenset({node})
        else:
            result = frozenset({node}) | dominators_of(parent)
        dom[node] = result
        return result

    for node in digraph.nodes:
        dominators_of(node)
    return dom


@dataclass(frozen=True)
class _AssumeFact:
    block_id: str
    cmd_index: int
    interval: SymbolIntervalConstraint


@dataclass(frozen=True)
class _RelationFact:
    block_id: str
    cmd_index: int
    relation: SymbolRelationConstraint


@dataclass
class RewriteCtx:
    """Per-program view of def-use, DSA, dominance and range facts."""

    program: TacProgram
    ite_max_depth: int = 4
    fresh_counter_start: int = 0
    # Declared sort per symbol (e.g. ``"bv256"``, ``"int"``, ``"bool"``).
    # Optional; when empty, rules that rely on sort-based bounds fall back
    # to dominating assume-facts only.
    symbol_sorts: dict[str, str] = field(default_factory=dict)
    # When True, R6 emits ``Apply(safe_math_narrow_bv256:bif IntCeilDiv(...))``
    # instead of the legacy ``havoc + polynomial-bounds`` rewrite. The
    # IntCeilDiv concept is then axiomatized at the SMT layer (sea_vc).
    # Default-on; ``ctac rw --no-ceildiv-op`` flips it for benchmark
    # comparison against the legacy emission.
    use_int_ceil_div: bool = True
    du: DefUseResult = field(init=False)
    dsa: DsaResult = field(init=False)
    static_symbols: frozenset[str] = field(init=False)
    static_defs: dict[str, TacExpr] = field(init=False)
    assumes_by_symbol: dict[str, list[_AssumeFact]] = field(init=False)
    relations_by_pair: dict[tuple[str, str], list[_RelationFact]] = field(init=False)
    dominators: dict[str, frozenset[str]] = field(init=False)
    successors_by_block: dict[str, tuple[str, ...]] = field(init=False)
    entry_block_id: str | None = field(init=False)
    _cur_block: str | None = field(default=None, init=False)
    _cur_cmd: int | None = field(default=None, init=False)
    _cur_cmd_obj: TacCmd | None = field(default=None, init=False)
    _at_cmd_top: bool = field(default=False, init=False)
    _pending_entry_cmds: list[TacCmd] = field(default_factory=list, init=False)
    _pending_by_position: dict[tuple[str, int], list[TacCmd]] = field(
        default_factory=dict, init=False
    )
    _pending_symbols: list[tuple[str, str]] = field(default_factory=list, init=False)
    _pending_skips: set[tuple[str, int]] = field(default_factory=set, init=False)
    _fresh_counter: int = field(default=0, init=False)
    # Rules push human-readable diagnostics here when they decline to
    # rewrite for non-obvious reasons (e.g., insertion would break a
    # downstream invariant). The driver propagates these to
    # ``RewriteResult.warnings`` and the CLI prints them.
    warnings: list[str] = field(default_factory=list, init=False)

    def __post_init__(self) -> None:
        self.du = extract_def_use(self.program, strip_var_suffixes=_STRIP_SUFFIXES)
        self.dsa = analyze_dsa(
            self.program, strip_var_suffixes=_STRIP_SUFFIXES, def_use=self.du
        )
        dynamic_symbols = {a.symbol for a in self.dsa.dynamic_assignments}
        # DSA-static = has at least one definition and is not dynamic. This
        # covers both AssignExpCmd and AssignHavocCmd single-def cases.
        self.static_symbols = frozenset(
            sym for sym in self.du.definitions_by_symbol if sym not in dynamic_symbols
        )

        static_defs: dict[str, TacExpr] = {}
        by_id = self.program.block_by_id()
        for sym in self.static_symbols:
            defs = self.du.definitions_by_symbol[sym]
            if len(defs) != 1:
                continue
            ds = defs[0]
            block = by_id.get(ds.block_id)
            if block is None:
                continue
            cmd = block.commands[ds.cmd_index]
            if isinstance(cmd, AssignExpCmd):
                static_defs[sym] = cmd.rhs
        self.static_defs = static_defs

        assumes: dict[str, list[_AssumeFact]] = defaultdict(list)
        relations: dict[tuple[str, str], list[_RelationFact]] = defaultdict(list)
        for block in self.program.blocks:
            for idx, cmd in enumerate(block.commands):
                if not isinstance(cmd, AssumeExpCmd):
                    continue
                interval = match_symbol_interval_constraint(
                    cmd.condition, strip_var_suffixes=_STRIP_SUFFIXES,
                )
                if interval is not None:
                    assumes[interval.symbol].append(
                        _AssumeFact(block_id=block.id, cmd_index=idx, interval=interval)
                    )
                    continue
                rel = match_symbol_relation_constraint(
                    cmd.condition, strip_var_suffixes=_STRIP_SUFFIXES,
                )
                if rel is not None:
                    fact = _RelationFact(block_id=block.id, cmd_index=idx, relation=rel)
                    relations[(rel.left, rel.right)].append(fact)
                    # Mirror so lookups from either direction hit.
                    flipped_op = _FLIP_REL_OP[rel.op]
                    mirror = _RelationFact(
                        block_id=block.id,
                        cmd_index=idx,
                        relation=SymbolRelationConstraint(
                            left=rel.right, op=flipped_op, right=rel.left
                        ),
                    )
                    relations[(rel.right, rel.left)].append(mirror)
        self.assumes_by_symbol = assumes
        self.relations_by_pair = relations
        self.dominators = _compute_dominators(self.program)
        self.successors_by_block = {
            b.id: tuple(b.successors) for b in self.program.blocks
        }
        self.entry_block_id = self.program.blocks[0].id if self.program.blocks else None
        self._fresh_counter = self.fresh_counter_start

    def set_position(self, block_id: str | None, cmd_index: int | None) -> None:
        """Mark the program point the driver is currently rewriting under."""
        self._cur_block = block_id
        self._cur_cmd = cmd_index

    def set_host_cmd(self, cmd: TacCmd | None, *, at_top: bool) -> None:
        """Record the command whose expression is currently being rewritten.

        ``at_top`` is True when the rule is called on the outermost expression
        of the host command (RHS for :class:`AssignExpCmd`, condition for
        :class:`AssumeExpCmd`). Children of that expression are ``at_top=False``.
        Rules that want to replace the host command wholesale (e.g. R4a / R6
        reusing the LHS as the new havoc) check this flag.
        """
        self._cur_cmd_obj = cmd
        self._at_cmd_top = at_top

    def current_cmd(self) -> TacCmd | None:
        return self._cur_cmd_obj

    def at_cmd_top(self) -> bool:
        return self._at_cmd_top

    def skip_current_cmd(self) -> None:
        """Mark the current ``(block, cmd_index)`` as to-be-deleted.

        Used when a rule has queued replacement commands via
        :meth:`emit_fresh_var` (typically with ``reuse_name``) and the
        original command is no longer needed.
        """
        if self._cur_block is None or self._cur_cmd is None:
            return
        self._pending_skips.add((self._cur_block, self._cur_cmd))

    def is_static(self, var_name: str) -> bool:
        """True iff ``var_name`` is DSA-static (incl. havoc-only definitions)."""
        return canonical_symbol(var_name, strip_var_suffixes=_STRIP_SUFFIXES) in self.static_symbols

    def successors_of(self, block_id: str) -> tuple[str, ...]:
        """CFG successors of ``block_id`` (empty tuple for unknown / sinks)."""
        return self.successors_by_block.get(block_id, ())

    def definition(self, var_name: str) -> TacExpr | None:
        """RHS expression of ``var_name``'s unique AssignExpCmd definition, if any.

        Havoc-defined statics return ``None`` (no RHS to expand).
        """
        return self.static_defs.get(canonical_symbol(var_name, strip_var_suffixes=_STRIP_SUFFIXES))

    def lookthrough(self, expr: TacExpr) -> TacExpr:
        """Transitively peel away static defs and ``safe_math_narrow`` wrappers.

        Keeps unwrapping until neither applies, so a rule calling ``lookthrough``
        once on a ``SymbolRef`` whose definition is ``narrow(IntDiv(...))`` sees
        the ``IntDiv`` directly.

        Use for *matching* — when a rule wants to see through aliases to
        recognize a structural pattern. For *emission* use :meth:`peel_narrow`
        instead: it strips the pipeline-identity narrow wrapper but keeps
        :class:`SymbolRef` names intact, so emitted expressions preserve the
        syntactic link to existing variables and avoid creating complex
        monomials (e.g. ``Ite(...)``-shaped denominators) from inlining.
        """
        seen: set[TacExpr] = set()
        while expr not in seen:
            seen.add(expr)
            if isinstance(expr, SymbolRef):
                d = self.definition(expr.name)
                if d is not None:
                    expr = d
                    continue
            if _is_safe_narrow_apply(expr):
                assert isinstance(expr, ApplyExpr)
                expr = expr.args[1]
                continue
            break
        return expr

    def peel_narrow(self, expr: TacExpr) -> TacExpr:
        """Strip ``Apply(safe_math_narrow_bvN:bif, E)`` wrappers everywhere in ``expr``.

        Does NOT expand ``SymbolRef`` definitions — callers keep the named
        variable intact. Used by emission-side logic (R4a / R6 assume
        construction) to preserve syntactic references to existing
        registers while still treating narrow as an empty cast. Applies
        recursively so inner narrow wrappers inside compound expressions
        (e.g. ``IntMul(R53, narrow(I178))``) are also stripped.
        """
        # Peel any outer narrow first.
        while _is_safe_narrow_apply(expr):
            assert isinstance(expr, ApplyExpr)
            expr = expr.args[1]
        if isinstance(expr, ApplyExpr):
            new_args = tuple(self.peel_narrow(a) for a in expr.args)
            if new_args != expr.args:
                return replace(expr, args=new_args)
        return expr

    def symbol_sort(self, var_name: str) -> str | None:
        """Declared sort of ``var_name`` (e.g. ``"bv256"``), or ``None`` if unknown."""
        sym = canonical_symbol(var_name, strip_var_suffixes=_STRIP_SUFFIXES)
        return self.symbol_sorts.get(sym)

    def range(self, var_name: str) -> tuple[int | None, int | None] | None:
        """Return ``(lo, hi)`` interval inferred from dominating range-assume facts."""
        sym = canonical_symbol(var_name, strip_var_suffixes=_STRIP_SUFFIXES)
        facts = self.assumes_by_symbol.get(sym)
        if not facts:
            return None
        lo: int | None = None
        hi: int | None = None
        cur_block = self._cur_block
        cur_cmd = self._cur_cmd
        for fact in facts:
            if cur_block is not None and not self._fact_dominates(fact, cur_block, cur_cmd):
                continue
            if fact.interval.lower is not None:
                lo = fact.interval.lower if lo is None else max(lo, fact.interval.lower)
            if fact.interval.upper is not None:
                hi = fact.interval.upper if hi is None else min(hi, fact.interval.upper)
        if lo is None and hi is None:
            return None
        return (lo, hi)

    def _fact_dominates(
        self,
        fact: _AssumeFact,
        query_block: str,
        query_cmd: int | None,
    ) -> bool:
        return self._position_dominates(
            fact.block_id, fact.cmd_index, query_block, query_cmd
        )

    def _position_dominates(
        self,
        fact_block: str,
        fact_cmd: int,
        query_block: str,
        query_cmd: int | None,
    ) -> bool:
        if fact_block == query_block:
            return query_cmd is None or fact_cmd < query_cmd
        return fact_block in self.dominators.get(query_block, frozenset())

    def diff_bounds(
        self, a_name: str, b_name: str
    ) -> tuple[int | None, int | None] | None:
        """Return inclusive bounds on ``a - b`` from dominating relational
        assumes, or ``None`` if nothing is known.

        Each relational op tightens the difference:

        - ``a <  b``  ⇒  ``a - b ≤ -1``
        - ``a <= b``  ⇒  ``a - b ≤  0``
        - ``a == b``  ⇒  ``a - b ∈ {0}``
        - ``a >= b``  ⇒  ``a - b ≥  0``
        - ``a >  b``  ⇒  ``a - b ≥  1``

        When both symbols are the same canonical name, returns ``(0, 0)``
        trivially.
        """
        sym_a = canonical_symbol(a_name, strip_var_suffixes=_STRIP_SUFFIXES)
        sym_b = canonical_symbol(b_name, strip_var_suffixes=_STRIP_SUFFIXES)
        if sym_a == sym_b:
            return (0, 0)
        facts = self.relations_by_pair.get((sym_a, sym_b))
        if not facts:
            return None
        lo: int | None = None
        hi: int | None = None
        cur_block = self._cur_block
        cur_cmd = self._cur_cmd
        for fact in facts:
            if cur_block is not None and not self._position_dominates(
                fact.block_id, fact.cmd_index, cur_block, cur_cmd
            ):
                continue
            op = fact.relation.op
            if op == "==":
                lo = 0 if lo is None else max(lo, 0)
                hi = 0 if hi is None else min(hi, 0)
            elif op == ">=":
                lo = 0 if lo is None else max(lo, 0)
            elif op == ">":
                lo = 1 if lo is None else max(lo, 1)
            elif op == "<=":
                hi = 0 if hi is None else min(hi, 0)
            elif op == "<":
                hi = -1 if hi is None else min(hi, -1)
        if lo is None and hi is None:
            return None
        return (lo, hi)

    # --- fresh-variable emission (entry-block insertion) ---

    def is_entry_defined(self, var_name: str) -> bool:
        """True iff ``var_name`` has every definition in the entry block.

        Used as a precondition for rules that emit entry-block assumes
        referencing ``var_name`` — the referenced symbol must be defined
        somewhere the entry-block insertion point can see.
        """
        if self.entry_block_id is None:
            return False
        canonical = canonical_symbol(var_name, strip_var_suffixes=_STRIP_SUFFIXES)
        defs = self.du.definitions_by_symbol.get(canonical, ())
        if not defs:
            return False
        return all(d.block_id == self.entry_block_id for d in defs)

    def emit_fresh_var(
        self,
        prefix: str = "T",
        assumes_fn: Callable[[SymbolRef], Sequence[TacExpr]] = lambda _: (),
        *,
        sort: str = "int",
        placement: str = "current",
        reuse_name: str | None = None,
    ) -> SymbolRef:
        """Queue a fresh havoc'd variable + accompanying assumes.

        ``placement`` chooses where the havoc + assumes are inserted:

        - ``"current"`` (default): just before the current ``(block, cmd_index)``
          position. Works for any operand that is DSA-static (def dominates
          the current use), which is the common case and the most permissive
          placement.
        - ``"entry"``: appended to the entry block before its terminator.
          Use when the rule wants to consolidate introduced vars; requires
          operands to be defined in the entry block (rule should check via
          :meth:`is_entry_defined`).

        ``assumes_fn`` receives the fresh :class:`SymbolRef` and returns the
        boolean assumes that pin its value.

        If ``reuse_name`` is provided, that name is used for the havoc instead
        of generating ``T<N>``; the caller is responsible for ensuring the
        existing symbol is being repurposed (typically a rule that replaces
        an :class:`AssignExpCmd`'s whole RHS reuses the LHS name, and calls
        :meth:`skip_current_cmd` so the old assignment is removed).
        """
        if reuse_name is not None:
            name = reuse_name
            new_symbol = False
        else:
            name = self._next_fresh_name(prefix)
            new_symbol = True
        t = SymbolRef(name)
        cmds: list[TacCmd] = [AssignHavocCmd(raw="", lhs=name)]
        for cond in assumes_fn(t):
            cmds.append(AssumeExpCmd(raw="", condition=cond))
        if placement == "entry":
            self._pending_entry_cmds.extend(cmds)
        elif placement == "current":
            assert self._cur_block is not None and self._cur_cmd is not None, (
                "emit_fresh_var(placement='current') requires a set position"
            )
            key = (self._cur_block, self._cur_cmd)
            self._pending_by_position.setdefault(key, []).extend(cmds)
        else:
            raise ValueError(f"unknown placement: {placement!r}")
        if new_symbol:
            self._pending_symbols.append((name, sort))
        return t

    def emit_fresh_assign(
        self,
        prefix: str,
        rhs: TacExpr,
        *,
        sort: str,
        placement: str = "current",
        block_id: str | None = None,
    ) -> SymbolRef:
        """Queue ``AssignExpCmd <name> <rhs>`` and register ``<name>:<sort>``.

        Counterpart to :meth:`emit_fresh_var` for the straight-assignment
        case: introduce a fresh variable whose value is exactly ``rhs``.
        Returns ``SymbolRef(<name>)`` so the caller can substitute it in
        place of ``rhs`` at the call site.

        Placements:

        - ``"current"`` — insert just before the rule's current command
          (mirrors :meth:`emit_fresh_var`).
        - ``"entry"`` — insert just before the entry block's terminator.
        - ``"block_end"`` — insert just before ``block_id``'s terminator.
          ``block_id`` is required and must name a block in the current
          program. Used by CSE to hoist a TCSE to the deepest common
          dominator of its uses, which is broader than entry alone.
        """
        name = self._next_fresh_name(prefix)
        cmd = AssignExpCmd(raw="", lhs=name, rhs=rhs)
        if placement == "entry":
            self._pending_entry_cmds.append(cmd)
        elif placement == "current":
            assert self._cur_block is not None and self._cur_cmd is not None, (
                "emit_fresh_assign(placement='current') requires a set position"
            )
            key = (self._cur_block, self._cur_cmd)
            self._pending_by_position.setdefault(key, []).append(cmd)
        elif placement == "block_end":
            if block_id is None:
                raise ValueError(
                    "emit_fresh_assign(placement='block_end') requires block_id"
                )
            block_obj = next(
                (b for b in self.program.blocks if b.id == block_id), None
            )
            if block_obj is None:
                raise ValueError(
                    f"emit_fresh_assign: block_id={block_id!r} not in program"
                )
            term_idx = next(
                (
                    i
                    for i, c in enumerate(block_obj.commands)
                    if isinstance(c, (JumpCmd, JumpiCmd))
                ),
                len(block_obj.commands),
            )
            key = (block_id, term_idx)
            self._pending_by_position.setdefault(key, []).append(cmd)
        else:
            raise ValueError(f"unknown placement: {placement!r}")
        self._pending_symbols.append((name, sort))
        return SymbolRef(name)

    def _next_fresh_name(self, prefix: str) -> str:
        """Pick a name not already present in the program's symbol table.

        Naming follows the existing register style — ``<prefix><N>`` with no
        separator (so ``T0``, ``T1``, ... matches ``R0``, ``I50``, etc.).
        """
        existing = self.du.symbol_to_id
        pending_names = {n for n, _ in self._pending_symbols}
        while True:
            name = f"{prefix}{self._fresh_counter}"
            self._fresh_counter += 1
            if name not in existing and name not in pending_names:
                return name

    def drain_pending(
        self,
    ) -> tuple[
        list[TacCmd],
        dict[tuple[str, int], list[TacCmd]],
        list[tuple[str, str]],
        set[tuple[str, int]],
        int,
    ]:
        """Return queued commands, symbol entries, skip-set, and next fresh counter.

        Called by the driver between outer iterations; returns everything it
        needs to splice the pending cmds into the program and suppress any
        commands whose positions were marked via :meth:`skip_current_cmd`.
        Preserves the fresh-name counter across the next :class:`RewriteCtx`
        rebuild.
        """
        entry_cmds = self._pending_entry_cmds
        pos_cmds = self._pending_by_position
        syms = self._pending_symbols
        skips = self._pending_skips
        counter = self._fresh_counter
        self._pending_entry_cmds = []
        self._pending_by_position = {}
        self._pending_symbols = []
        self._pending_skips = set()
        return entry_cmds, pos_cmds, syms, skips, counter
