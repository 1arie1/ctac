"""``ctac pin`` — drop blocks, bind variables, enumerate splits.

Two-phase architecture:

* **Phase 1 — analysis.** :func:`compute_dead_blocks` is a pure
  graph-level fixpoint over the CFG. It uses a small Boolean
  evaluator (:func:`static_eval_bool`) to predict which JumpiCmd
  conditions become constant under the user's binds + auto-generated
  RC binds, so the dropped block set can be computed without
  invoking the rewriter.

* **Phase 2 — transformation.** Given the dead set from Phase 1,
  apply CFG surgery + substitution + cleanup folds in a single
  straight-line pass. (Implemented in subsequent commits.)

The result satisfies a structural contract: every block in the
output is reachable from entry AND can reach a terminal block (no
dangling halts, no unreachable orphans).
"""

from __future__ import annotations

import itertools
import re
from collections.abc import Iterable, Mapping
from dataclasses import dataclass, replace

import networkx as nx

from ctac.ast.nodes import (
    AnnotationCmd,
    ApplyExpr,
    AssertCmd,
    AssignExpCmd,
    AssignHavocCmd,
    AssumeExpCmd,
    ConstExpr,
    JumpCmd,
    JumpiCmd,
    SymbolRef,
    TacCmd,
    TacExpr,
)
from ctac.analysis.passes import analyze_dsa, analyze_use_before_def
from ctac.analysis.symbols import canonical_symbol
from ctac.ast.range_constraints import const_expr_to_int
from ctac.ast.subst import subst_symbol_to_expr
from ctac.ir.models import NBId, TacBlock, TacProgram
from ctac.rewrite import rewrite_program
from ctac.rewrite.rules.bool_fold import BOOL_CONST_FOLD
from ctac.rewrite.rules.copyprop import CP_ALIAS
from ctac.rewrite.rules.ite import ITE_BOOL, ITE_SAME
from ctac.rewrite.unparse import canonicalize_cmd
from ctac.smt.encoding.path_skeleton import (
    block_id_for_reachability_var,
    is_reachability_var,
    reachability_var_name,
)
from ctac.tracing import NullTrace, Trace


def _canon(name: str) -> str:
    """Canonicalize a symbol name (strip ``:N`` DSA-version suffix)."""
    return canonical_symbol(name, strip_var_suffixes=True)


# Public type aliases.
BlockId = NBId
Bind = tuple[str, ConstExpr]


# ---------------------------------------------------------------- helpers


def _entry_block_id(program: TacProgram) -> BlockId:
    """First block in source order is the entry. Mirrors sea_vc."""
    if not program.blocks:
        raise ValueError("program has no blocks; cannot determine entry")
    return program.blocks[0].id


def _build_definition_map(program: TacProgram) -> dict[str, TacExpr]:
    """Single-static-assignment definition map: ``canonical_var -> rhs``.

    Keys are canonicalized (DSA ``:N`` suffix stripped) so lookups
    match symbol references regardless of their per-use suffix.

    Only ``AssignExpCmd`` defs are recorded — havocs are unconstrained
    and the static evaluator treats them as unknown via absence.

    If the same canonical variable is defined more than once (which
    violates DSA but can happen in malformed inputs), the *last*
    definition wins.
    """
    out: dict[str, TacExpr] = {}
    for b in program.blocks:
        for cmd in b.commands:
            if isinstance(cmd, AssignExpCmd):
                out[_canon(cmd.lhs)] = cmd.rhs
    return out


def _build_def_block_map(program: TacProgram) -> dict[str, frozenset[BlockId]]:
    """Map canonical symbol name -> set of blocks defining it via
    ``AssignExpCmd``.

    Used by the post-pinning Ite-arm fold to detect symbols whose
    every def site is in the dropped block set; references to such
    symbols are dead in the surviving program.

    Havoc defs are intentionally excluded: RC vars are havoc'd in the
    entry block (which is never dropped), so a havoc'd RC var's def
    site stays alive even when its named block is dropped — pin
    handles that case via ``_drop_havoc_defs_for_dead_rcs`` and the
    RC=false bind. For non-RC havocs that escape their block, a use
    after a drop is already a use-before-def, not an Ite-arm dropping
    case."""
    by_sym: dict[str, set[BlockId]] = {}
    for b in program.blocks:
        for cmd in b.commands:
            if isinstance(cmd, AssignExpCmd):
                by_sym.setdefault(_canon(cmd.lhs), set()).add(b.id)
    return {k: frozenset(v) for k, v in by_sym.items()}


def _build_assume_map(program: TacProgram) -> dict[str, ConstExpr]:
    """Pull ``Eq(SymbolRef(x), ConstExpr(c))``-shape unconditional
    assumes into a substitution. Useful for static eval to recognize
    ``assume B987 == false`` style facts that the user encoded
    inline rather than via ``--bind``.

    Conservative: only records bindings for assumes whose RHS is a
    Bool ``ConstExpr``. Multi-block, multi-cmd; entry-block precedence
    matters but for Phase 1 we treat all assumes uniformly (sound for
    the cases we model, since pin's substitution isn't path-sensitive
    either).
    """
    out: dict[str, ConstExpr] = {}
    for b in program.blocks:
        for cmd in b.commands:
            if not isinstance(cmd, AssumeExpCmd):
                continue
            cond = cmd.condition
            if (
                isinstance(cond, ApplyExpr)
                and cond.op == "Eq"
                and len(cond.args) == 2
            ):
                a, c = cond.args
                if isinstance(a, SymbolRef) and isinstance(c, ConstExpr):
                    if c.value in ("true", "false"):
                        out[_canon(a.name)] = c
                elif isinstance(c, SymbolRef) and isinstance(a, ConstExpr):
                    if a.value in ("true", "false"):
                        out[_canon(c.name)] = a
    return out


def _jumpis_in(program: TacProgram) -> Iterable[tuple[BlockId, JumpiCmd]]:
    """Yield ``(block_id, jumpi_cmd)`` for each JumpiCmd in the program."""
    for b in program.blocks:
        if b.commands and isinstance(b.commands[-1], JumpiCmd):
            yield b.id, b.commands[-1]


def _cfg_digraph(program: TacProgram) -> nx.DiGraph:
    """Build a networkx DiGraph from the program's CFG.

    Lightweight: nodes are block ids; edges follow ``successors``.
    Doesn't carry any per-edge data (Phase 1 doesn't need it)."""
    g = nx.DiGraph()
    for b in program.blocks:
        g.add_node(b.id)
    for b in program.blocks:
        for s in b.successors:
            if s in g:
                g.add_edge(b.id, s)
    return g


# ------------------------------------------------ static Boolean evaluator


_TRUE = ConstExpr("true")
_FALSE = ConstExpr("false")


def static_eval_bool(
    expr: TacExpr,
    subs: Mapping[str, ConstExpr],
    defs: Mapping[str, TacExpr] | None = None,
    *,
    _seen: frozenset[str] = frozenset(),
) -> bool | None:
    """Evaluate ``expr`` as a Boolean under the given substitutions.

    Recognized shapes: ``ConstExpr("true"|"false")``,
    ``SymbolRef(name)`` (resolved via ``subs`` then ``defs``),
    ``ApplyExpr`` over ``LNot``/``LAnd``/``LOr``/``Eq``/``Ite``.

    Returns ``True``/``False`` when the expression evaluates to a
    concrete Bool; ``None`` when the result depends on a symbol not
    in ``subs`` or a non-Bool operator we don't model.

    Cycle-safe: a symbol whose definition recursively refers to
    itself (via ``_seen``) bails to ``None``.
    """
    if isinstance(expr, ConstExpr):
        if expr.value == "true":
            return True
        if expr.value == "false":
            return False
        return None

    if isinstance(expr, SymbolRef):
        canon = _canon(expr.name)
        if canon in subs:
            v = subs[canon].value
            if v == "true":
                return True
            if v == "false":
                return False
            return None
        if defs is not None and canon in defs and canon not in _seen:
            return static_eval_bool(
                defs[canon], subs, defs, _seen=_seen | {canon}
            )
        return None

    if not isinstance(expr, ApplyExpr):
        return None

    op, args = expr.op, expr.args

    if op == "LNot":
        if len(args) != 1:
            return None
        v = static_eval_bool(args[0], subs, defs, _seen=_seen)
        return None if v is None else not v

    if op == "LAnd":
        # Three-valued: any concrete False -> False; if all concrete True -> True;
        # else None (some operand unknown).
        any_unknown = False
        for a in args:
            v = static_eval_bool(a, subs, defs, _seen=_seen)
            if v is False:
                return False
            if v is None:
                any_unknown = True
        return None if any_unknown else True

    if op == "LOr":
        any_unknown = False
        for a in args:
            v = static_eval_bool(a, subs, defs, _seen=_seen)
            if v is True:
                return True
            if v is None:
                any_unknown = True
        return None if any_unknown else False

    if op == "Eq":
        if len(args) != 2:
            return None
        va = static_eval_bool(args[0], subs, defs, _seen=_seen)
        vb = static_eval_bool(args[1], subs, defs, _seen=_seen)
        if va is None or vb is None:
            return None
        return va == vb

    if op == "Ite":
        if len(args) != 3:
            return None
        cond = static_eval_bool(args[0], subs, defs, _seen=_seen)
        if cond is None:
            return None
        return static_eval_bool(
            args[1] if cond else args[2], subs, defs, _seen=_seen
        )

    return None


# -------------------------------------------------------- dead-set closure


@dataclass(frozen=True)
class DeadSetResult:
    """Output of :func:`compute_dead_blocks`."""

    dead: frozenset[BlockId]
    iterations: int


def compute_dead_blocks(
    program: TacProgram,
    user_drops: Iterable[BlockId],
    user_binds: Mapping[str, ConstExpr] | None = None,
    *,
    trace: Trace | None = None,
) -> DeadSetResult:
    """Compute the closure of blocks that must be dropped.

    Pure CFG analysis: builds a DiGraph, applies node removals (for
    user drops and orphans discovered in earlier iterations) and
    edge removals (for JumpiCmd conditions that fold to a constant
    under user binds + RC binds), then sweeps bidirectional
    reachability. Iterates until the dead set stops growing.

    Does **not** invoke the rewriter; caller can run this as a
    cheap "what-if" preview.

    The returned set always includes the user's named drops. It
    does not include the entry block (which is structurally
    undroppable; if user names it the caller should error out
    separately — :func:`validate_plan`).
    """
    if user_binds is None:
        user_binds = {}
    tr: Trace = trace if trace is not None else NullTrace()

    entry = _entry_block_id(program)
    all_blocks = {b.id for b in program.blocks}
    dead = set(user_drops) & all_blocks
    user_drop_set = set(dead)

    # Emit "user_drop" events upfront for clear reason attribution.
    for b in sorted(user_drop_set):
        tr.emit({"event": "block-dropped", "phase": "analyze",
                 "block": b, "reason": "user_drop", "iter": 0})

    defs = _build_definition_map(program)
    assume_subs = _build_assume_map(program)

    base_graph = _cfg_digraph(program)
    # A "terminal" is a block that originally had no successor — a halt
    # block. Computing this once on the source CFG (rather than on the
    # working copy after node removal) prevents pin from declaring a
    # block-with-dead-only-successor a "live exit." Such blocks are
    # structurally dead under the drop and should cascade.
    original_terminals = {
        n for n in base_graph.nodes if base_graph.out_degree(n) == 0
    }
    jumpis = list(_jumpis_in(program))

    iterations = 0
    while True:
        iterations += 1
        prior_dead = set(dead)

        # Substitution map for static evaluation = user binds (highest
        # priority) + assume-derived facts + RC binds for the current
        # dead set. RC binds last so they override any conflicting
        # assume that mentions the same RC var (shouldn't happen in
        # practice, but order makes the intent explicit).
        subs: dict[str, ConstExpr] = {**assume_subs, **user_binds}
        for b in dead:
            subs[reachability_var_name(b)] = _FALSE

        # Working CFG: drop dead blocks, then for each Jumpi whose
        # condition evaluates statically, remove the dead-branch edge.
        gp = base_graph.copy()
        gp.remove_nodes_from(dead)

        for block_id, jumpi in jumpis:
            if block_id in dead:
                continue
            cond_expr = SymbolRef(jumpi.condition)
            v = static_eval_bool(cond_expr, subs, defs)
            if v is None:
                continue
            kill = jumpi.else_target if v else jumpi.then_target
            if gp.has_edge(block_id, kill):
                gp.remove_edge(block_id, kill)

        # Bidirectional reachability.
        if entry in gp:
            fwd = nx.descendants(gp, entry) | {entry}
        else:
            fwd = set()
        # Use original-CFG terminals (intersected with what's still
        # alive in gp). A block whose successors all died is NOT a
        # terminal — it's a structurally-dead block that should
        # cascade.
        terminals = (original_terminals - dead) & fwd
        bwd: set[BlockId] = set()
        for t in terminals:
            bwd |= nx.ancestors(gp, t) | {t}
        live = fwd & bwd

        new_dead = all_blocks - live
        if new_dead == dead:
            tr.emit({"event": "phase1-converged", "phase": "analyze",
                     "iter": iterations, "final_dead_count": len(dead)})
            return DeadSetResult(dead=frozenset(dead), iterations=iterations)

        # Newly-orphaned blocks this iteration. Emit their attribution.
        added = new_dead - prior_dead
        for b in sorted(added):
            # Distinguish forward- vs backward-unreachable for diagnostics.
            reason = (
                "unreachable_from_entry"
                if b not in fwd
                else "unreachable_to_exit"
            )
            tr.emit({"event": "block-dropped", "phase": "analyze",
                     "block": b, "reason": reason, "iter": iterations})
        dead = new_dead


# ------------------------------------------------------------- validation


def validate_plan_against(
    program: TacProgram,
    *,
    drops: Iterable[BlockId] = (),
    binds: Mapping[str, ConstExpr] | None = None,
) -> list[str]:
    """Pre-flight check: returns a list of human-readable issues.

    Empty list = clean. Used by the CLI to surface errors before
    running the full pin.
    """
    issues: list[str] = []
    drops_set = set(drops)
    all_blocks = {b.id for b in program.blocks}

    for d in drops_set:
        if d not in all_blocks:
            issues.append(f"--drop target {d!r} is not a block in the program")

    if binds:
        for var in binds:
            if is_reachability_var(var):
                issues.append(
                    f"--bind {var!r} is a reachability variable; pin one "
                    f"via --drop on the corresponding block instead"
                )

    if drops_set:
        result = compute_dead_blocks(program, drops_set, binds or {})
        entry = _entry_block_id(program)
        if entry in result.dead:
            issues.append(
                f"plan would drop the entry block {entry!r} "
                f"(directly or by cascade); program would have no executions"
            )
        # Are there any live exits remaining?
        live = all_blocks - result.dead
        if not any(
            not any(s in live for s in b.successors)
            for b in program.blocks
            if b.id in live
        ):
            issues.append(
                "plan leaves no entry-to-exit path; every live block has "
                "a live successor (no terminals reachable)"
            )

    return issues


# ----------------------------------------------------- Phase 2 transforms


def _check_no_rc_in_jumpi_conditions(program: TacProgram) -> None:
    """Pre-condition: RC variables are never used as JumpiCmd conditions.

    The Certora RC-var contract says RCs only appear in map definitions
    (Ite-merge guards on memory variables) and never in control-flow
    conditions. Pin relies on this — if violated, the dominance-based
    RC=true substitution would need to participate in CFG surgery
    (creating the iteration we're trying to avoid). Hard error rather
    than silent miscompilation.
    """
    for b in program.blocks:
        for cmd in b.commands:
            if isinstance(cmd, JumpiCmd):
                if is_reachability_var(_canon(cmd.condition)):
                    raise ValueError(
                        f"JumpiCmd in block {b.id!r} has RC variable "
                        f"{cmd.condition!r} as condition; this violates "
                        f"the Certora RC-var contract (RCs appear only "
                        f"in map definitions, never in jump conditions). "
                        f"Pin cannot proceed."
                    )


def _dominator_sets(program: TacProgram) -> dict[BlockId, frozenset[BlockId]]:
    """For each block, the set of blocks that dominate it (including
    itself). Computed on the program's CFG as-is — caller is
    responsible for having removed dead blocks first.

    Blocks not reachable from the entry get an empty dominator set."""
    if not program.blocks:
        return {}
    g = _cfg_digraph(program)
    entry = _entry_block_id(program)
    if entry not in g:
        return {b.id: frozenset() for b in program.blocks}

    fwd = nx.descendants(g, entry) | {entry}
    sub = g.subgraph(fwd)
    idom = nx.immediate_dominators(sub, entry)

    out: dict[BlockId, frozenset[BlockId]] = {}
    for n in sub.nodes:
        chain = {n}
        cur = n
        # idom[entry] == entry; walk up until we reach the fixed point.
        while cur != idom.get(cur, cur):
            cur = idom[cur]
            chain.add(cur)
        out[n] = frozenset(chain)

    for b in program.blocks:
        if b.id not in out:
            out[b.id] = frozenset()
    return out


def _per_block_bind_maps(
    program: TacProgram,
    dead: frozenset[BlockId],
    user_binds: Mapping[str, ConstExpr],
    dominators: Mapping[BlockId, frozenset[BlockId]],
) -> dict[BlockId, dict[str, ConstExpr]]:
    """Per-block substitution map encoding the RC variable contract:

    * Global (every block): user binds + ``RC_BLK = false`` for each
      dropped block.
    * Per surviving block X: ``RC_BLK = true`` for every block BLK
      that dominates X in the post-drop CFG.

    RC=false (from a dead block) takes precedence over RC=true (from
    a dominator) — but in practice dead blocks aren't in the
    post-drop CFG so they can't be dominators of anything; the two
    sets are disjoint.
    """
    global_b: dict[str, ConstExpr] = dict(user_binds)
    for b in dead:
        global_b[reachability_var_name(b)] = ConstExpr("false")

    out: dict[BlockId, dict[str, ConstExpr]] = {}
    for b in program.blocks:
        bm = dict(global_b)
        for dom in dominators.get(b.id, ()):
            rc = reachability_var_name(dom)
            if rc not in bm:
                bm[rc] = ConstExpr("true")
        out[b.id] = bm
    return out


def _expand_block_binds_for_suffixes(
    block: TacBlock, mapping: Mapping[str, TacExpr]
) -> dict[str, TacExpr]:
    """Per-block version of :func:`_expand_with_suffixes`. Walks one
    block's commands and adds DSA-suffixed variants of the canonical
    keys actually present in this block's expressions."""
    if not mapping:
        return dict(mapping)
    canonical_keys = {_canon(k): v for k, v in mapping.items()}
    out: dict[str, TacExpr] = dict(mapping)
    out.update(canonical_keys)

    def _walk(expr: TacExpr) -> None:
        if isinstance(expr, SymbolRef):
            ck = _canon(expr.name)
            if ck in canonical_keys:
                out[expr.name] = canonical_keys[ck]
        elif isinstance(expr, ApplyExpr):
            for a in expr.args:
                _walk(a)

    for cmd in block.commands:
        if isinstance(cmd, AssignExpCmd):
            _walk(cmd.rhs)
        elif isinstance(cmd, AssumeExpCmd):
            _walk(cmd.condition)
        elif isinstance(cmd, AssertCmd):
            _walk(cmd.predicate)
    return out


def _substitute_per_block(
    program: TacProgram,
    per_block_binds: Mapping[BlockId, Mapping[str, ConstExpr]],
) -> TacProgram:
    """Substitute SymbolRef -> ConstExpr per block, using each block's
    own bind map. Blocks without a map (or with an empty one) pass
    through unchanged."""
    new_blocks: list[TacBlock] = []
    for b in program.blocks:
        bm = per_block_binds.get(b.id)
        if not bm:
            new_blocks.append(b)
            continue
        expanded = _expand_block_binds_for_suffixes(b, bm)
        new_cmds = [_subst_in_cmd(c, expanded) for c in b.commands]
        new_blocks.append(
            TacBlock(id=b.id, successors=list(b.successors), commands=new_cmds)
        )
    return TacProgram(blocks=new_blocks)


def _expand_with_suffixes(
    program: TacProgram, mapping: Mapping[str, TacExpr]
) -> dict[str, TacExpr]:
    """Build a substitution map keyed by *every* DSA-suffixed variant of
    each canonical name in ``mapping``.

    pin's binds are conceptually keyed by the canonical name (e.g.
    ``ReachabilityCertora65_1_0_0_0_0``), but TAC use sites carry
    ``:N`` suffixes (e.g. ``ReachabilityCertora65_1_0_0_0_0:15``).
    We walk the program once and add each suffixed variant of each
    bound symbol to a flat lookup map; ``subst_symbol_to_expr`` can
    then match exact names without needing to canonicalize at every
    step.
    """
    if not mapping:
        return dict(mapping)
    canonical_keys = {_canon(k): v for k, v in mapping.items()}
    out: dict[str, TacExpr] = dict(mapping)
    out.update(canonical_keys)

    def _walk(expr: TacExpr) -> None:
        if isinstance(expr, SymbolRef):
            if _canon(expr.name) in canonical_keys:
                out[expr.name] = canonical_keys[_canon(expr.name)]
        elif isinstance(expr, ApplyExpr):
            for a in expr.args:
                _walk(a)

    for b in program.blocks:
        for cmd in b.commands:
            if isinstance(cmd, AssignExpCmd):
                _walk(cmd.rhs)
            elif isinstance(cmd, AssumeExpCmd):
                _walk(cmd.condition)
            elif isinstance(cmd, AssertCmd):
                _walk(cmd.predicate)
    return out


def _subst_in_cmd(cmd: TacCmd, mapping: Mapping[str, TacExpr]) -> TacCmd:
    """Substitute SymbolRef -> TacExpr through every expression-bearing
    field of ``cmd``. Returns a new cmd if anything changed.

    Annotations and Havocs have no expression payload (lhs is a name,
    not a SymbolRef) and pass through unchanged. JumpiCmd's ``condition``
    is a name, not an expression — handled separately by terminator
    surgery, not by this expression substitution.

    Re-renders ``cmd.raw`` after substituting, so ``render_program``
    (which serializes from ``cmd.raw``) emits the substituted form.
    Without this, downstream tools that parse the written file see the
    original symbol references and the bind has no observable effect.

    The caller is responsible for ensuring ``mapping`` covers every
    DSA-suffixed variant the substitution should hit (use
    :func:`_expand_with_suffixes`).
    """
    if isinstance(cmd, AssignExpCmd):
        new_rhs = subst_symbol_to_expr(cmd.rhs, mapping)
        if new_rhs is cmd.rhs:
            return cmd
        return canonicalize_cmd(replace(cmd, rhs=new_rhs))
    if isinstance(cmd, AssumeExpCmd):
        new_cond = subst_symbol_to_expr(cmd.condition, mapping)
        if new_cond is cmd.condition:
            return cmd
        return canonicalize_cmd(replace(cmd, condition=new_cond))
    if isinstance(cmd, AssertCmd):
        new_pred = subst_symbol_to_expr(cmd.predicate, mapping)
        if new_pred is cmd.predicate:
            return cmd
        return canonicalize_cmd(replace(cmd, predicate=new_pred))
    return cmd


def _substitute_in_program(
    program: TacProgram, mapping: Mapping[str, TacExpr]
) -> TacProgram:
    """Substitute SymbolRef -> TacExpr in every expression-bearing
    command across the program. Returns a new TacProgram.

    Handles DSA ``:N`` suffix variance: the mapping can be keyed by
    canonical names; this function expands it to cover every suffixed
    variant present in the program before substituting."""
    if not mapping:
        return program
    expanded = _expand_with_suffixes(program, mapping)
    new_blocks: list[TacBlock] = []
    for b in program.blocks:
        new_cmds = [_subst_in_cmd(c, expanded) for c in b.commands]
        new_blocks.append(
            TacBlock(id=b.id, successors=list(b.successors), commands=new_cmds)
        )
    return TacProgram(blocks=new_blocks)


def _drop_cfg_surgery(
    program: TacProgram,
    dead: frozenset[BlockId],
    subs: Mapping[str, ConstExpr],
    defs: Mapping[str, TacExpr],
) -> TacProgram:
    """Rewrite per-predecessor terminators so they no longer reference
    dead blocks.

    For each live block B with a JumpiCmd terminator:

    * If the condition statically evaluates to ``True`` under ``subs``
      (using ``defs`` to chase symbol definitions), rewrite to
      ``JumpCmd(then_target)``.
    * If it evaluates to ``False``, rewrite to ``JumpCmd(else_target)``.
    * Otherwise, if exactly one of ``then_target`` / ``else_target`` is
      in ``dead``, rewrite to the live target as ``JumpCmd``.
    * If both targets are dead, B itself should be in ``dead`` per the
      Phase 1 contract; raise rather than emit a dangling halt.

    Successor lists are rebuilt to match the new terminator. Live
    blocks remain in the program; ``_remove_blocks`` removes the dead
    set in a separate step.
    """
    new_blocks: list[TacBlock] = []
    for b in program.blocks:
        if b.id in dead:
            new_blocks.append(b)
            continue

        if not b.commands:
            new_blocks.append(b)
            continue

        last = b.commands[-1]
        if isinstance(last, JumpCmd):
            if last.target in dead:
                # Phase 1 contract: this should not happen for a live block.
                raise AssertionError(
                    f"live block {b.id!r} has unconditional jump to dead "
                    f"block {last.target!r}; Phase 1 should have flagged "
                    f"{b.id!r} as dead too"
                )
            new_blocks.append(b)
            continue

        if not isinstance(last, JumpiCmd):
            new_blocks.append(b)
            continue

        # JumpiCmd: rewrite ONLY when one of its targets is in the
        # effective dead set. We don't speculatively fold static-eval-
        # constant conditions when both targets are live — pin is a
        # targeted CFG-edit tool, and folding such Jumpi's would
        # silently re-shape the CFG in places the user didn't ask
        # about (creating spurious orphans relative to the source).
        then_dead = last.then_target in dead
        else_dead = last.else_target in dead
        if then_dead and else_dead:
            raise AssertionError(
                f"live block {b.id!r}'s JumpiCmd targets both dead "
                f"({last.then_target!r}, {last.else_target!r}); Phase 1 "
                f"should have flagged {b.id!r} as dead too"
            )

        keep_target: str | None = None
        if then_dead:
            keep_target = last.else_target
        elif else_dead:
            keep_target = last.then_target
        else:
            # Both targets live: try static-eval as a refinement only
            # when it would coincide with what cleanup would do anyway.
            # Specifically, only fold if the condition is a SymbolRef
            # whose value is bound directly in subs (user --bind or
            # auto-RC bind from drops). Don't chase through defs here
            # — that's an auto-simplification we leave to the cleanup
            # rewriter pass.
            if last.condition in subs or _canon(last.condition) in subs:
                cond_val = static_eval_bool(
                    SymbolRef(last.condition), subs, defs
                )
                if cond_val is True:
                    keep_target = last.then_target
                elif cond_val is False:
                    keep_target = last.else_target

        if keep_target is None:
            # Both targets live and no folding triggered — keep the Jumpi.
            new_blocks.append(b)
            continue

        new_jump = JumpCmd(raw="", target=keep_target)
        new_cmds = list(b.commands[:-1]) + [new_jump]
        new_blocks.append(
            TacBlock(
                id=b.id,
                successors=[keep_target],
                commands=new_cmds,
            )
        )

    return TacProgram(blocks=new_blocks)


def _remove_blocks(
    program: TacProgram, dead: frozenset[BlockId]
) -> TacProgram:
    """Return a new program with ``dead`` blocks removed and every
    surviving block's ``successors`` cleaned of references to
    removed blocks."""
    if not dead:
        return program
    surviving = [b for b in program.blocks if b.id not in dead]
    new_blocks = [
        TacBlock(
            id=b.id,
            successors=[s for s in b.successors if s not in dead],
            commands=list(b.commands),
        )
        for b in surviving
    ]
    return TacProgram(blocks=new_blocks)


def _drop_havoc_defs_for_dead_rcs(
    program: TacProgram, dead: frozenset[BlockId]
) -> TacProgram:
    """Remove ``AssignHavocCmd lhs ReachabilityCertora<dead>`` from
    every live block. The block hosting the havoc is itself dead so
    this is mostly belt-and-braces; but production-style TAC sometimes
    co-locates RC havocs in non-dead blocks (a single decls block)
    and we want those purged after binding the RCs to false.
    """
    from ctac.ast.nodes import AssignHavocCmd

    dead_rc_names = {reachability_var_name(b) for b in dead}
    if not dead_rc_names:
        return program
    new_blocks: list[TacBlock] = []
    changed = False
    for b in program.blocks:
        new_cmds: list[TacCmd] = []
        for cmd in b.commands:
            if (
                isinstance(cmd, AssignHavocCmd)
                and _canon(cmd.lhs) in dead_rc_names
            ):
                changed = True
                continue
            new_cmds.append(cmd)
        new_blocks.append(
            TacBlock(id=b.id, successors=list(b.successors), commands=new_cmds)
        )
    return TacProgram(blocks=new_blocks) if changed else program


def _try_lor_rc_self_dom(
    expr: TacExpr, predecessors: frozenset[BlockId]
) -> TacExpr | None:
    """If ``expr`` is ``LOr(RC[B_1], ..., RC[B_k])`` and the operand
    block IDs equal ``predecessors``, return ``_TRUE``. Else ``None``.

    Soundness: every reaching execution at the use-site block W has
    fired exactly one of W's live predecessors; if the disjunction
    names them all, it's true at W.
    """
    if not isinstance(expr, ApplyExpr) or expr.op != "LOr":
        return None
    if not expr.args:
        return None
    operand_blocks: set[BlockId] = set()
    for a in expr.args:
        if not isinstance(a, SymbolRef):
            return None
        bid = block_id_for_reachability_var(_canon(a.name))
        if bid is None:
            return None
        operand_blocks.add(bid)
    if frozenset(operand_blocks) != predecessors:
        return None
    return _TRUE


def _rewrite_expr_lor_rc(
    expr: TacExpr, predecessors: frozenset[BlockId]
) -> TacExpr:
    """Recursively apply :func:`_try_lor_rc_self_dom` to every LOr in
    ``expr``. Returns ``expr`` unchanged if nothing fires."""
    if isinstance(expr, ApplyExpr):
        new_args = tuple(_rewrite_expr_lor_rc(a, predecessors) for a in expr.args)
        if expr.op == "LOr":
            folded = _try_lor_rc_self_dom(
                ApplyExpr(op=expr.op, args=list(new_args)), predecessors
            )
            if folded is not None:
                return folded
        if any(na is not oa for na, oa in zip(new_args, expr.args)):
            return ApplyExpr(op=expr.op, args=list(new_args))
    return expr


def _fold_lor_rc_self_dominance(program: TacProgram) -> TacProgram:
    """Self-dominance LOr-of-RC fold: per-block rewrite of
    ``LOr(RC[B_1], ..., RC[B_k])`` to ``true`` when ``{B_i}`` equals the
    block's live predecessor set in the post-drop CFG.

    Run this between substitution (which folds RC=false for dropped
    blocks) and the rewriter cleanup pass (which then propagates
    ``Ite(true, x, _) → x``).
    """
    cfg = _cfg_digraph(program)
    new_blocks: list[TacBlock] = []
    changed = False
    for b in program.blocks:
        preds = frozenset(cfg.predecessors(b.id))
        if not preds:
            new_blocks.append(b)
            continue
        new_cmds: list[TacCmd] = []
        block_changed = False
        for cmd in b.commands:
            if isinstance(cmd, AssignExpCmd):
                new_rhs = _rewrite_expr_lor_rc(cmd.rhs, preds)
                if new_rhs is not cmd.rhs:
                    new_cmds.append(canonicalize_cmd(replace(cmd, rhs=new_rhs)))
                    block_changed = True
                    continue
            elif isinstance(cmd, AssumeExpCmd):
                new_cond = _rewrite_expr_lor_rc(cmd.condition, preds)
                if new_cond is not cmd.condition:
                    new_cmds.append(canonicalize_cmd(replace(cmd, condition=new_cond)))
                    block_changed = True
                    continue
            elif isinstance(cmd, AssertCmd):
                new_pred = _rewrite_expr_lor_rc(cmd.predicate, preds)
                if new_pred is not cmd.predicate:
                    new_cmds.append(canonicalize_cmd(replace(cmd, predicate=new_pred)))
                    block_changed = True
                    continue
            new_cmds.append(cmd)
        if block_changed:
            new_blocks.append(
                TacBlock(id=b.id, successors=list(b.successors), commands=new_cmds)
            )
            changed = True
        else:
            new_blocks.append(b)
    return TacProgram(blocks=new_blocks) if changed else program


def _is_dropped_def_ref(
    expr: TacExpr,
    *,
    source_defs: Mapping[str, frozenset[BlockId]],
    dead: frozenset[BlockId],
) -> bool:
    """True iff ``expr`` is a ``SymbolRef`` whose source-program def
    sites are all in ``dead``.

    Conservative: returns False for non-symbol expressions, for
    symbols with at least one surviving def, and for symbols not in
    ``source_defs`` (no info — treat as live)."""
    if not isinstance(expr, SymbolRef):
        return False
    canon = _canon(expr.name)
    defs = source_defs.get(canon)
    if not defs:
        return False
    return defs.issubset(dead)


def _rewrite_expr_drop_ite_arms(
    expr: TacExpr,
    *,
    source_defs: Mapping[str, frozenset[BlockId]],
    dead: frozenset[BlockId],
) -> TacExpr:
    """Recursively fold ``Ite(c, armT, armF)`` where one arm references
    a symbol whose every source-program def is in ``dead``.

    If both arms are dropped, returns the original expression — the
    use site itself is dead and a higher-level pass should remove it,
    but folding to an arbitrary value would be unsound."""
    if not isinstance(expr, ApplyExpr):
        return expr
    new_args = tuple(
        _rewrite_expr_drop_ite_arms(a, source_defs=source_defs, dead=dead)
        for a in expr.args
    )
    if expr.op == "Ite" and len(new_args) == 3:
        cond, arm_t, arm_f = new_args
        t_dropped = _is_dropped_def_ref(arm_t, source_defs=source_defs, dead=dead)
        f_dropped = _is_dropped_def_ref(arm_f, source_defs=source_defs, dead=dead)
        if t_dropped and not f_dropped:
            return arm_f
        if f_dropped and not t_dropped:
            return arm_t
    if any(na is not oa for na, oa in zip(new_args, expr.args)):
        return ApplyExpr(op=expr.op, args=list(new_args))
    return expr


def _drop_ite_arms_with_dropped_def(
    program: TacProgram,
    *,
    source_defs: Mapping[str, frozenset[BlockId]],
    dead: frozenset[BlockId],
) -> TacProgram:
    """Per-block rewrite: any Ite arm referencing a symbol whose
    source-program defs are all dropped is folded out of the Ite.

    Soundness: in the surviving program, no execution produces such a
    symbol's value, so any Ite arm referencing it is on a dead branch.
    The Ite folds to its surviving arm regardless of the condition
    value — the user's claim is that the gating condition is already
    correlated with the dropped path, so it would never select the
    dead arm in any execution that reaches the Ite.

    Run this between substitution and the rewriter cleanup pass.
    Source-program def info must be captured before block removal so
    we can recognize the now-dropped def sites."""
    new_blocks: list[TacBlock] = []
    changed = False
    for b in program.blocks:
        new_cmds: list[TacCmd] = []
        block_changed = False
        for cmd in b.commands:
            if isinstance(cmd, AssignExpCmd):
                new_rhs = _rewrite_expr_drop_ite_arms(
                    cmd.rhs, source_defs=source_defs, dead=dead
                )
                if new_rhs is not cmd.rhs:
                    new_cmds.append(canonicalize_cmd(replace(cmd, rhs=new_rhs)))
                    block_changed = True
                    continue
            elif isinstance(cmd, AssumeExpCmd):
                new_cond = _rewrite_expr_drop_ite_arms(
                    cmd.condition, source_defs=source_defs, dead=dead
                )
                if new_cond is not cmd.condition:
                    new_cmds.append(canonicalize_cmd(replace(cmd, condition=new_cond)))
                    block_changed = True
                    continue
            elif isinstance(cmd, AssertCmd):
                new_pred = _rewrite_expr_drop_ite_arms(
                    cmd.predicate, source_defs=source_defs, dead=dead
                )
                if new_pred is not cmd.predicate:
                    new_cmds.append(canonicalize_cmd(replace(cmd, predicate=new_pred)))
                    block_changed = True
                    continue
            new_cmds.append(cmd)
        if block_changed:
            new_blocks.append(
                TacBlock(id=b.id, successors=list(b.successors), commands=new_cmds)
            )
            changed = True
        else:
            new_blocks.append(b)
    return TacProgram(blocks=new_blocks) if changed else program


_CLEANUP_RULES = (BOOL_CONST_FOLD, ITE_BOOL, ITE_SAME, CP_ALIAS)


def _cleanup(program: TacProgram) -> TacProgram:
    """Run the rewriter to fixpoint with pin's cleanup rule set:
    bool-const fold, ITE_BOOL, ITE_SAME, CP_ALIAS. Returns the rewritten
    program (no dead-code elimination here; that's a separate step)."""
    res = rewrite_program(program, _CLEANUP_RULES)
    return res.program


# ------------------------------------------------------- post-conditions


def _reachability_orphans(program: TacProgram) -> set[BlockId]:
    """Return blocks NOT on an entry-to-terminal path.

    Orphan = (forward-reachable from entry) \\cap (backward-reachable
    from any forward-reachable terminal) — complement of the live set.
    """
    if not program.blocks:
        return set()
    entry = _entry_block_id(program)
    g = _cfg_digraph(program)
    if entry not in g:
        return set(g.nodes)
    fwd = nx.descendants(g, entry) | {entry}
    terminals = {n for n in g.nodes if g.out_degree(n) == 0} & fwd
    bwd: set[BlockId] = set()
    for t in terminals:
        bwd |= nx.ancestors(g, t) | {t}
    live = fwd & bwd
    return set(g.nodes) - live


def assert_no_orphans(program: TacProgram) -> None:
    """Strict: every block lies on an entry-to-terminal path.

    Use this when you want to verify a program is structurally clean.
    Pin's internal contract is *relative* (don't introduce new
    orphans); use :func:`assert_no_new_orphans` for that.
    """
    orphans = _reachability_orphans(program)
    if orphans:
        sample = sorted(orphans)[:5]
        more = "" if len(orphans) <= 5 else f" (+{len(orphans) - 5} more)"
        raise AssertionError(
            f"orphan blocks present: {sample}{more}"
        )


def assert_no_new_orphans(
    source: TacProgram, output: TacProgram
) -> None:
    """Relative: pin must not introduce new orphans.

    Pre-existing orphans in ``source`` (blocks that were already
    forward-unreachable from entry, or unable to reach a terminal)
    are accepted in ``output``. Only orphans whose block ids appear
    in ``output`` but not as orphans of ``source`` are pin's fault."""
    src_orphans = _reachability_orphans(source)
    out_orphans = _reachability_orphans(output)
    new = out_orphans - src_orphans
    if new:
        sample = sorted(new)[:5]
        more = "" if len(new) <= 5 else f" (+{len(new) - 5} more)"
        raise AssertionError(
            f"pin introduced orphan blocks: {sample}{more}"
        )


def _used_block_ids(program: TacProgram) -> set[BlockId]:
    """Block ids referenced as JumpCmd/JumpiCmd targets."""
    refs: set[BlockId] = set()
    for b in program.blocks:
        for cmd in b.commands:
            if isinstance(cmd, JumpCmd):
                refs.add(cmd.target)
            elif isinstance(cmd, JumpiCmd):
                refs.add(cmd.then_target)
                refs.add(cmd.else_target)
    return refs


def assert_no_dangling_jumps(program: TacProgram) -> None:
    """Post-condition: every JumpCmd/JumpiCmd target exists in the program."""
    block_ids = {b.id for b in program.blocks}
    refs = _used_block_ids(program)
    missing = refs - block_ids
    if missing:
        raise AssertionError(
            f"dangling jump targets after pin: {sorted(missing)[:5]}"
        )


def _ubd_canonical_symbols(program: TacProgram) -> set[str]:
    ubd = analyze_use_before_def(program)
    return {_canon(i.symbol) for i in ubd.issues}


def _dsa_issue_signatures(program: TacProgram) -> set[tuple[str, str | None]]:
    dsa = analyze_dsa(program)
    return {(i.kind, _canon(i.symbol) if i.symbol else None) for i in dsa.issues}


def assert_no_use_before_def(program: TacProgram) -> None:
    """Strict: every variable use is dominated by a def, no exceptions.

    Use this on a program that should be clean from scratch. For the
    relative pin contract (pin shouldn't introduce *new* issues), use
    :func:`assert_no_new_use_before_def` instead."""
    ubd = analyze_use_before_def(program)
    if ubd.issues:
        sample = [
            f"{i.symbol}@{i.block_id}:{i.cmd_index}"
            for i in ubd.issues[:5]
        ]
        more = (
            "" if len(ubd.issues) <= 5
            else f" (+{len(ubd.issues) - 5} more)"
        )
        raise AssertionError(
            f"use-before-def violations: {sample}{more}"
        )


def assert_no_new_use_before_def(
    source: TacProgram, output: TacProgram
) -> None:
    """Relative: pin must not *introduce* UBD violations.

    Compares canonical symbol names (DSA suffixes stripped). Issues
    present in ``source`` are accepted; issues whose symbol appears
    only in ``output`` are pin's fault and trigger an assertion.
    """
    src = _ubd_canonical_symbols(source)
    out = _ubd_canonical_symbols(output)
    new = out - src
    if new:
        raise AssertionError(
            f"pin introduced use-before-def on {len(new)} symbol(s): "
            f"{sorted(new)[:5]}"
            + (f" (+{len(new) - 5} more)" if len(new) > 5 else "")
            + "\n  a dropped block defined these variables; their "
            "surviving uses didn't fold away. Inspect the output's "
            "Ite expressions over the corresponding RC vars."
        )


def assert_dsa_clean(program: TacProgram) -> None:
    """Strict: DSA shape is preserved. See :func:`assert_no_new_dsa_issues`
    for the relative variant pin uses internally."""
    dsa = analyze_dsa(program)
    if dsa.issues:
        sample = [
            f"{i.kind}@{i.block_id}: {i.detail[:60]}"
            for i in dsa.issues[:5]
        ]
        more = (
            "" if len(dsa.issues) <= 5
            else f" (+{len(dsa.issues) - 5} more)"
        )
        raise AssertionError(f"DSA shape violations: {sample}{more}")


def assert_no_new_dsa_issues(
    source: TacProgram, output: TacProgram
) -> None:
    """Relative: pin must not introduce new DSA shape issues."""
    src = _dsa_issue_signatures(source)
    out = _dsa_issue_signatures(output)
    new = out - src
    if new:
        raise AssertionError(
            f"pin introduced {len(new)} DSA issue(s): "
            f"{sorted(str(s) for s in new)[:5]}"
        )


# Quiet down the static checker about unused names that live for re-export.
_ = AnnotationCmd


# ---------------------------------------------------- AssumeRange (--assume-range)


@dataclass(frozen=True)
class AssumeRange:
    """One ``--assume-range`` entry — an inclusive integer interval
    on a single TAC symbol.

    ``lo`` / ``hi`` are the bound values (``None`` means "no bound on
    that side"). ``lo_strict`` / ``hi_strict`` flip the corresponding
    side from non-strict (``Le``) to strict (``Lt``). At least one of
    ``lo`` / ``hi`` must be non-None.

    Path-restriction tool: pin emits the assume into the program
    unconditionally, creating a sub-problem where the bound holds.
    Soundness w.r.t. the original program is the user's responsibility,
    same as ``--bind`` / ``--drop``.
    """

    var: str
    lo: int | None = None
    lo_strict: bool = False
    hi: int | None = None
    hi_strict: bool = False

    def __post_init__(self) -> None:
        if self.lo is None and self.hi is None:
            raise ValueError("assume-range needs at least one bound")
        if self.lo is not None and self.hi is not None:
            lo_eff = self.lo + 1 if self.lo_strict else self.lo
            hi_eff = self.hi - 1 if self.hi_strict else self.hi
            if lo_eff > hi_eff:
                lo_op = "<" if self.lo_strict else "<="
                hi_op = "<" if self.hi_strict else "<="
                raise ValueError(
                    f"contradictory assume-range on {self.var}: "
                    f"{self.lo} {lo_op} {self.var} {hi_op} {self.hi}"
                )


_ASSUME_RANGE_RX = re.compile(
    r"^\s*"
    r"(?:(?P<c1>-?(?:0[xX]-?[0-9a-fA-F_]+|\d+))\s*(?P<o1><=|<|>=|>)\s*)?"
    r"(?P<var>[A-Za-z_][A-Za-z0-9_]*)"
    r"(?:\s*(?P<o2><=|<|>=|>)\s*(?P<c2>-?(?:0[xX]-?[0-9a-fA-F_]+|\d+)))?"
    r"\s*$"
)


def _parse_int_const(text: str) -> int:
    """Parse a TAC integer literal: decimal, ``0xff``, ``0x-48``, ``-0x48``."""
    val = const_expr_to_int(ConstExpr(text))
    if val is None:
        raise ValueError(f"unparseable integer literal: {text!r}")
    return val


def parse_assume_range(text: str) -> AssumeRange:
    """Parse ``[const op] VAR [op const]`` into an :class:`AssumeRange`.

    Each ``op`` is one of ``<``, ``<=``, ``>``, ``>=``. Mixed-direction
    chains (``LO <= VAR >= HI``) are rejected. Constants accept
    decimal, hex (``0xff``), and TAC's signed hex (``0x-48``).
    """
    m = _ASSUME_RANGE_RX.match(text)
    if m is None:
        raise ValueError(f"unparseable assume-range: {text!r}")
    if m.group("c1") is None and m.group("c2") is None:
        raise ValueError(f"assume-range needs at least one bound: {text!r}")

    var = m.group("var")
    lo: int | None = None
    lo_strict = False
    hi: int | None = None
    hi_strict = False

    def _set_lo(val: int, strict: bool) -> None:
        nonlocal lo, lo_strict
        if lo is not None:
            raise ValueError(f"assume-range gives lo bound twice: {text!r}")
        lo, lo_strict = val, strict

    def _set_hi(val: int, strict: bool) -> None:
        nonlocal hi, hi_strict
        if hi is not None:
            raise ValueError(f"assume-range gives hi bound twice: {text!r}")
        hi, hi_strict = val, strict

    if m.group("c1") is not None:
        c1 = _parse_int_const(m.group("c1"))
        op = m.group("o1")
        # ``LO op VAR``: ``<`` / ``<=`` are lower bounds; ``>`` / ``>=`` are upper.
        if op in ("<=", "<"):
            _set_lo(c1, op == "<")
        else:
            _set_hi(c1, op == ">")
    if m.group("c2") is not None:
        c2 = _parse_int_const(m.group("c2"))
        op = m.group("o2")
        # ``VAR op HI``: ``<`` / ``<=`` are upper bounds; ``>`` / ``>=`` are lower.
        if op in ("<=", "<"):
            _set_hi(c2, op == "<")
        else:
            _set_lo(c2, op == ">")

    return AssumeRange(
        var=var, lo=lo, lo_strict=lo_strict, hi=hi, hi_strict=hi_strict
    )


def _fmt_const(v: int) -> str:
    """Untagged hex literal, signed via the TAC ``0x-N`` form."""
    if v < 0:
        return f"0x-{-v:x}"
    return f"0x{v:x}"


def _build_assume_cmd(ar: AssumeRange) -> AssumeExpCmd:
    """Construct an :class:`AssumeExpCmd` whose ``raw`` is freshly rendered.

    ``LAnd`` is used when both bounds are present; otherwise the single
    comparison is the assume's condition directly.
    """
    var = SymbolRef(ar.var)
    parts: list[TacExpr] = []
    if ar.lo is not None:
        op = "Lt" if ar.lo_strict else "Le"
        parts.append(ApplyExpr(op, (ConstExpr(_fmt_const(ar.lo)), var)))
    if ar.hi is not None:
        op = "Lt" if ar.hi_strict else "Le"
        parts.append(ApplyExpr(op, (var, ConstExpr(_fmt_const(ar.hi)))))
    cond: TacExpr = parts[0] if len(parts) == 1 else ApplyExpr("LAnd", tuple(parts))
    cmd = AssumeExpCmd(raw="", condition=cond)
    return canonicalize_cmd(cmd)


def _inject_assume_ranges(
    program: TacProgram,
    ranges: tuple[AssumeRange, ...],
) -> TacProgram:
    """Insert one ``AssumeExpCmd`` per :class:`AssumeRange`.

    For DSA-static vars (single def), insert immediately after the def
    in the same block. For DSA-dynamic vars (multiple defs), insert as
    the first cmd of every unique successor block of any def-block:
    that's where the def's value enters the post-merge frontier and
    every reachable use is dominated.
    """
    if not ranges:
        return program

    dsa = analyze_dsa(program, strip_var_suffixes=True)
    dynamic = {a.symbol for a in dsa.dynamic_assignments}
    by_id = program.block_by_id()

    inserts: list[tuple[BlockId, int, AssumeExpCmd]] = []
    for ar in ranges:
        canon = _canon(ar.var)
        def_sites: list[tuple[BlockId, int]] = []
        for blk in program.blocks:
            # Module shadows ``enumerate`` with the multi-case enumerator;
            # iterate via index to avoid the collision.
            for idx in range(len(blk.commands)):
                cmd = blk.commands[idx]
                if isinstance(cmd, (AssignExpCmd, AssignHavocCmd)):
                    if _canon(cmd.lhs) == canon:
                        def_sites.append((blk.id, idx))
        if not def_sites:
            raise ValueError(
                f"--assume-range: no def found for variable {ar.var!r}"
            )

        assume_cmd = _build_assume_cmd(ar)
        if canon not in dynamic:
            for (blk_id, idx) in def_sites:
                inserts.append((blk_id, idx + 1, assume_cmd))
        else:
            successors: set[BlockId] = set()
            for (blk_id, _idx) in def_sites:
                blk = by_id.get(blk_id)
                if blk is None:
                    continue
                successors.update(blk.successors)
            for s in successors:
                inserts.append((s, 0, assume_cmd))

    by_block: dict[BlockId, list[tuple[int, AssumeExpCmd]]] = {}
    for blk_id, pos, cmd in inserts:
        by_block.setdefault(blk_id, []).append((pos, cmd))

    new_blocks: list[TacBlock] = []
    for blk in program.blocks:
        if blk.id not in by_block:
            new_blocks.append(blk)
            continue
        cmds = list(blk.commands)
        # Insert in descending position order so earlier insertions
        # don't shift later positions.
        for pos, cmd in sorted(by_block[blk.id], key=lambda x: -x[0]):
            cmds.insert(pos, cmd)
        new_blocks.append(replace(blk, commands=cmds))
    return TacProgram(blocks=new_blocks)


# ----------------------------------------------------- PinPlan / apply()


@dataclass(frozen=True)
class PinPlan:
    """Specification for one pin invocation.

    Fields are tuples (immutable) so plans are hashable and easy to
    record in manifests / traces.
    """

    drops: tuple[BlockId, ...] = ()
    binds: tuple[Bind, ...] = ()
    splits: tuple[BlockId, ...] = ()
    assume_ranges: tuple[AssumeRange, ...] = ()
    cleanup: bool = True


@dataclass(frozen=True)
class PinResult:
    """Single-case result of :func:`apply`.

    Multi-case results (when ``plan.splits`` is non-empty) are
    represented by :class:`CaseSet` and produced by :func:`enumerate`.
    """

    program: TacProgram
    plan: PinPlan
    source_program: TacProgram
    dead_blocks: frozenset[BlockId]
    binds_applied: tuple[Bind, ...]
    rc_binds_applied: tuple[Bind, ...]


def bind(
    program: TacProgram,
    binds: Iterable[Bind],
) -> TacProgram:
    """Public bind primitive: substitute SymbolRef -> ConstExpr.

    Rejects RC variable names. Use :func:`apply` with ``--drop`` (or
    its programmatic equivalent) to mark a block dead — the
    corresponding RC bind is generated automatically as part of the
    drop pipeline.
    """
    binds = tuple(binds)
    for var, _val in binds:
        if is_reachability_var(var):
            raise ValueError(
                f"RC variable {var!r} is externally-defined; use a drop "
                f"to disable its block, not bind()."
            )
    mapping = {var: val for var, val in binds}
    return _substitute_in_program(program, mapping)


def _substitute_with_rc(
    program: TacProgram,
    binds: Mapping[str, ConstExpr],
) -> TacProgram:
    """Internal substitution that doesn't reject RC names. Used by
    :func:`apply` for the auto-generated RC=false binds."""
    return _substitute_in_program(program, binds)


def apply(
    program: TacProgram,
    plan: PinPlan,
    *,
    trace: Trace | None = None,
) -> PinResult:
    """Apply a single-case pin (no splits).

    Pipeline:
        1. Validate the plan (reject RC binds, unknown drop targets,
           etc.) and raise ``ValueError`` with all collected issues.
        2. Phase 1: compute the dead-block closure via
           :func:`compute_dead_blocks`.
        3. Phase 2:
            a. CFG terminator surgery (folds JumpiCmd's whose
               condition becomes constant; rewrites edges to dead
               blocks).
            b. Substitute user binds + auto-RC binds.
            c. Drop havoc defs for dead RC vars.
            d. Remove dead blocks.
            e. Cleanup pass (rewriter; bool-fold + ITE_BOOL +
               ITE_SAME + CP_ALIAS).
        4. Validate post-conditions: no orphans, no dangling jumps.

    The trace receives event records throughout. ``plan.splits`` is
    not honored here — use :func:`enumerate` for split-based
    multi-case enumeration.
    """
    if plan.splits:
        raise ValueError(
            "apply() does not handle plan.splits; use enumerate() instead"
        )
    tr: Trace = trace if trace is not None else NullTrace()
    source = program

    # Pre-condition: RC vars must not appear in JumpiCmd conditions.
    # Hard error if violated — pin's RC-folding model assumes RCs are
    # used only in expression contexts (map definitions / Ite-merges).
    _check_no_rc_in_jumpi_conditions(program)

    # Up-front validation. Collect all issues so the user sees them
    # together rather than a single first-fail.
    user_binds_map = {var: val for var, val in plan.binds}
    issues = validate_plan_against(
        program, drops=plan.drops, binds=user_binds_map
    )
    if issues:
        raise ValueError(
            "ctac pin: plan rejected:\n  - " + "\n  - ".join(issues)
        )

    tr.emit({
        "event": "pin-start",
        "phase": "analyze",
        "schema_version": 1,
        "plan": {
            "drops": list(plan.drops),
            "binds": [(var, val.value) for var, val in plan.binds],
            "splits": list(plan.splits),
            "assume_ranges": [
                {
                    "var": ar.var,
                    "lo": ar.lo,
                    "lo_strict": ar.lo_strict,
                    "hi": ar.hi,
                    "hi_strict": ar.hi_strict,
                }
                for ar in plan.assume_ranges
            ],
            "cleanup": plan.cleanup,
        },
        "source_blocks": len(program.blocks),
    })

    # Phase 1.
    #
    # Compute two dead-set closures:
    #   full_dead = with the user's drops + binds applied
    #   pre_dead  = with NO user input (pure structural orphans of source)
    #
    # Effective drop set = full_dead minus (pre_dead minus user-named).
    # I.e. honor everything the user named, plus their cascade; but don't
    # silently drop pre-existing orphans the user didn't ask about.
    # Those flow through to the output (and post-condition checks are
    # relative, so they pass).
    dead_result = compute_dead_blocks(
        program, plan.drops, user_binds_map, trace=tr
    )
    full_dead = dead_result.dead
    pre_result = compute_dead_blocks(program, (), {})
    pre_dead = pre_result.dead - set(plan.drops)
    dead = full_dead - pre_dead

    # Trace the effective decision: which blocks were preserved as
    # pre-existing orphans, and which we'll actually drop.
    if pre_dead:
        tr.emit({
            "event": "preserved-pre-existing-orphans",
            "phase": "analyze",
            "blocks": sorted(pre_dead),
            "count": len(pre_dead),
        })

    # Build the global bind map (user binds + RC=false for dropped
    # blocks). The dominance-based RC=true component is per-block and
    # is computed below, after CFG surgery + remove.
    rc_binds_false: dict[str, ConstExpr] = {
        reachability_var_name(b): _FALSE for b in dead
    }
    rc_binds_tuple = tuple((k, v) for k, v in rc_binds_false.items())
    global_binds: dict[str, ConstExpr] = {
        **user_binds_map,
        **rc_binds_false,
    }

    for var, _val in plan.binds:
        tr.emit({"event": "user-bind", "phase": "transform", "var": var,
                 "value": _val.value})
    for var, val in rc_binds_tuple:
        tr.emit({"event": "rc-bind", "phase": "transform",
                 "var": var, "value": val.value, "reason": "block_dropped"})

    # Phase 2. Order:
    #   1. CFG surgery (rewrite terminators of preds of dead blocks).
    #   2. Remove dead blocks from the program.
    #   3. Compute dominators on the resulting CFG (the final shape).
    #   4. Build per-block bind maps (global RC=false + per-block
    #      RC=true for blocks dominated by surviving BLKs).
    #   5. Substitute per-block.
    #   6. Purge any leftover RC havocs for dead blocks (in surviving
    #      blocks that hosted them).
    #   7. Cleanup rewriter pass.
    defs = _build_definition_map(program)
    source_def_blocks = _build_def_block_map(program)
    program = _drop_cfg_surgery(program, dead, global_binds, defs)
    program = _remove_blocks(program, dead)

    for b in sorted(dead):
        tr.emit({"event": "block-removed", "phase": "transform", "block": b})

    dominators = _dominator_sets(program)
    per_block = _per_block_bind_maps(
        program, dead, user_binds_map, dominators
    )

    # Trace per-block RC=true bindings (debugging aid; quiet about
    # the global half — already covered by rc-bind / user-bind events).
    for block_id, bm in per_block.items():
        for var, val in bm.items():
            if val.value == "true" and is_reachability_var(_canon(var)):
                tr.emit({
                    "event": "rc-bind", "phase": "transform",
                    "var": var, "value": "true",
                    "reason": "dominator_of_block", "block": block_id,
                })

    program = _substitute_per_block(program, per_block)
    program = _drop_havoc_defs_for_dead_rcs(program, dead)
    program = _fold_lor_rc_self_dominance(program)
    program = _drop_ite_arms_with_dropped_def(
        program, source_defs=source_def_blocks, dead=dead
    )
    if plan.assume_ranges:
        program = _inject_assume_ranges(program, plan.assume_ranges)
        for ar in plan.assume_ranges:
            tr.emit({
                "event": "assume-range-injected",
                "phase": "transform",
                "var": ar.var,
                "lo": ar.lo,
                "lo_strict": ar.lo_strict,
                "hi": ar.hi,
                "hi_strict": ar.hi_strict,
            })

    if plan.cleanup:
        program = _cleanup(program)
        tr.emit({"event": "cleanup-complete", "phase": "transform"})

    # Post-conditions. Order: cheapest structural checks first, then
    # the data-flow checks that depend on a clean CFG.
    #
    # All checks are relative to the source: pin must not *introduce*
    # orphans, UBD, or DSA issues, but pre-existing issues in the input
    # pass through unchanged.
    assert_no_new_orphans(source, program)
    tr.emit({"event": "post-condition-check", "phase": "validate",
             "check": "no_new_orphans", "result": "pass"})
    assert_no_dangling_jumps(program)
    tr.emit({"event": "post-condition-check", "phase": "validate",
             "check": "no_dangling_jumps", "result": "pass"})
    assert_no_new_use_before_def(source, program)
    tr.emit({"event": "post-condition-check", "phase": "validate",
             "check": "no_new_use_before_def", "result": "pass"})
    assert_no_new_dsa_issues(source, program)
    tr.emit({"event": "post-condition-check", "phase": "validate",
             "check": "no_new_dsa_issues", "result": "pass"})

    tr.emit({
        "event": "pin-complete",
        "phase": "validate",
        "blocks_in": len(source.blocks),
        "blocks_out": len(program.blocks),
        "blocks_dropped": len(dead),
    })

    return PinResult(
        program=program,
        plan=plan,
        source_program=source,
        dead_blocks=dead,
        binds_applied=plan.binds,
        rc_binds_applied=rc_binds_tuple,
    )


# ---------------------------------------------------------- enumerate()


@dataclass(frozen=True)
class Case:
    """One case produced by :func:`enumerate`.

    ``kept_predecessors`` records which predecessor was kept for each
    split block, in the same order as ``plan.splits``. The
    ``short_filename`` is a stable, filesystem-safe identifier
    derived from the kept-predecessor selection (filled in by the
    manifest writer; library callers can ignore it).
    """

    program: TacProgram
    kept_predecessors: tuple[tuple[BlockId, BlockId], ...]
    dead_blocks: frozenset[BlockId]


@dataclass(frozen=True)
class CaseSet:
    """Multi-case result of :func:`enumerate`."""

    cases: tuple[Case, ...]
    plan: PinPlan
    source_program: TacProgram
    pruned_vacuous: tuple[tuple[tuple[BlockId, BlockId], ...], ...] = ()


def _predecessors_of(program: TacProgram, block_id: BlockId) -> list[BlockId]:
    """Return the block ids whose CFG successor list contains
    ``block_id``, in source order."""
    out: list[BlockId] = []
    for b in program.blocks:
        if block_id in b.successors:
            out.append(b.id)
    return out


def enumerate(  # noqa: A001 — shadows builtin but matches public API name
    program: TacProgram,
    plan: PinPlan,
    *,
    trace: Trace | None = None,
    keep_vacuous: bool = False,
) -> CaseSet:
    """Enumerate the cross-product of split decisions, applying drop
    + bind for each case.

    For each ``--split BLK`` in ``plan.splits``, all but one
    predecessor of ``BLK`` is added to that case's drop set. The
    cross-product over splits gives the set of cases.

    A case is "vacuous" when its kept-predecessor for some split
    block becomes structurally unreachable in the resulting program
    (e.g. another split's drops severed its access path). Vacuous
    cases are pruned by default; set ``keep_vacuous=True`` to emit
    them anyway.

    Per-case post-conditions (no orphans, no dangling jumps) match
    those of :func:`apply`.
    """
    tr: Trace = trace if trace is not None else NullTrace()

    # Validate split targets exist.
    block_ids = {b.id for b in program.blocks}
    for s in plan.splits:
        if s not in block_ids:
            raise ValueError(f"--split target {s!r} is not a block in the program")

    # For each split, gather predecessors. Skip the split itself if
    # it has no predecessors (vacuous from the start).
    pred_lists: list[list[BlockId]] = []
    for s in plan.splits:
        preds = _predecessors_of(program, s)
        if not preds:
            raise ValueError(
                f"--split target {s!r} has no predecessors; nothing to "
                f"enumerate over"
            )
        pred_lists.append(preds)

    tr.emit({
        "event": "split-enumeration",
        "phase": "analyze",
        "splits": [
            {"block": s, "predecessors": preds}
            for s, preds in zip(plan.splits, pred_lists, strict=True)
        ],
        "case_count_unpruned": _product_size(pred_lists),
    })

    cases: list[Case] = []
    pruned: list[tuple[tuple[BlockId, BlockId], ...]] = []

    for combo in itertools.product(*pred_lists):
        # combo[i] is the kept predecessor of splits[i].
        kept = tuple(zip(plan.splits, combo, strict=True))
        case_drops: list[BlockId] = list(plan.drops)
        for split_block, kept_pred, all_preds in zip(
            plan.splits, combo, pred_lists, strict=True
        ):
            for p in all_preds:
                if p != kept_pred:
                    case_drops.append(p)

        # Build a case-specific plan with no splits (all expanded into drops).
        case_plan = PinPlan(
            drops=tuple(case_drops),
            binds=plan.binds,
            splits=(),
            cleanup=plan.cleanup,
        )

        # Vacuity check: if the kept predecessor becomes structurally
        # unreachable (e.g. another split severed its access path),
        # this case is impossible. Compute the dead set under the
        # full case plan and inspect.
        user_binds_map = {var: val for var, val in plan.binds}
        dead_result = compute_dead_blocks(
            program, case_plan.drops, user_binds_map
        )
        if not keep_vacuous and any(p in dead_result.dead for p in combo):
            tr.emit({
                "event": "case-pruned-vacuous",
                "phase": "analyze",
                "kept_predecessors": list(kept),
                "reason": "kept predecessor became unreachable under the "
                          "drops induced by other splits",
            })
            pruned.append(kept)
            continue

        # Apply this case's drop+bind plan.
        try:
            res = apply(program, case_plan, trace=tr)
        except ValueError as e:
            # The plan was structurally invalid for this case (e.g. no
            # live exit remained). Treat as vacuous-prune unless the
            # caller asked to keep them.
            if keep_vacuous:
                raise
            tr.emit({
                "event": "case-pruned-invalid",
                "phase": "analyze",
                "kept_predecessors": list(kept),
                "reason": str(e),
            })
            pruned.append(kept)
            continue

        cases.append(Case(
            program=res.program,
            kept_predecessors=kept,
            dead_blocks=res.dead_blocks,
        ))

    tr.emit({
        "event": "enumeration-complete",
        "phase": "analyze",
        "case_count": len(cases),
        "pruned_count": len(pruned),
    })

    return CaseSet(
        cases=tuple(cases),
        plan=plan,
        source_program=program,
        pruned_vacuous=tuple(pruned),
    )


def _product_size(lists: Iterable[list]) -> int:
    n = 1
    for lst in lists:
        n *= len(lst)
    return n
