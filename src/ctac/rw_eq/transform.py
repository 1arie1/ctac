"""Lockstep walker that merges ``(orig, rw)`` into one equivalence-check
TAC program.

The walker visits each (same-id) block of ``orig`` and ``rw`` in
lockstep, advancing one or both sides per dispatched rule. It emits a
single merged ``TacProgram`` whose only ``AssertCmd`` instances are
rw-eq's own equivalence checks (``CHK<n> = ...; assert CHK<n>``); the
orig program's own assertions are converted to assumes so downstream
tools (``ua --strategy split`` + ``ctac smt``) verify rwriter
soundness, not the orig's own correctness question.

Rules table
-----------

Code-execution order (NOT rule-number order). The first matching
branch wins; rule 10 is the abort sink.

==  ===========================  =====================================  =======================================  ========
#   Rule                         Trigger                                Emit                                     Advance
==  ===========================  =====================================  =======================================  ========
9   eos lhs                      ``R is None``                          L verbatim                               L
8   eos rhs                      ``L is None``                          R verbatim                               R
7   terminator                   both at JumpCmd / JumpiCmd             one terminator (after equiv check)       both
6   rehavoc window               ``L: X = e``, ``R: havoc X``           shadow window (see §rule 6)              both*
6b  dehavoc window               ``L: havoc X``, ``R: X = e``           lhs constraint window + shadow def +
                                 (def reachable through a benign       uniqueness ``CHK = Eq(X, shadow)``
                                 rhs window)                           (see ``_consume_dehavoc_window``)        both*
1   identical (non-assert)       ``cmd_equiv(L, R)`` and not Assert     L verbatim                               both
2   same-lhs assignment          both AssignExp, ``L.lhs == R.lhs``     ``CHK = Eq(L.rhs, R.rhs); assert CHK; L``  both
5c  resolution pair              lhs (A|P),(A'|P); rhs P                ``CHK = Eq(LAnd(pair), P); assert CHK``
5a  paired assumes               both AssumeExp                         ``CHK = Eq(L.cond, R.cond); assert CHK;
                                                                        assume L.cond [; assume R.cond if differ]``  both
5b  paired asserts               both AssertCmd                         ``CHK = Eq(L.pred, R.pred); assert CHK;
                                                                        assume L.pred [; assume R.pred if differ]``  both
9b  lhs-only DCE                 L is AssignExp/Havoc, ``L.lhs ∉ rhs``  L verbatim                               L
3   rhs-only fresh assignment    R is AssignExp/Havoc, ``R.lhs ∉ lhs``  R verbatim                               R
4   rhs-only assume              R is AssumeExp                         ``CHK = R.cond; assert CHK``             R
4b  lhs-only assume              L is AssumeExp                         ``CHK = L.cond; assert CHK``             L
10  no-match abort               nothing matched                        rich diagnostic, raise                   —
==  ===========================  =====================================  =======================================  ========

* Rule 6 advances the lhs by 1 (past ``X = e``) and the rhs through
  the entire window (havoc + admitted assumes + close).

Rule 6 — rehavoc window (R4A pattern)
-------------------------------------

Triggered when ``L: X = e`` and ``R: havoc X`` with the same X (the
rwriter's R4A "div purification": replace ``X = e`` with ``havoc X;
assume bounds``). The walker mints a fresh shadow ``X__rw_eq<n>``,
emits ``havoc X__rw_eq<n>`` so the shadow has a def site (downstream
encoders treat it as a free SMT const, but the merged TAC is also
structurally valid under ``ctac df --show use-before-def``),
substitutes ``X → X_new`` in each rhs assume the window admits, and
closes on the next non-assume rhs command by emitting:

    assert (e == X_new); X = e

So the post-window state has ``X`` bound to ``e`` (matching orig) and
the shadow's bounds in scope.

Caveat: the window admits the rwriter's post-havoc assumes without
checking they're jointly satisfiable (``--check-feasibility`` inserts
per-window probes; ``--strict`` aborts instead).

Post-walk pass: hoist statics above dynamics
--------------------------------------------

After walking each block, :func:`_hoist_statics_above_dynamics`
reorders any static AssignExpCmd (and its dependent AssertCmd, when
the assert references the assignment's lhs) that landed *after* a
dynamic-classified (parallel-phi merge) assignment to the static
prologue. DSA shape requires ``(static)*(dynamic)*terminator``: rule
2 firing on a phi-merge assignment would otherwise place the static
CHK after a dynamic and break sea_vc's DSA precondition.

Mirrors SSA's "insert after phi nodes" applied to TAC's
parallel-assignment shape (where phi-likes live at end of block).

Assumptions and caveats
-----------------------

1. **Block topology matches (lockstep mode)**: in lockstep mode
   ``orig`` and ``rw`` must have the same set of block ids and the
   same successor list per block. Stuttering mode relaxes this: ``rw``
   may carry a subsequence of ``orig``'s block ids (fewer blocks,
   divergent topology), decomposed at divergence/sync points by
   :func:`_detect_mode` / :func:`analyze_simulation`. Rule 6
   introduces shadow vars only in the entry block; it does not touch
   block topology.

2. **Single namespace**: variable names are preserved across orig and
   rw — the rwriter renames nothing. Rule 6 mints fresh
   ``X__rw_eq<n>`` shadow vars; that's the only walker-introduced
   namespace addition. Rules 2 / 4 / 5 / 6 also mint fresh ``CHK<n>``
   bools for equivalence checks (rule 3 emits its rhs-only command
   verbatim with no CHK).

3. **Asserts → assumes**: the orig's AssertCmds are converted to
   assumes by rule 5b (paired) so the merged program doesn't carry
   the orig's own correctness question. Rule 1 explicitly excludes
   AssertCmds from its "identical → emit verbatim" path so this
   conversion happens for identical asserts too.

4. **A successful assert is automatically an assume downstream**:
   rules 4 and 4b emit ``CHK = cond; assert CHK`` with no following
   ``assume cond``. ``ua --strategy split`` converts non-selected
   asserts to assumes in each per-split file, so other split queries
   see ``assume CHK`` ⇒ ``cond`` true. Rules 5a / 5b *do* emit
   explicit ``assume L.cond`` because their CHK captures the
   *equivalence* of two conditions, not either condition's truth.

5. **Rule 4b assumes the rwriter is allowed to drop only useless
   assumes**: dropping an orig assume is sound iff the assume is
   implied by the rest of the merged state. Rule 4b's CHK catches a
   dropped load-bearing assume. False positives are possible if the
   rwriter is sound on orig's domain but its computation differs on
   orig-unreachable states. The dispatch order pre-empts the most
   common shape of this — a rwriter-introduced fresh assignment
   sitting between an orig assume and its rwriter-side replacement
   assume — by running rules 9b / 3 *before* rules 4 / 4b, so the
   asymmetric remainder gets consumed first and the assumes pair via
   rule 5a. Patterns that survive even that pre-emption (e.g. an orig
   assume with no rwriter-side replacement at all, or a replacement
   that requires multi-cmd reordering across an Assume boundary) will
   still produce a rule-4b CHK.

6. **Hoist post-pass assumes CHKs reference only static / cross-block
   symbols**: a CHK whose RHS references a same-block dynamic symbol
   would be moved before that symbol's definition, breaking data
   flow. No current emission rule produces such a CHK; if one is
   added, the hoist needs a free-var safety check.

7. **Dynamic-symbol classification comes from orig's DSA**: orig and
   rw share block structure (rule 6 adds shadow vars only to the
   entry block, not in the body), so orig's classification suffices.
   A future rwriter rule that adds *body* commands asymmetrically
   would need this revisited.
"""

from __future__ import annotations

import json
from collections import Counter
from dataclasses import replace

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
    LabelCmd,
    SymbolRef,
    TacCmd,
    TacExpr,
)
from ctac.analysis.defuse import extract_def_use
from ctac.analysis.expr_walk import iter_expr_symbols
from ctac.analysis.passes import analyze_dsa
from ctac.analysis.symbols import canonical_symbol
from ctac.ast.subst import subst_symbol
from ctac.graph.cfg import Cfg
from ctac.ir.models import TacBlock, TacProgram
from ctac.rewrite.rules.common import eq_modulo_meta
from ctac.rewrite.rules.store_eq import normalize_store_eq
from ctac.rewrite.unparse import canonicalize_cmd, unparse_cmd
from ctac.rw_eq.dest_emit import emit_dest_write, emit_in_dest_ite
from ctac.rw_eq.model import (
    BlockRef,
    EquivContractError,
    EquivResult,
    RehavocSite,
)
from ctac.rw_eq.sim_precheck import SimDecomposition, analyze_simulation
from ctac.smt.encoding.path_skeleton import reachability_var_name

_TERMINATOR_TYPES = (JumpCmd, JumpiCmd)
_NOISE_TYPES = (AnnotationCmd, LabelCmd)


def emit_equivalence_program(
    orig: TacProgram,
    rw: TacProgram,
    *,
    strict: bool = False,
    check_feasibility: bool = False,
) -> EquivResult:
    """Walk the two programs in lockstep and emit the merged
    equivalence-check program.

    See module docstring for the rule table.

    Args:
        orig, rw: programs with matching block ids and successors.
        strict: abort on rule-6 (rehavoc) instead of admitting.
        check_feasibility: insert per-rehavoc-window ``assert false``
            commands so a downstream solver can detect contradictory
            assumes.

    Raises:
        EquivContractError: structural mismatch (different block ids,
            different successor lists, terminator mismatch, or a
            lockstep step that no rule accepts).
        StructuralSimError: stuttering-mode input (rw is a structural
            sub-CFG of orig) fails the simulation pre-check
            (joint-post-dom violation or shared stutter region).
    """
    decomp = _detect_mode(orig, rw)
    lhs_defined = _collect_defined_symbols(orig)
    rhs_defined = _collect_defined_symbols(rw)
    # Dynamic-symbol classification from orig (DSA on orig). Used to
    # hoist rw-eq's static CHK<n> insertions out of the dynamic
    # parallel-assignment section of any block — DSA shape requires
    # ``(static)*(dynamic)*terminator``, and a static after a dynamic
    # is rejected by sea_vc's precondition check. Orig and rw share
    # block structure (rule 6 is the only walker rule that introduces
    # asymmetry, and it does so via shadow vars in the entry block,
    # not in the body), so orig's classification is sufficient.
    orig_du = extract_def_use(orig)
    orig_dsa = analyze_dsa(orig, def_use=orig_du)
    dynamic_symbols = frozenset(a.symbol for a in orig_dsa.dynamic_assignments)
    state = _WalkerState(
        lhs_defined=lhs_defined,
        rhs_defined=rhs_defined,
        strict=strict,
        check_feasibility=check_feasibility,
    )

    # Stuttering-mode setup: pre-mint DEST_A and IN_DEST_B symbols,
    # build id_of enumeration, and compute LHS predecessor index for
    # IN_DEST ITE construction.
    dest_sym_for: dict[BlockRef, "SymbolRef"] = {}
    in_dest_sym_for: dict[BlockRef, "SymbolRef"] = {}
    id_of: dict[BlockRef, int] = {}
    orig_preds: dict[str, frozenset[str]] = {}
    if decomp is not None:
        id_of = {
            b: i for i, b in enumerate(sorted(decomp.matched, key=lambda x: x.id))
        }
        for A in sorted(decomp.divergence_points, key=lambda x: x.id):
            dest_sym_for[A] = state.fresh_dest_for(A)
        orig_preds = _build_pred_index(orig)
        for B in sorted(decomp.sync_points, key=lambda x: x.id):
            # Skip if B has no LHS preds (rw's entry block case —
            # no IN_DEST CHK needed; resolves the journal's
            # OPEN-entry-block item).
            if orig_preds.get(B.id):
                in_dest_sym_for[B] = state.fresh_in_dest_for(B)

    new_blocks: list[TacBlock] = []
    by_id_rw = rw.block_by_id()
    # ReachabilityCertora<bid> symbols referenced in IN_DEST ITEs. Tracked
    # during the walk so we can declare + havoc them at the entry block
    # afterwards (so use-before-def passes; sea_vc aliases them to its
    # internal BLK_<id> guards downstream).
    rc_vars_referenced: set[str] = set()
    # Iterate orig in topological order. Declared order is usually topo
    # but not guaranteed; Cfg.ordered_blocks() makes the dependency on
    # ordering explicit.
    for orig_b in Cfg(orig).ordered_blocks():
        bref = BlockRef.of(orig_b)

        if decomp is None:
            # Lockstep mode (block-id-isomorphic) — original behavior.
            rw_b = by_id_rw[orig_b.id]
            if list(orig_b.successors) != list(rw_b.successors):
                raise EquivContractError(
                    f"block {orig_b.id}: successor lists differ "
                    f"(orig={orig_b.successors!r}, rw={rw_b.successors!r})"
                )
            new_cmds = _walk_block(orig_b, rw_b, state)
        elif bref in decomp.stutter:
            # Stutter block — LHS-only. Synthesize empty rw block;
            # rule 9 ("eos rhs") emits each LHS cmd verbatim.
            empty_rw_b = TacBlock(id=orig_b.id, successors=[], commands=[])
            new_cmds = _walk_block(orig_b, empty_rw_b, state)
        elif bref in decomp.divergence_points:
            # Divergence common block. Strip rw's terminator so the
            # walker pairs the bodies and rule 9 emits LHS's
            # terminator verbatim once R is exhausted.
            rw_b_orig = by_id_rw[orig_b.id]
            rw_terminator = _last_terminator(rw_b_orig, orig_b.id)
            rw_b_stripped = TacBlock(
                id=orig_b.id,
                successors=[],
                commands=list(rw_b_orig.commands[:-1]),
            )
            new_cmds = _walk_block(orig_b, rw_b_stripped, state)
            # Splice DEST_A := <expr> immediately before LHS's
            # terminator (the last cmd in new_cmds is the LHS
            # terminator, emitted verbatim by rule 9).
            dest_cmd = emit_dest_write(
                divergence=bref,
                rw_terminator=rw_terminator,
                dest_sym=dest_sym_for[bref],
                id_of=id_of,
            )
            new_cmds = _splice_before_terminator(new_cmds, [dest_cmd])
        else:
            # Non-divergence matched block — walk lockstep against
            # the same-id rw block. Successor lists must agree (else
            # the block would be a divergence point).
            rw_b = by_id_rw[orig_b.id]
            if list(orig_b.successors) != list(rw_b.successors):
                raise EquivContractError(
                    f"block {orig_b.id}: non-divergence matched block has "
                    f"mismatched successors "
                    f"(orig={orig_b.successors!r}, rw={rw_b.successors!r}) "
                    f"— this should be a divergence point but the decomp "
                    f"didn't flag it"
                )
            new_cmds = _walk_block(orig_b, rw_b, state)

        # Prepend IN_DEST_B ITE + CHK at sync entry.
        if decomp is not None and bref in in_dest_sym_for:
            lhs_pred_ids = sorted(orig_preds.get(orig_b.id, frozenset()))
            lhs_preds = [BlockRef(id=p) for p in lhs_pred_ids]
            chk_name = state.fresh_chk()
            in_dest_cmds = emit_in_dest_ite(
                sync=bref,
                in_dest_sym=in_dest_sym_for[bref],
                lhs_preds=lhs_preds,
                decomp=decomp,
                id_of=id_of,
                dest_sym_for=dest_sym_for,
                chk_name=chk_name,
            )
            # Track RC vars referenced in this sync's ITE — we declare
            # and havoc them after the walk so use-before-def passes
            # and sea_vc can alias them to its internal BLK_<id> guards.
            for p in lhs_pred_ids:
                rc_vars_referenced.add(reachability_var_name(p))
            # emit_in_dest_ite increments asserts on its own via the
            # AssertCmd it emits; ensure the walker's counter
            # reflects this for downstream `--report` counts.
            state.asserts_emitted += 1
            new_cmds = list(in_dest_cmds) + new_cmds

        new_cmds = _hoist_statics_above_dynamics(new_cmds, dynamic_symbols)
        new_blocks.append(
            TacBlock(id=orig_b.id, successors=list(orig_b.successors), commands=new_cmds)
        )

    # Post-walk: declare and havoc the ReachabilityCertora<bid> symbols
    # the IN_DEST ITEs reference. sea_vc aliases ``ReachabilityCertora<id>``
    # → ``BLK_<id>`` (the encoder's internal block-reachability guard)
    # via define-fun, so the havoc'd value is overridden semantically;
    # but the input use-before-def check fires before sea_vc, hence
    # the explicit havoc def. No-op when the orig program already
    # declared / havoc'd these symbols (we let the parser handle
    # any duplicate declarations downstream).
    if decomp is not None and rc_vars_referenced and new_blocks:
        for rc in sorted(rc_vars_referenced):
            state.extra_symbols.append((rc, "bool"))
        entry = new_blocks[0]
        havoc_cmds: list[TacCmd] = [
            canonicalize_cmd(AssignHavocCmd(raw="", lhs=rc))
            for rc in sorted(rc_vars_referenced)
        ]
        new_blocks[0] = TacBlock(
            id=entry.id,
            successors=list(entry.successors),
            commands=havoc_cmds + list(entry.commands),
        )

    # Stash the id_of mapping at the head of the entry block so
    # downstream htac printers can annotate DEST_<bid> / IN_DEST_<bid>
    # integer constants with the source block id (huge readability
    # win when manually validating the simulation).
    if decomp is not None and id_of and new_blocks:
        id_map_payload = {str(i): b.id for b, i in id_of.items()}
        annot = AnnotationCmd(
            raw="",
            payload=(
                "JSON"
                + json.dumps(
                    {
                        "key": {"name": "rw-eq.id-of"},
                        "value": id_map_payload,
                    },
                    sort_keys=True,
                    separators=(",", ":"),
                )
            ),
        )
        annot = canonicalize_cmd(annot)
        entry = new_blocks[0]
        new_blocks[0] = TacBlock(
            id=entry.id,
            successors=list(entry.successors),
            commands=[annot, *entry.commands],
        )

    if decomp is not None:
        stutter_tup = tuple(sorted(decomp.stutter, key=lambda b: b.id))
        div_tup = tuple(sorted(decomp.divergence_points, key=lambda b: b.id))
        sync_tup = tuple(sorted(decomp.sync_points, key=lambda b: b.id))
    else:
        stutter_tup = ()
        div_tup = ()
        sync_tup = ()

    return EquivResult(
        program=TacProgram(blocks=new_blocks),
        rule_hits=dict(state.rule_hits),
        rehavoc_sites=tuple(state.rehavoc_sites),
        extra_symbols=tuple(state.extra_symbols),
        asserts_emitted=state.asserts_emitted,
        feasibility_asserts_emitted=state.feasibility_asserts_emitted,
        stutter_blocks=stutter_tup,
        divergence_points=div_tup,
        sync_points=sync_tup,
    )


def _detect_mode(orig: TacProgram, rw: TacProgram) -> SimDecomposition | None:
    """Decide whether to walk in lockstep or stuttering mode.

    Returns ``None`` for lockstep (block-id-isomorphic inputs) or the
    :class:`SimDecomposition` for stuttering. Raises
    :class:`EquivContractError` for inputs that are neither shape (rw
    not a subsequence of orig).
    """
    orig_ids = [b.id for b in orig.blocks]
    rw_ids = [b.id for b in rw.blocks]
    if orig_ids == rw_ids:
        return None  # lockstep
    # Stuttering candidate: rw's ids must be a (proper) subsequence of orig's.
    if set(rw_ids) - set(orig_ids):
        # rw has ids orig doesn't — not a structural sub-CFG.
        _check_block_set(orig, rw)  # delegate to existing diagnostic
    if not _is_subsequence(rw_ids, orig_ids):
        _check_block_set(orig, rw)  # ordering wrong; delegate diagnostic
    return analyze_simulation(orig, rw)


def _is_subsequence(needle: list[str], haystack: list[str]) -> bool:
    """Whether ``needle``'s elements appear in ``haystack`` in order
    (gaps allowed). Used to verify rw's blocks are a topological
    subsequence of orig's blocks."""
    it = iter(haystack)
    return all(x in it for x in needle)


def _build_pred_index(program: TacProgram) -> dict[str, frozenset[str]]:
    """Inverse of ``block.successors``: ``bid -> {predecessor_bids}``."""
    preds: dict[str, set[str]] = {b.id: set() for b in program.blocks}
    for b in program.blocks:
        for s in b.successors:
            preds.setdefault(s, set()).add(b.id)
    return {k: frozenset(v) for k, v in preds.items()}


def _last_terminator(block: TacBlock, block_id: str) -> JumpCmd | JumpiCmd:
    if not block.commands:
        raise EquivContractError(
            f"block {block_id}: empty command list — no terminator to extract"
        )
    last = block.commands[-1]
    if not isinstance(last, _TERMINATOR_TYPES):
        raise EquivContractError(
            f"block {block_id}: last command is not a terminator "
            f"({type(last).__name__})"
        )
    return last


def _splice_before_terminator(
    cmds: list[TacCmd], to_insert: list[TacCmd]
) -> list[TacCmd]:
    """Insert ``to_insert`` just before the trailing terminator of
    ``cmds``. Pure helper used to put DEST_A := <expr> writes between
    the body and the LHS terminator."""
    if not cmds or not isinstance(cmds[-1], _TERMINATOR_TYPES):
        # No terminator at the end (rare — would indicate a malformed
        # block); append at the end.
        return cmds + to_insert
    return cmds[:-1] + to_insert + [cmds[-1]]


def _check_block_set(orig: TacProgram, rw: TacProgram) -> None:
    orig_ids = [b.id for b in orig.blocks]
    rw_ids = [b.id for b in rw.blocks]
    if orig_ids != rw_ids:
        # Report the first divergence to keep the error short.
        for o, r in zip(orig_ids, rw_ids):
            if o != r:
                raise EquivContractError(
                    f"block-order mismatch at {o!r} vs {r!r} "
                    f"(orig has {len(orig_ids)} blocks, rw has {len(rw_ids)})"
                )
        raise EquivContractError(
            f"block-count mismatch: orig has {len(orig_ids)}, rw has {len(rw_ids)}"
        )


def _collect_defined_symbols(program: TacProgram) -> frozenset[str]:
    """Symbols that appear as LHS of an AssignExpCmd or AssignHavocCmd
    anywhere in ``program``. Used to decide whether a symbol introduced
    on the RW side is "fresh" (rule 3)."""
    names: set[str] = set()
    for b in program.blocks:
        for c in b.commands:
            if isinstance(c, (AssignExpCmd, AssignHavocCmd)):
                names.add(c.lhs)
    return frozenset(names)


def _hoist_statics_above_dynamics(
    cmds: list[TacCmd], dynamic_symbols: frozenset[str]
) -> list[TacCmd]:
    """Reorder ``cmds`` so any static AssignExpCmd (and its dependent
    AssertCmd, when the assert refers to the assignment's lhs) appears
    *before* any dynamic-classified assignment in the block.

    DSA shape requires ``(static)*(dynamic)*terminator``: once a dynamic
    assignment appears, no further static assignments may follow.
    rw-eq's emit sites (rule 2 / 4 / 5 / 6) splice ``CHK<n> = Eq(...);
    AssertCmd CHK<n>`` next to the original-program command they're
    checking, which can land them in the block's dynamic phi-merge
    section. This helper hoists those check pairs to the static prologue
    so the merged program still satisfies DSA shape.

    Mirrors SSA's "insert after phi nodes" convention applied to TAC's
    parallel-assignment shape (where phi-like assignments live at the
    end of a block, just before the terminator). Idempotent.

    Caveat: a hoisted CHK whose RHS references a same-block dynamic
    symbol would be moved before that symbol's definition, breaking
    data flow. Today every emitted CHK references only static or
    cross-block symbols, so this is safe; if a future emission rule
    breaks the assumption, add a free-var check here.
    """
    first_dyn = None
    for i, c in enumerate(cmds):
        if isinstance(c, (AssignExpCmd, AssignHavocCmd)) and c.lhs in dynamic_symbols:
            first_dyn = i
            break
    if first_dyn is None:
        return cmds

    prefix = list(cmds[:first_dyn])
    rest_kept: list[TacCmd] = []
    moved: list[TacCmd] = []

    i = first_dyn
    while i < len(cmds):
        cmd = cmds[i]
        if isinstance(cmd, AssignExpCmd) and cmd.lhs not in dynamic_symbols:
            group: list[TacCmd] = [cmd]
            j = i + 1
            while j < len(cmds):
                nxt = cmds[j]
                if (
                    isinstance(nxt, AssertCmd)
                    and isinstance(nxt.predicate, SymbolRef)
                    and nxt.predicate.name == cmd.lhs
                ):
                    group.append(nxt)
                    j += 1
                else:
                    break
            moved.extend(group)
            i = j
        else:
            rest_kept.append(cmd)
            i += 1

    return prefix + moved + rest_kept


class _WalkerState:
    def __init__(
        self,
        *,
        lhs_defined: frozenset[str],
        rhs_defined: frozenset[str],
        strict: bool,
        check_feasibility: bool,
    ) -> None:
        self.lhs_defined = lhs_defined
        self.rhs_defined = rhs_defined
        # Canonical view for symbol-level checks against expression
        # uses (iter_expr_symbols canonicalizes; def-side names are raw).
        self.rhs_defined_canon = frozenset(
            canonical_symbol(n) for n in rhs_defined
        )
        self.strict = strict
        self.check_feasibility = check_feasibility
        self.rule_hits: Counter[str] = Counter()
        self.rehavoc_sites: list[RehavocSite] = []
        self.extra_symbols: list[tuple[str, str]] = []
        self._fresh_chk = 0
        self._fresh_shadow = 0
        self.asserts_emitted = 0
        self.feasibility_asserts_emitted = 0

    def fresh_chk(self) -> str:
        n = self._fresh_chk
        self._fresh_chk += 1
        name = f"CHK{n}"
        self.extra_symbols.append((name, "bool"))
        return name

    def fresh_shadow(self, base: str, sort: str) -> str:
        n = self._fresh_shadow
        self._fresh_shadow += 1
        name = f"{base}__rw_eq{n}"
        self.extra_symbols.append((name, sort))
        return name

    def fresh_dest_for(self, divergence: BlockRef) -> SymbolRef:
        """Mint ``DEST_<block_id>`` (sort ``int``). Static (single def
        at A's terminator). Returns the typed handle; the underlying
        name is also registered in ``extra_symbols`` for symbol-table
        wiring downstream."""
        name = f"DEST_{divergence.id}"
        self.extra_symbols.append((name, "int"))
        return SymbolRef(name=name)

    def fresh_in_dest_for(self, sync: BlockRef) -> SymbolRef:
        """Mint ``IN_DEST_<block_id>`` (sort ``int``). Static (single
        def at B's entry, the ITE-chain assignment)."""
        name = f"IN_DEST_{sync.id}"
        self.extra_symbols.append((name, "int"))
        return SymbolRef(name=name)

    def hit(self, rule: str) -> None:
        self.rule_hits[rule] += 1

    def record_rehavoc(self, site: RehavocSite) -> None:
        self.rehavoc_sites.append(site)


def _meaningful_indices(commands: list[TacCmd]) -> list[int]:
    """Indices of commands that aren't pure noise (AnnotationCmd /
    LabelCmd)."""
    return [i for i, c in enumerate(commands) if not isinstance(c, _NOISE_TYPES)]


def _emit_eq_assert(
    state: _WalkerState,
    lhs_expr: TacExpr,
    rhs_expr: TacExpr,
    *,
    block_id: str,
    cmd_index: int,
    kind: str,
) -> list[TacCmd]:
    """Produce the three-command shape: CHK = Eq(lhs, rhs); assert CHK."""
    chk = state.fresh_chk()
    eq_expr = ConstExpr("true") if lhs_expr == rhs_expr else _eq(lhs_expr, rhs_expr)
    # Reduce ``Eq(Store(M, k1, v1), Store(M, k2, v2))`` to a conjunction of
    # index/value equalities at emit time. Store-typed equality is sound but
    # sea_vc cannot lower register-level Store, and rw-eq's contract makes
    # the strengthening behaviorally equivalent here. See
    # rewrite.rules.store_eq for the soundness argument.
    eq_expr = normalize_store_eq(eq_expr) or eq_expr
    out: list[TacCmd] = [
        canonicalize_cmd(AssignExpCmd(raw="", lhs=chk, rhs=eq_expr)),
        canonicalize_cmd(
            AssertCmd(
                raw="",
                predicate=SymbolRef(chk),
                message=f"rw-eq:{block_id}:{cmd_index} {kind}",
            )
        ),
    ]
    state.asserts_emitted += 1
    return out


def _emit_feasibility_assert(
    state: _WalkerState,
    *,
    block_id: str,
    cmd_index: int,
    kind: str,
) -> list[TacCmd]:
    out = [
        canonicalize_cmd(
            AssertCmd(
                raw="",
                predicate=ConstExpr("false"),
                message=f"rw-eq-feasibility:{block_id}:{cmd_index} {kind}",
            )
        )
    ]
    state.feasibility_asserts_emitted += 1
    return out


def _eq(a: TacExpr, b: TacExpr) -> TacExpr:
    from ctac.ast.nodes import ApplyExpr

    return ApplyExpr(op="Eq", args=(a, b))


def _cmd_equiv(a: TacCmd, b: TacCmd) -> bool:
    """Structural equality modulo ``raw`` and ``meta_index``."""
    if type(a) is not type(b):
        return False
    if isinstance(a, AssignExpCmd) and isinstance(b, AssignExpCmd):
        return a.lhs == b.lhs and a.rhs == b.rhs
    if isinstance(a, AssignHavocCmd) and isinstance(b, AssignHavocCmd):
        return a.lhs == b.lhs
    if isinstance(a, AssumeExpCmd) and isinstance(b, AssumeExpCmd):
        return a.condition == b.condition
    if isinstance(a, AssertCmd) and isinstance(b, AssertCmd):
        return a.predicate == b.predicate and a.message == b.message
    if isinstance(a, JumpCmd) and isinstance(b, JumpCmd):
        return a.target == b.target
    if isinstance(a, JumpiCmd) and isinstance(b, JumpiCmd):
        return (
            a.then_target == b.then_target
            and a.else_target == b.else_target
            and a.condition == b.condition
        )
    return False


def _safe_unparse(cmd: TacCmd) -> str:
    """Best-effort command rendering for diagnostics. Falls back to the
    raw text or a type tag if unparse can't handle the shape."""
    try:
        return unparse_cmd(cmd)
    except Exception:
        raw = getattr(cmd, "raw", "") or ""
        return raw if raw else f"<{type(cmd).__name__}>"


def _format_cmd_window(
    cmds: list[TacCmd], i: int, *, before: int = 2, after: int = 1
) -> str:
    """Render ``cmds[i]`` plus a small window of surrounding commands,
    one per line, with ``>>`` marking the focus position. Used in
    diagnostics so the user sees not just the failing pair but a few
    commands of context on each side."""
    lo = max(0, i - before)
    hi = min(len(cmds), i + after + 1)
    if lo >= len(cmds):
        return "    (end of block)"
    lines: list[str] = []
    for k in range(lo, hi):
        marker = ">>" if k == i else "  "
        lines.append(f"    {marker} [{k:>3}] {_safe_unparse(cmds[k])}")
    return "\n".join(lines)


def _diagnose_no_match(L: TacCmd, R: TacCmd) -> str:
    """One-line hint for the most common rule-10 fall-through patterns.
    Empty string when nothing useful to add."""
    if isinstance(L, AssumeExpCmd) and isinstance(
        R, (AssignExpCmd, AssignHavocCmd)
    ):
        return (
            "hint: lhs has an assume but rhs has an assignment to a "
            "name that already exists on the lhs. The rewriter likely "
            "reordered an assume past an assignment, or a rule "
            "introduced a fresh name with the same identifier as an "
            "existing one. Try `ctac rw --report` and look for rules "
            "that reorder commands."
        )
    if isinstance(L, (AssignExpCmd, AssignHavocCmd)) and isinstance(
        R, AssumeExpCmd
    ):
        return (
            "hint: lhs has an assignment but rhs has an assume — "
            "the rewriter likely lifted a side condition into an "
            "assume on the rhs without a matching command on the lhs."
        )
    if isinstance(L, AssertCmd) and not isinstance(R, AssertCmd):
        return (
            "hint: lhs has an assert but rhs does not — the rewriter "
            "may have dropped the assertion (rule 5b expects matching "
            "asserts on both sides)."
        )
    if isinstance(R, AssertCmd) and not isinstance(L, AssertCmd):
        return (
            "hint: rhs has an assert that lhs lacks — the rewriter "
            "introduced an assertion (rule 5b expects matching asserts "
            "on both sides)."
        )
    return ""


def _format_no_rule_match_error(
    *,
    orig_block_id: str,
    lhs_cmds: list[TacCmd],
    rhs_cmds: list[TacCmd],
    li: int,
    ri: int,
    state: "_WalkerState",
) -> str:
    """Build the rule-10 diagnostic. Includes pretty-printed command
    text on each side, a small surrounding-context window, and a
    pattern-specific hint when the (lhs, rhs) shape is a known case."""
    L = lhs_cmds[li]
    R = rhs_cmds[ri]
    hint = _diagnose_no_match(L, R)
    rhs_lhs_overlap = (
        isinstance(R, (AssignExpCmd, AssignHavocCmd))
        and R.lhs in state.lhs_defined
    )
    overlap_note = (
        f"\n  rhs assigns to {R.lhs!r} which is also defined on the lhs "
        f"side — rule 3 (fresh-rhs) declined."
        if rhs_lhs_overlap
        else ""
    )
    parts = [
        f"block {orig_block_id}: lockstep step does not match any rule",
        f"  lhs[{li}]: {type(L).__name__}: {_safe_unparse(L)}",
        f"  rhs[{ri}]: {type(R).__name__}: {_safe_unparse(R)}",
        f"  lhs context (block {orig_block_id}):",
        _format_cmd_window(lhs_cmds, li),
        f"  rhs context (block {orig_block_id}):",
        _format_cmd_window(rhs_cmds, ri),
    ]
    if overlap_note:
        parts.append(overlap_note.lstrip("\n"))
    if hint:
        parts.append(f"  {hint}")
    return "\n".join(parts)


def _walk_block(
    orig_block: TacBlock, rw_block: TacBlock, state: _WalkerState
) -> list[TacCmd]:
    output: list[TacCmd] = []
    lhs_cmds = orig_block.commands
    rhs_cmds = rw_block.commands
    li = 0
    ri = 0
    # Indices of lhs assumes already consumed out of order (rule 5c
    # pairs a resolution partner that sits a few assumes ahead).
    lhs_skip: set[int] = set()

    def _peek(cmds: list[TacCmd], i: int) -> tuple[TacCmd | None, int]:
        # Skip noise.
        while i < len(cmds) and isinstance(cmds[i], _NOISE_TYPES):
            output.append(cmds[i])  # echo annotations from whichever side we're skipping past
            i += 1
        if i >= len(cmds):
            return None, i
        return cmds[i], i

    # The above closure has a side-effect (echoing noise into output) that
    # only fires the first time a side's noise is consumed. To keep the
    # ordering predictable and avoid double-emission, peek lhs and rhs
    # noise separately *outside* the walker loop. Simpler implementation
    # uses a non-side-effecting peek and explicit advance.

    def peek(
        cmds: list[TacCmd], i: int, skip: set[int] | None = None
    ) -> tuple[TacCmd | None, int]:
        while i < len(cmds) and (
            isinstance(cmds[i], _NOISE_TYPES) or (skip and i in skip)
        ):
            i += 1
        if i >= len(cmds):
            return None, i
        return cmds[i], i

    while True:
        L, li_new = peek(lhs_cmds, li, lhs_skip)
        R, ri_new = peek(rhs_cmds, ri)
        # Echo skipped lhs noise into output (preserves comments and
        # snippet annotations from the orig program for inspection).
        # Indices in lhs_skip were already emitted by rule 5c.
        for k in range(li, li_new):
            if k not in lhs_skip:
                output.append(lhs_cmds[k])
        li = li_new
        # rhs noise is dropped silently (the orig already carries the
        # informational annotations; rhs's are likely the same or
        # rewriter-internal).
        ri = ri_new

        if L is None and R is None:
            break

        # Rule 9: lhs has more, rhs exhausted.
        if R is None:
            output.append(L)
            li += 1
            state.hit("9_lhs_only")
            continue

        # Rule 8: rhs has more, lhs exhausted.
        if L is None:
            output.append(R)
            ri += 1
            state.hit("8_rhs_only")
            continue

        # Terminator handling (rule 7): pair matching terminators.
        # When ONLY one side is at a terminator, fall through — rules
        # 9b (lhs-only DCE), 4 (rhs-only assume), and 3 (rhs-only
        # fresh assignment) will consume the asymmetric remainder and
        # the walker eventually re-meets at the terminator. This is
        # essential when the rewriter inserts new commands just before
        # the entry block's terminator (e.g. CSE's TCSE<n> hoists,
        # R4A's havoc + bound, ITE_PURIFY's TB<n> introductions): the
        # rhs entry block grows additional rhs-only commands that the
        # orig doesn't have, and rule 3 must get a chance to consume
        # them before the terminator check fires. Rule 10 catches real
        # asymmetries that rules 9b/4/3 can't handle.
        l_term = isinstance(L, _TERMINATOR_TYPES)
        r_term = isinstance(R, _TERMINATOR_TYPES)
        if l_term and r_term:
            if not _cmd_equiv(L, R):
                raise EquivContractError(
                    f"block {orig_block.id}: terminator mismatch"
                )
            output.append(L)
            li += 1
            ri += 1
            state.hit("7_terminator")
            continue

        # Rule 6: rehavoc window — lhs `X = e`, rhs `havoc X` with same X.
        if (
            isinstance(L, AssignExpCmd)
            and isinstance(R, AssignHavocCmd)
            and L.lhs == R.lhs
        ):
            if state.strict:
                raise EquivContractError(
                    f"block {orig_block.id}: rule-6 rehavoc of {L.lhs} "
                    f"hit under --strict"
                )
            ri = _consume_rehavoc_window(
                output=output,
                lhs=L,
                lhs_block_id=orig_block.id,
                lhs_cmd_index=li,
                rhs_cmds=rhs_cmds,
                ri_after_havoc=ri + 1,
                state=state,
            )
            li += 1
            state.hit("6_rehavoc")
            continue

        # Rule 6b: dehavoc window — lhs `havoc X`, rhs reaches `X = e`
        # through a benign window. unpurify_div's shape: the orig
        # carries a frontend-purified division (havoc + Euclidean
        # bounds via temp chains); the rewriter recovered the def and
        # dropped the temps. Mirror of rule 6.
        if isinstance(L, AssignHavocCmd):
            def_idx = _scan_dehavoc_def(
                rhs_cmds, ri, L.lhs, state.lhs_defined
            )
            if def_idx is not None:
                if state.strict:
                    raise EquivContractError(
                        f"block {orig_block.id}: rule-6b dehavoc of "
                        f"{L.lhs} hit under --strict"
                    )
                li, ri = _consume_dehavoc_window(
                    output=output,
                    lhs_havoc=L,
                    lhs_block_id=orig_block.id,
                    lhs_cmds=lhs_cmds,
                    li_after_havoc=li + 1,
                    rhs_cmds=rhs_cmds,
                    ri=ri,
                    def_idx=def_idx,
                    state=state,
                )
                state.hit("6b_dehavoc")
                continue

        # Rule 1: identical command on both sides.
        # AssertCmds are excluded — they must always go through rule
        # 5b so the orig's predicate gets emitted as an `assume` in
        # the merged program (the only AssertCmds in the merged
        # program should be rw-eq's own equivalence checks). Without
        # the AssertCmd exclusion, identical orig asserts pass through
        # verbatim and downstream tools (ua --strategy split) treat
        # them as assertion sites — leaking the orig's correctness
        # question into the rwriter-soundness verification.
        if _cmd_equiv(L, R) and not isinstance(L, AssertCmd):
            output.append(L)
            li += 1
            ri += 1
            state.hit("1_identical")
            continue

        # Rule 2: same LHS assignment, different RHS.
        # Emit the equivalence check FIRST (CHK<n> = Eq(L.rhs, R.rhs);
        # assert CHK<n>), then L's assignment. The check doesn't
        # reference L.lhs, so the order is semantically equivalent —
        # but it matters for DSA shape: when L's lhs is a dynamic
        # symbol (parallel-phi merge variable), placing the static
        # CHK assignment after it creates a static-after-dynamic shape
        # violation that downstream tools (sea_vc encoder's DSA
        # precondition check) reject.
        if (
            isinstance(L, AssignExpCmd)
            and isinstance(R, AssignExpCmd)
            and L.lhs == R.lhs
        ):
            output.extend(
                _emit_eq_assert(
                    state,
                    L.rhs,
                    R.rhs,
                    block_id=orig_block.id,
                    cmd_index=li,
                    kind="assignment",
                )
            )
            output.append(L)
            li += 1
            ri += 1
            state.hit("2_assignment_diff")
            continue

        # Rule 4c: lhs assume over a dead lhs island — EVERY symbol in
        # its condition is one the rw side doesn't define at all (e.g.
        # a summary-output havoc slot whose every use the equate-aware
        # lift redirected to the value register; DCE then removed the
        # slot and its bound on the rw side). Such an assume has no rw
        # twin in any form, so it is neither a droppable fact (rule
        # 4b's CHK would wrongly demand a constraint on a havoc be
        # *valid*) nor pairable (rule 5a would mis-pair it against an
        # unrelated rw assume and skew the whole stream). Emit
        # verbatim: the merged program keeps orig's constraint in
        # force for every downstream obligation.
        #
        # The gate is ALL-dead deliberately: an assume mixing dead and
        # live symbols (e.g. an equate whose value side CP renamed —
        # lhs ``R137 == R472`` vs rw ``R137 == R469``) still has a
        # positional rw twin, and 5a's CHK over the pair discharges
        # from the lhs def chain. Consuming those here skews the
        # streams and mis-pairs everything after.
        #
        # Caveat mirrors rule 6: if the island's constraints are
        # jointly infeasible, orig pruned paths that rw keeps — not
        # detected by default (--check-feasibility territory).
        if isinstance(L, AssumeExpCmd):
            l_syms = list(iter_expr_symbols(L.condition))
            has_dead = any(
                sym not in state.rhs_defined_canon for sym in l_syms
            )
            if (
                l_syms
                and has_dead
                and not _assume_ahead(rhs_cmds, ri, L.condition)
            ):
                output.append(L)
                li += 1
                state.hit("4c_lhs_dead_island_assume")
                continue

        # Rule 5a: both AssumeExpCmd.
        if isinstance(L, AssumeExpCmd) and isinstance(R, AssumeExpCmd):
            # Tautology absorption: CP on the rw side propagates a
            # slot-equate into itself (``assume X == V`` becomes
            # ``assume V == V``) after renaming X's uses to V. The
            # renames are verified per use site by rule 2 (each CHK
            # discharges via the equate, emitted as an assume below);
            # the equate-site CHK itself would wrongly demand the
            # equate be implied *before* it is assumed. Emit L's
            # constraint, skip the CHK.
            if (
                isinstance(R.condition, ApplyExpr)
                and R.condition.op == "Eq"
                and len(R.condition.args) == 2
                and R.condition.args[0] == R.condition.args[1]
            ):
                output.append(L)
                li += 1
                ri += 1
                state.hit("5a_tautology_absorb")
                continue
            # Alignment lookahead: the rewriter inserts assumes the
            # orig doesn't have (e.g. materialize_havoc_equate_bounds'
            # duplicated bounds) and positional pairing would skew at
            # each insertion, mis-pairing every assume after it. If
            # L's EXACT condition appears a little further down the
            # rhs assume run, the current R is such an insertion:
            # consume it rule-4 style (rhs-only CHK) and let the
            # streams re-meet. Symmetric check for lhs-side extras.
            if L.condition != R.condition:
                if _assume_ahead(rhs_cmds, ri + 1, L.condition):
                    output.extend(
                        _emit_eq_assert_for_assume(
                            state,
                            R.condition,
                            block_id=orig_block.id,
                            cmd_index=li,
                        )
                    )
                    ri += 1
                    state.hit("4_rhs_assume")
                    continue
                if _assume_ahead(lhs_cmds, li + 1, R.condition):
                    output.extend(
                        _emit_eq_assert_for_assume(
                            state,
                            L.condition,
                            block_id=orig_block.id,
                            cmd_index=li,
                            kind="lhs-only-assume",
                        )
                    )
                    li += 1
                    state.hit("4b_lhs_assume")
                    continue
                # Rule 5c: resolution pair. dedup_assumes replaces the
                # first of {(A | P), (A' | P)} with P and drops the
                # second, so the rhs P meets lhs (A | P) here with the
                # partner a few assumes ahead. The CHK carries the
                # entire argument -- Eq(LAnd(pair), P) is what z3
                # verifies, so the trigger needs no negation
                # reasoning and a wrong pass shows up as a SAT CHK.
                # Both originals are emitted (constraints stay in
                # force); the partner index is skipped when the walk
                # reaches it.
                if (
                    isinstance(L.condition, ApplyExpr)
                    and L.condition.op == "LOr"
                    and len(L.condition.args) == 2
                    and any(
                        eq_modulo_meta(arg, R.condition)
                        for arg in L.condition.args
                    )
                ):
                    partner = _resolution_partner_ahead(
                        lhs_cmds, li + 1, R.condition, lhs_skip
                    )
                    if partner is not None:
                        pi, L2 = partner
                        output.extend(
                            _emit_eq_assert(
                                state,
                                ApplyExpr(
                                    "LAnd",
                                    (L.condition, L2.condition),
                                ),
                                R.condition,
                                block_id=orig_block.id,
                                cmd_index=li,
                                kind="assume",
                            )
                        )
                        output.append(L)
                        output.append(L2)
                        lhs_skip.add(pi)
                        li += 1
                        ri += 1
                        state.hit("5c_resolution_pair")
                        continue
            output.extend(
                _emit_eq_assert(
                    state,
                    L.condition,
                    R.condition,
                    block_id=orig_block.id,
                    cmd_index=li,
                    kind="assume",
                )
            )
            output.append(L)
            if L.condition != R.condition:
                output.append(R)
            li += 1
            ri += 1
            state.hit("5a_assume_pair")
            continue

        # Rule 5b: both AssertCmd. Original asserts turn into assumes
        # in the merged program; only the equivalence check remains
        # as an assert.
        if isinstance(L, AssertCmd) and isinstance(R, AssertCmd):
            output.extend(
                _emit_eq_assert(
                    state,
                    L.predicate,
                    R.predicate,
                    block_id=orig_block.id,
                    cmd_index=li,
                    kind="assert",
                )
            )
            output.append(
                canonicalize_cmd(AssumeExpCmd(raw="", condition=L.predicate))
            )
            if L.predicate != R.predicate:
                output.append(
                    canonicalize_cmd(AssumeExpCmd(raw="", condition=R.predicate))
                )
            li += 1
            ri += 1
            state.hit("5b_assert_pair")
            continue

        # Rules 9b and 3 — "consume the asymmetric remainder" — both
        # run *before* rules 4 / 4b (the unpaired-assume CHKs).
        #
        # 9b eats an lhs-only DCE'd assignment; 3 eats a rhs-only fresh
        # assignment. When either side has a soon-to-be-DCE'd or
        # rwriter-introduced intermediate sitting opposite the other
        # side's assume, eating the asymmetric assignment first lets
        # the next dispatch pair the assumes via rule 5a (or via 5b /
        # 1 / 2 if the next-up commands are asserts / identical /
        # same-lhs assignments).
        #
        # If we let rule 4 / 4b fire first, the corresponding-side
        # assume gets emitted as an unpaired CHK and the matching
        # assume on the other side has nothing left to pair with —
        # the walker emits two unpaired CHKs where one paired CHK
        # was the right encoding. (Concretely: kev-kvault
        # `shares_to_burn_consistency` had an orig
        # ``assume R55 == R53`` opposite a rwriter-introduced
        # ``TB6 = R179 == 0`` followed by the rwriter's replacement
        # case-split assume; before the reorder, rule 4b consumed the
        # orig assume against an unprepared rhs cursor and the CHK
        # came back SAT.)

        # Rule 9b: lhs has an assignment whose LHS isn't defined in rhs
        # at all — DCE removed it. Emit verbatim, advance LHS only. (The
        # bare rule 9 only handles end-of-stream DCE; this handles the
        # mid-stream case.)
        if (
            isinstance(L, (AssignExpCmd, AssignHavocCmd))
            and L.lhs not in state.rhs_defined
        ):
            output.append(L)
            li += 1
            state.hit("9b_lhs_dce")
            continue

        # Rule 3: rhs-introduced fresh symbol. Emit verbatim, advance
        # RHS only. Symmetric to 9b.
        if (
            isinstance(R, (AssignExpCmd, AssignHavocCmd))
            and R.lhs not in state.lhs_defined
        ):
            output.append(R)
            ri += 1
            state.hit("3_fresh_rhs")
            continue

        # Rule 4: rhs-only assume.
        if isinstance(R, AssumeExpCmd):
            output.extend(
                _emit_eq_assert_for_assume(
                    state, R.condition, block_id=orig_block.id, cmd_index=li,
                )
            )
            ri += 1
            state.hit("4_rhs_assume")
            continue

        # Rule 4b: lhs-only assume. The orig has a constraint at this
        # position that the rhs doesn't pair with. Two cases:
        #
        # - Most often, an orig bounds-assume that survived a rule-6
        #   rehavoc window: rule 6 already consumed the rhs's matching
        #   assume inside the window (with ``X → shadow`` substitution),
        #   so the lhs's post-window copy on the still-live X has no
        #   rhs counterpart.
        # - Hypothetically, a rule that drops an orig assume because
        #   it's redundant given other constraints. No current rule
        #   does this, but the gate must allow for it.
        #
        # The rwriter is allowed to drop an orig assume only if the
        # assume was *useless* — implied by the rest of the merged
        # state. Emit a CHK that asserts ``L.cond`` holds at this
        # point. No ``assume L.cond`` afterward: a successful assert
        # is automatically an assume for downstream reasoning (the
        # ``ua --strategy split`` step converts every non-selected
        # assert to an assume in each per-split file, so other split
        # queries see ``CHK = L.cond; assume CHK`` and treat L.cond as
        # a known fact). Adding a literal ``assume L.cond`` would just
        # restate the same constraint.
        #
        # Symmetric to rule 4 in shape: both unpaired assumes turn
        # into ``CHK = cond; assert CHK``.
        if isinstance(L, AssumeExpCmd):
            output.extend(
                _emit_eq_assert_for_assume(
                    state,
                    L.condition,
                    block_id=orig_block.id,
                    cmd_index=li,
                    kind="lhs-only-assume",
                )
            )
            li += 1
            state.hit("4b_lhs_assume")
            continue

        # Rule 10: nothing matches.
        raise EquivContractError(
            _format_no_rule_match_error(
                orig_block_id=orig_block.id,
                lhs_cmds=lhs_cmds,
                rhs_cmds=rhs_cmds,
                li=li,
                ri=ri,
                state=state,
            )
        )

    return output


def _emit_eq_assert_for_assume(
    state: _WalkerState,
    cond: TacExpr,
    *,
    block_id: str,
    cmd_index: int,
    kind: str = "rhs-only-assume",
) -> list[TacCmd]:
    """Rule 4 / 4b: turn an unpaired ``assume A`` into a CHK that
    asserts ``A`` holds at this point in the merged program.

    Rule 4 (rhs-only assume): catches a rwriter that ADDED a new
    constraint not in orig — checks the addition is implied (else
    the rwriter is restricting beyond orig and could mask bugs).
    Rule 4b (lhs-only assume): catches a rwriter that DROPPED an
    orig constraint — checks the dropped constraint is still
    implied (else the rwriter dropped something load-bearing).
    """
    chk = state.fresh_chk()
    state.asserts_emitted += 1
    return [
        canonicalize_cmd(AssignExpCmd(raw="", lhs=chk, rhs=cond)),
        canonicalize_cmd(
            AssertCmd(
                raw="",
                predicate=SymbolRef(chk),
                message=f"rw-eq:{block_id}:{cmd_index} {kind}",
            )
        ),
    ]


def _flatten_land(e: TacExpr) -> list[TacExpr]:
    if isinstance(e, ApplyExpr) and e.op == "LAnd":
        out: list[TacExpr] = []
        for a in e.args:
            out.extend(_flatten_land(a))
        return out
    return [e]


def _cond_matches(target: TacExpr, cand: TacExpr) -> bool:
    """``cand`` counts as ``target`` for alignment: exact equality, or
    ``cand``'s conjuncts are a (modulo-meta) subset of ``target``'s.
    The subset case covers the rewriter folding a range-decided
    conjunct out of an assume (``LAnd(Ge, Le)`` surviving as ``Ge``):
    the residue is still the same assume for stream-alignment
    purposes, and whatever CHK the realignment emits carries the
    actual proof obligation."""
    if cand == target:
        return True
    t = _flatten_land(target)
    if len(t) <= 1:
        return False
    c = _flatten_land(cand)
    return all(any(eq_modulo_meta(ci, ti) for ti in t) for ci in c)


def _assume_ahead(
    cmds: list[TacCmd], i: int, condition: TacExpr, k: int = 8
) -> bool:
    """True iff an ``AssumeExpCmd`` matching ``condition`` (exactly or
    as a conjunct-subset residue, see :func:`_cond_matches`) appears
    within the next ``k`` assumes of ``cmds[i:]``, scanning only the
    current assume run (noise skipped; any other command kind closes
    the scan). The 5a alignment lookahead."""
    seen = 0
    j = i
    while j < len(cmds) and seen < k:
        c = cmds[j]
        if isinstance(c, _NOISE_TYPES):
            j += 1
            continue
        if isinstance(c, AssumeExpCmd):
            if _cond_matches(condition, c.condition):
                return True
            seen += 1
            j += 1
            continue
        break
    return False


def _resolution_partner_ahead(
    cmds: list[TacCmd],
    i: int,
    payload: TacExpr,
    skip: set[int],
    k: int = 8,
) -> tuple[int, AssumeExpCmd] | None:
    """The resolution partner for rule 5c: an ``AssumeExpCmd`` within
    the next ``k`` assumes whose condition is a 2-arg ``LOr`` with an
    arm equal to ``payload`` modulo meta suffixes. Scans the current
    assume run only (noise skipped; any other command closes it)."""
    seen = 0
    j = i
    while j < len(cmds) and seen < k:
        c = cmds[j]
        if isinstance(c, _NOISE_TYPES) or j in skip:
            j += 1
            continue
        if isinstance(c, AssumeExpCmd):
            cond = c.condition
            if (
                isinstance(cond, ApplyExpr)
                and cond.op == "LOr"
                and len(cond.args) == 2
                and any(eq_modulo_meta(arg, payload) for arg in cond.args)
            ):
                return j, c
            seen += 1
            j += 1
            continue
        break
    return None


def _scan_dehavoc_def(
    rhs_cmds: list[TacCmd],
    ri: int,
    x: str,
    lhs_defined: frozenset[str],
) -> int | None:
    """Index of the rhs ``X = e`` def reachable from ``ri`` through a
    benign window (noise, assumes, rhs-fresh assignments), or ``None``.

    A non-benign command (paired def, havoc, assert, terminator)
    closes the scan without a match — the dehavoc rule then declines
    and dispatch falls through to the ordinary rules.
    """
    j = ri
    while j < len(rhs_cmds):
        cmd = rhs_cmds[j]
        if isinstance(cmd, _NOISE_TYPES):
            j += 1
            continue
        if isinstance(cmd, AssignExpCmd) and cmd.lhs == x:
            return j
        if isinstance(cmd, AssumeExpCmd):
            j += 1
            continue
        if isinstance(cmd, AssignExpCmd):
            # Fresh temps AND kept intermediates (e.g. unpurify's
            # retained A-binding chain, present on both sides) are
            # benign — the consumer pairs the shared ones in-window.
            j += 1
            continue
        return None
    return None


def _consume_dehavoc_window(
    *,
    output: list[TacCmd],
    lhs_havoc: AssignHavocCmd,
    lhs_block_id: str,
    lhs_cmds: list[TacCmd],
    li_after_havoc: int,
    rhs_cmds: list[TacCmd],
    ri: int,
    def_idx: int,
    state: _WalkerState,
) -> tuple[int, int]:
    """Rule 6b — the mirror of rule 6: lhs ``havoc X`` (plus a
    constraint window), rhs ``X = e`` (unpurify_div's recovery of a
    frontend-purified division). Returns the new ``(li, ri)``.

    Emission order is what makes the CHK provable:

    1. lhs's ``havoc X`` — X keeps the orig's def.
    2. lhs constraint window verbatim: the dropped temp assignments
       and the assumes that pin X (the Euclidean bounds).
    3. rhs window: rw-only assumes become rule-4-style CHKs (e.g.
       unpurify's ``assume Gt(B, 0)`` — provable *now*, after the lhs
       bounds are in scope); rhs-fresh assignments pass through.
    4. ``shadow = e`` under a fresh ``X__rw_eq<n>``, then
       ``CHK = Eq(X, shadow)`` — the uniqueness obligation: under the
       lhs constraints, X is pinned to exactly the recovered value.
       Discharging it also certifies the rw value lies in the orig's
       admitted set, so both inclusion directions ride one CHK.

    Same caveat as rule 6: if the lhs constraints are jointly
    infeasible the CHK holds vacuously while the rw path stays alive;
    ``check_feasibility`` inserts the probe that detects it.
    """
    output.append(lhs_havoc)
    x = lhs_havoc.lhs

    # (2)+(3) interleaved sub-walk up to the rhs def. lhs constraint
    # cmds (assumes pinning X, dropped temps) emit verbatim; shared
    # intermediates (e.g. unpurify's kept A-binding chain) pair
    # rule-1/2 style; rhs-only assumes are QUEUED — their rule-4 CHKs
    # are only provable once the lhs constraints are in scope.
    li = li_after_havoc
    queued_rhs_assumes: list[tuple[TacExpr, int]] = []
    while ri < def_idx:
        R = rhs_cmds[ri]
        if isinstance(R, _NOISE_TYPES):
            ri += 1
            continue
        L: TacCmd | None = None
        while li < len(lhs_cmds):
            cand = lhs_cmds[li]
            if isinstance(cand, _NOISE_TYPES):
                output.append(cand)
                li += 1
                continue
            L = cand
            break
        if (
            L is not None
            and isinstance(L, AssignExpCmd)
            and isinstance(R, AssignExpCmd)
            and L.lhs == R.lhs
        ):
            if not _cmd_equiv(L, R):
                output.extend(
                    _emit_eq_assert(
                        state,
                        L.rhs,
                        R.rhs,
                        block_id=lhs_block_id,
                        cmd_index=li,
                        kind="assignment",
                    )
                )
            output.append(L)
            li += 1
            ri += 1
            continue
        if isinstance(R, AssumeExpCmd):
            queued_rhs_assumes.append((R.condition, ri))
            ri += 1
            continue
        if isinstance(R, AssignExpCmd) and R.lhs not in state.lhs_defined:
            output.append(R)
            ri += 1
            continue
        # R is a shared assignment whose lhs twin isn't current —
        # consume lhs constraint cmds until the twin surfaces.
        if L is not None and isinstance(L, AssumeExpCmd):
            output.append(L)
            li += 1
            continue
        if (
            L is not None
            and isinstance(L, AssignExpCmd)
            and L.lhs not in state.rhs_defined
        ):
            output.append(L)
            li += 1
            continue
        raise EquivContractError(
            f"block {lhs_block_id}: dehavoc window for {x} cannot "
            f"align lhs/rhs (lhs: {_safe_unparse(L) if L else '<eos>'}, "
            f"rhs: {_safe_unparse(R)})"
        )

    # lhs constraint tail: the Euclidean assumes (and their dropped
    # temps) extend past the slot where the rhs def landed; consume
    # them into the window so they stay assumes (constraints on X) —
    # outside the window rule 4b would wrongly demand they be implied.
    while li < len(lhs_cmds):
        cmd = lhs_cmds[li]
        if isinstance(cmd, _NOISE_TYPES):
            output.append(cmd)
            li += 1
            continue
        if isinstance(cmd, AssumeExpCmd):
            output.append(cmd)
            li += 1
            continue
        if isinstance(cmd, AssignExpCmd) and cmd.lhs not in state.rhs_defined:
            output.append(cmd)
            li += 1
            continue
        break

    # Queued rhs assumes: provable now that the lhs constraints are
    # in scope (e.g. unpurify's ``assume Gt(B, 0)`` follows from the
    # Euclidean bounds).
    for cond, at in queued_rhs_assumes:
        output.extend(
            _emit_eq_assert_for_assume(
                state,
                cond,
                block_id=lhs_block_id,
                cmd_index=at,
                kind="dehavoc-assume",
            )
        )

    # (4) shadow def + uniqueness CHK.
    rhs_def = rhs_cmds[def_idx]
    assert isinstance(rhs_def, AssignExpCmd)
    sort = _guess_sort(x)
    shadow = state.fresh_shadow(x, sort)
    state.record_rehavoc(
        RehavocSite(
            block_id=lhs_block_id,
            cmd_index=def_idx,
            var_name=x,
            shadow_name=shadow,
        )
    )
    output.append(
        canonicalize_cmd(AssignExpCmd(raw="", lhs=shadow, rhs=rhs_def.rhs))
    )
    if state.check_feasibility:
        output.extend(
            _emit_feasibility_assert(
                state,
                block_id=lhs_block_id,
                cmd_index=def_idx,
                kind="dehavoc",
            )
        )
    output.extend(
        _emit_eq_assert(
            state,
            SymbolRef(x),
            SymbolRef(shadow),
            block_id=lhs_block_id,
            cmd_index=def_idx,
            kind="dehavoc",
        )
    )
    return li, def_idx + 1


def _consume_rehavoc_window(
    *,
    output: list[TacCmd],
    lhs: AssignExpCmd,
    lhs_block_id: str,
    lhs_cmd_index: int,
    rhs_cmds: list[TacCmd],
    ri_after_havoc: int,
    state: _WalkerState,
) -> int:
    """Process the rhs's rehavoc window starting just past the
    ``havoc X``. Returns the new ``ri`` after the window closes.

    See the module docstring's "Rule 6" section for the contract.
    The window admits consecutive AssumeExpCmds (with ``X → X_new``
    substitution in each condition) and closes on the next non-assume
    command (or exhaustion). Anything that doesn't fit aborts via
    :class:`EquivContractError`.
    """
    sort = _guess_sort(lhs.lhs)
    shadow = state.fresh_shadow(lhs.lhs, sort)
    state.record_rehavoc(
        RehavocSite(
            block_id=lhs_block_id,
            cmd_index=lhs_cmd_index,
            var_name=lhs.lhs,
            shadow_name=shadow,
        )
    )
    # Havoc the shadow before any of its uses: the substituted assumes
    # below reference shadow, and the closing CHK does too. Without an
    # explicit AssignHavocCmd, shadow has no def site — the symbol
    # table declares it but no command assigns it. sea_vc happens to
    # encode it as a free SMT const (so the ASSUMES still constrain
    # it functionally), but the merged TAC is structurally invalid:
    # `ctac df --show use-before-def` flags every reference, and a
    # future encoder that requires a def for every use would reject
    # the program. Emit `havoc shadow` so the merged TAC is well-
    # formed independent of any encoder's tolerance.
    output.append(
        canonicalize_cmd(AssignHavocCmd(raw="", lhs=shadow))
    )
    mapping = {lhs.lhs: shadow}

    ri = ri_after_havoc
    while ri < len(rhs_cmds):
        cmd = rhs_cmds[ri]
        if isinstance(cmd, _NOISE_TYPES):
            ri += 1
            continue
        if isinstance(cmd, AssumeExpCmd):
            new_cond = subst_symbol(cmd.condition, mapping)
            output.append(
                canonicalize_cmd(AssumeExpCmd(raw="", condition=new_cond))
            )
            ri += 1
            continue
        if (
            isinstance(cmd, AssignHavocCmd)
            and cmd.lhs == lhs.lhs
        ):
            raise EquivContractError(
                f"block {lhs_block_id}: rehavoc window for {lhs.lhs} "
                f"contains a second havoc of {lhs.lhs}; aborting "
                f"(unexpected rewriter shape)"
            )
        # Non-assume RHS command — close window successfully.
        break

    if state.check_feasibility:
        output.extend(
            _emit_feasibility_assert(
                state,
                block_id=lhs_block_id,
                cmd_index=lhs_cmd_index,
                kind="rehavoc",
            )
        )
    output.extend(
        _emit_eq_assert(
            state,
            lhs.rhs,
            SymbolRef(shadow),
            block_id=lhs_block_id,
            cmd_index=lhs_cmd_index,
            kind="rehavoc",
        )
    )
    output.append(lhs)  # lhs's `X = e` finally takes effect
    return ri


def _guess_sort(_var_name: str) -> str:
    """Best-effort sort guess for a shadow variable. The walker doesn't
    have access to the symbol table, so we default to ``int`` (matches
    the int-arithmetic shape of R4A's bounds). Refine when the walker
    is plumbed through symbol_sorts."""
    return "int"


# Re-export for callers that prefer not to reach into model directly.
__all__ = ["emit_equivalence_program"]


# Suppress unused-import lint for replace (kept as a future hook).
_ = replace
