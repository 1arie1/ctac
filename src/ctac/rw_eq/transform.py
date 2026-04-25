"""Lockstep walker that merges (orig, rw) into one equivalence-check
TAC program.

See ``Plan: ctac rw-eq`` for the full rules table; the implementation
below maps each rule to a branch in :func:`_walk_block`. Rule numbers
in comments correspond to the table.
"""

from __future__ import annotations

from collections import Counter
from dataclasses import replace

from ctac.ast.nodes import (
    AnnotationCmd,
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
from ctac.analysis.passes import analyze_dsa
from ctac.ast.subst import subst_symbol
from ctac.ir.models import TacBlock, TacProgram
from ctac.rewrite.unparse import canonicalize_cmd, unparse_cmd
from ctac.rw_eq.model import EquivContractError, EquivResult, RehavocSite

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
    """
    _check_block_set(orig, rw)
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

    new_blocks: list[TacBlock] = []
    by_id_rw = rw.block_by_id()
    for orig_b in orig.blocks:
        rw_b = by_id_rw[orig_b.id]
        if list(orig_b.successors) != list(rw_b.successors):
            raise EquivContractError(
                f"block {orig_b.id}: successor lists differ "
                f"(orig={orig_b.successors!r}, rw={rw_b.successors!r})"
            )
        new_cmds = _walk_block(orig_b, rw_b, state)
        new_cmds = _hoist_statics_above_dynamics(new_cmds, dynamic_symbols)
        new_blocks.append(
            TacBlock(id=orig_b.id, successors=list(orig_b.successors), commands=new_cmds)
        )

    return EquivResult(
        program=TacProgram(blocks=new_blocks),
        rule_hits=dict(state.rule_hits),
        rehavoc_sites=tuple(state.rehavoc_sites),
        extra_symbols=tuple(state.extra_symbols),
        asserts_emitted=state.asserts_emitted,
        feasibility_asserts_emitted=state.feasibility_asserts_emitted,
    )


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

    def peek(cmds: list[TacCmd], i: int) -> tuple[TacCmd | None, int]:
        while i < len(cmds) and isinstance(cmds[i], _NOISE_TYPES):
            i += 1
        if i >= len(cmds):
            return None, i
        return cmds[i], i

    while True:
        L, li_new = peek(lhs_cmds, li)
        R, ri_new = peek(rhs_cmds, ri)
        # Echo skipped lhs noise into output (preserves comments and
        # snippet annotations from the orig program for inspection).
        for k in range(li, li_new):
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

        # Rule 5a: both AssumeExpCmd.
        if isinstance(L, AssumeExpCmd) and isinstance(R, AssumeExpCmd):
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

        # Rule 9b: lhs has an assignment whose LHS isn't defined in rhs
        # at all — DCE removed it. Emit verbatim, advance LHS only. (The
        # bare rule 9 only handles end-of-stream DCE; this handles the
        # mid-stream case.)
        #
        # IMPORTANT: 9b runs *before* rules 4 (rhs-only assume) and 3
        # (rhs fresh assignment). When the lhs has a soon-to-be-DCE'd
        # assignment, eating it first lets the next-up lhs assume /
        # assert / assignment pair with the rhs's matching command via
        # rule 5a / 5b / 1 / 2. If we let rule 4 fire first, the rhs's
        # "replacement" assume gets emitted as a rhs-only check and the
        # subsequent lhs assume has nothing on the rhs to pair with —
        # the walker stalls on a structurally-fine input.
        if (
            isinstance(L, (AssignExpCmd, AssignHavocCmd))
            and L.lhs not in state.rhs_defined
        ):
            output.append(L)
            li += 1
            state.hit("9b_lhs_dce")
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
        # state. Emit a CHK that asserts ``L.cond`` is implied at this
        # point (catches a future rule that drops a load-bearing
        # assume), and ALSO emit ``assume L.cond`` so downstream
        # equivalence checks (rule 2 / 5a / 5b) stay scoped to orig's
        # reachable domain. Without the assume, a downstream rule-2
        # check could fail on states where ``L.cond`` doesn't hold —
        # states that orig wouldn't reach but the merged program would
        # without the scoping — producing a false positive about a
        # rwriter that's actually sound on orig's domain.
        #
        # Symmetric to rule 4 in the assert-the-orphan-condition sense
        # (both emit CHK + assert), and to rule 5a in the
        # preserve-path-scope sense (both ``assume L.cond`` afterward).
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
            output.append(L)
            li += 1
            state.hit("4b_lhs_assume")
            continue

        # Rule 3: rhs-introduced fresh symbol.
        if (
            isinstance(R, (AssignExpCmd, AssignHavocCmd))
            and R.lhs not in state.lhs_defined
        ):
            output.append(R)
            ri += 1
            state.hit("3_fresh_rhs")
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

    See the plan's "Rule 6 — rehavoc window" for the contract; in v1
    the window admits consecutive AssumeExpCmds (with X→X_new
    substitution) and closes on the next non-assume command (or
    exhaustion). Anything that doesn't fit aborts via
    EquivContractError.
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
