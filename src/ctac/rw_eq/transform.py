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
from ctac.ast.subst import subst_symbol
from ctac.ir.models import TacBlock, TacProgram
from ctac.rewrite.unparse import canonicalize_cmd
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

        # Terminator handling: both should be terminators at this point
        # if one is. Rule 7 (matching) or rule 10 (mismatch).
        l_term = isinstance(L, _TERMINATOR_TYPES)
        r_term = isinstance(R, _TERMINATOR_TYPES)
        if l_term or r_term:
            if not (l_term and r_term):
                raise EquivContractError(
                    f"block {orig_block.id}: terminator on one side but not the other "
                    f"(lhs={type(L).__name__}, rhs={type(R).__name__})"
                )
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
        if _cmd_equiv(L, R):
            output.append(L)
            li += 1
            ri += 1
            state.hit("1_identical")
            continue

        # Rule 2: same LHS assignment, different RHS.
        if (
            isinstance(L, AssignExpCmd)
            and isinstance(R, AssignExpCmd)
            and L.lhs == R.lhs
        ):
            output.append(L)
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

        # Rule 3: rhs-introduced fresh symbol.
        if (
            isinstance(R, (AssignExpCmd, AssignHavocCmd))
            and R.lhs not in state.lhs_defined
        ):
            output.append(R)
            ri += 1
            state.hit("3_fresh_rhs")
            continue

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

        # Rule 10: nothing matches.
        raise EquivContractError(
            f"block {orig_block.id}: lockstep step does not match any rule "
            f"(lhs={type(L).__name__}, rhs={type(R).__name__})"
        )

    return output


def _emit_eq_assert_for_assume(
    state: _WalkerState,
    cond: TacExpr,
    *,
    block_id: str,
    cmd_index: int,
) -> list[TacCmd]:
    """Rule 4: turn an RHS-only ``assume A`` into an ``assert A``
    in the merged program (same shape as the equivalence checks)."""
    chk = state.fresh_chk()
    state.asserts_emitted += 1
    return [
        canonicalize_cmd(AssignExpCmd(raw="", lhs=chk, rhs=cond)),
        canonicalize_cmd(
            AssertCmd(
                raw="",
                predicate=SymbolRef(chk),
                message=f"rw-eq:{block_id}:{cmd_index} rhs-only-assume",
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
