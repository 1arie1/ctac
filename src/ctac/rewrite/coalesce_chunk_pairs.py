"""Coalesce (lo, hi) chunk pairs of u128 values flowing through
parallel selects into a fresh wide ``H<N>`` register.

The SBF lowering manipulates u128 values as two u64 chunks moving in
lockstep through FLOW constructs — parallel ``Ite`` selects on the
same condition, const pairs, (value, 0) widenings — with no
arithmetic anchor for :mod:`ctac.rewrite.rewrite_u128_carry_add` to
fire on::

    R_lo  = Mod(V, 2^64)              ; extraction pair of V
    R_hi  = Div(V, 2^64)
    a     = Ite(B, R_lo, x_lo)        ; parallel select
    b     = Ite(B, R_hi, x_hi)
    ...   = LAnd(Eq(b, 0), Lt(a, c))  ; chunked compare on the pair

This pass discovers such pairs and re-anchors them as chunks of a
fresh value-level select::

    H<N>  = Ite(B, V, X)              ; X = x's value (see feeds)
    a     = Mod(H<N>, 2^64)
    b     = Div(H<N>, 2^64)

then STOPS — the existing rule library does the rest
(``CHUNKED_U128_LT`` gets its direct-extract shape back,
``CHUNK_MERGE`` collapses inline recombinations to ``H<N>``, the
gadget / band consumers fire on the chunks). Same philosophy as the
carry-add lift: produce the lift / op / split shape the concept
recognizers consume; don't re-implement the consumers.

Feed resolution — an Ite arm pair ``(arm_lo, arm_hi)`` names a value
when:

* **extraction**: both are the ``Mod`` / ``Div``-by-``2^64`` chunks
  of the same ``V`` (no range gate — the pair's value is ``V`` by
  Euclidean decomposition for ANY ``V >= 0``);
* **chunks of a previous coalesce**: same shape, via the fixpoint
  rounds (cascaded selects lift one layer per round);
* **const pair**: ``(c_lo, c_hi)`` with ``c_lo < 2^64`` — value
  ``c_hi * 2^64 + c_lo``;
* **widen**: ``(e, 0)`` with ``e`` provably u64 — value ``e``;
* **synthesized recombination**: both arms provably u64 — mint
  ``HF = narrow(IntAdd(IntMul(arm_hi, 2^64), arm_lo))`` (the narrow
  is safe: the int value is < 2^128). Bounds are derived via
  ``infer_expr_range``, never invented.

Select pairs may be static or DSA-dynamic (the per-branch phi-feed
form, pre ``lift_dynamic_ite``). Rewriting a dynamic def's RHS keeps
it dynamic; the fresh ``H<N>`` def is inserted into the block's
static prefix (before the first dynamic command) so the
``(static)*(dynamic)*terminator`` shape invariant holds — the same
discipline as :mod:`ctac.rewrite.lift_dynamic_ite`.

rw-eq verification (per the per-cmd walker):

* RHS ``H<N>`` / ``HF`` (fresh names) — rule 3 rhs-only-fresh, no
  CHK.
* LHS / RHS ``a`` paired — rule 2 ``CHK = Eq(Ite(B, lo1, lo2),
  Mod(Ite(B, V1, V2), 2^64))``. Discharges from the feed chunk
  facts in scope (the extraction defs, const arithmetic, the u64
  range assumes) — linear + mod, no recursion.
* LHS / RHS ``b`` paired — same with ``Div``.

Original feed defs are left in place — deleting defs is DCE's job,
not a recognizer's.

Idempotent: re-anchored pairs have ``Mod`` / ``Div`` RHSs, which the
select matcher does not target.
"""

from __future__ import annotations

from dataclasses import dataclass, replace

from ctac.analysis.symbols import canonical_symbol
from ctac.ast.nodes import (
    ApplyExpr,
    AssignExpCmd,
    ConstExpr,
    SymbolRef,
    TacCmd,
    TacExpr,
)
from ctac.ir.models import TacBlock, TacProgram
from ctac.rewrite.context import RewriteCtx
from ctac.rewrite.range_infer import infer_expr_range
from ctac.rewrite.rules.common import (
    DIV_OPS,
    MOD_OPS,
    const_to_int,
    eq_modulo_meta,
)
from ctac.rewrite.unparse import canonicalize_cmd

_U64_MAX = (1 << 64) - 1
_TWO_TO_64 = 1 << 64
_TWO_TO_64_BV = ConstExpr(f"{hex(_TWO_TO_64)}")
_TWO_TO_64_INT = ConstExpr(f"{hex(_TWO_TO_64)}(int)")
_NARROW_FN = SymbolRef("safe_math_narrow_bv256:bif")


@dataclass(frozen=True)
class CoalesceChunkPairsResult:
    program: TacProgram
    hits: int
    fresh_symbols: tuple[tuple[str, str], ...]


def _u64_bounded(expr: TacExpr, ctx: RewriteCtx) -> bool:
    rng = infer_expr_range(expr, ctx)
    if rng is None:
        return False
    lo, hi = rng
    return lo is not None and hi is not None and lo >= 0 and hi <= _U64_MAX


def _chunk_of(
    e: TacExpr, ctx: RewriteCtx
) -> tuple[str, SymbolRef, str] | None:
    """If ``e`` is a symbol whose (single) def is ``Mod(V, 2^64)`` /
    ``Div(V, 2^64)`` with ``V`` a symbol, return
    ``(kind, V, canon(e))`` with kind ``'lo'`` / ``'hi'``."""
    if not isinstance(e, SymbolRef):
        return None
    d = ctx.definition(e.name)
    if not (isinstance(d, ApplyExpr) and len(d.args) == 2):
        return None
    v, m = d.args
    if not isinstance(v, SymbolRef) or const_to_int(m) != _TWO_TO_64:
        return None
    if d.op in MOD_OPS:
        return "lo", v, canonical_symbol(e.name)
    if d.op in DIV_OPS:
        return "hi", v, canonical_symbol(e.name)
    return None


@dataclass(frozen=True)
class _Feed:
    """One resolved Ite-arm pair: the value expression, plus an
    optional synthesized-recombination def to insert first."""

    value: TacExpr
    synth: AssignExpCmd | None = None


def _resolve_feed(
    arm_lo: TacExpr,
    arm_hi: TacExpr,
    ctx: RewriteCtx,
    fresh: "_FreshNames",
    *,
    allow_synth: bool,
) -> _Feed | None:
    lo_chunk = _chunk_of(arm_lo, ctx)
    hi_chunk = _chunk_of(arm_hi, ctx)
    if (
        lo_chunk is not None
        and hi_chunk is not None
        and lo_chunk[0] == "lo"
        and hi_chunk[0] == "hi"
        and canonical_symbol(lo_chunk[1].name)
        == canonical_symbol(hi_chunk[1].name)
    ):
        return _Feed(value=lo_chunk[1])
    c_lo = const_to_int(arm_lo)
    c_hi = const_to_int(arm_hi)
    if c_lo is not None and c_hi is not None:
        if c_lo >= _TWO_TO_64:
            return None
        return _Feed(value=ConstExpr(hex(c_hi * _TWO_TO_64 + c_lo)))
    if c_hi == 0 and _u64_bounded(arm_lo, ctx):
        return _Feed(value=arm_lo)
    if not allow_synth:
        return None
    # Synthesized recombination — last resort only (a synth can
    # satisfy the WRONG slot orientation by building a limb-swapped
    # composite: sound, but useless to the recognizers and it poisons
    # the cascade; the caller tries both orientations without synth
    # first). Defer when an arm is itself Ite-defined: it is a
    # candidate pair, and the next fixpoint round sees it as chunks
    # of its own H.
    for arm in (arm_lo, arm_hi):
        if isinstance(arm, SymbolRef) and _is_ite(
            ctx.definition(arm.name) or ConstExpr("0x0")
        ):
            return None
    if _u64_bounded(arm_lo, ctx) and _u64_bounded(arm_hi, ctx):
        name = fresh.pick()
        rhs = ApplyExpr(
            "Apply",
            (
                _NARROW_FN,
                ApplyExpr(
                    "IntAdd",
                    (
                        ApplyExpr("IntMul", (arm_hi, _TWO_TO_64_INT)),
                        arm_lo,
                    ),
                ),
            ),
        )
        return _Feed(
            value=SymbolRef(name),
            synth=canonicalize_cmd(AssignExpCmd(raw="", lhs=name, rhs=rhs)),
        )
    return None


class _FreshNames:
    def __init__(self, program: TacProgram) -> None:
        self.taken: set[str] = set()
        for block in program.blocks:
            for cmd in block.commands:
                lhs = getattr(cmd, "lhs", None)
                if isinstance(lhs, str):
                    self.taken.add(canonical_symbol(lhs))
        self.minted: list[str] = []

    def pick(self) -> str:
        n = 0
        while True:
            name = f"H{n}"
            if name not in self.taken:
                self.taken.add(name)
                self.minted.append(name)
                return name
            n += 1


@dataclass(frozen=True)
class _Site:
    lo_idx: int
    hi_idx: int
    cond: TacExpr
    then_feed: _Feed
    else_feed: _Feed


def _is_ite(rhs: TacExpr) -> bool:
    return isinstance(rhs, ApplyExpr) and rhs.op == "Ite" and len(rhs.args) == 3


def _find_sites(
    block: TacBlock, ctx: RewriteCtx, fresh: _FreshNames
) -> list[_Site]:
    ites: list[tuple[int, AssignExpCmd]] = [
        (i, c)
        for i, c in enumerate(block.commands)
        if isinstance(c, AssignExpCmd) and _is_ite(c.rhs)
    ]
    sites: list[_Site] = []
    claimed: set[int] = set()
    for ai in range(len(ites)):
        i, a = ites[ai]
        if i in claimed:
            continue
        assert isinstance(a.rhs, ApplyExpr)
        for bi in range(ai + 1, len(ites)):
            j, b = ites[bi]
            if j in claimed:
                continue
            assert isinstance(b.rhs, ApplyExpr)
            if not eq_modulo_meta(a.rhs.args[0], b.rhs.args[0]):
                continue
            # A synthesized recomb can resolve EITHER orientation (it
            # would happily build a limb-swapped composite), so it
            # must never decide which slot is the lo: at least one
            # feed must resolve without synth (the anchor), and the
            # other may then fall back to synth. Both-synth pairs are
            # rejected outright.
            for lo_idx, hi_idx, lo_rhs, hi_rhs in (
                (i, j, a.rhs, b.rhs),
                (j, i, b.rhs, a.rhs),
            ):
                then_feed = _resolve_feed(
                    lo_rhs.args[1],
                    hi_rhs.args[1],
                    ctx,
                    fresh,
                    allow_synth=False,
                )
                else_feed = _resolve_feed(
                    lo_rhs.args[2],
                    hi_rhs.args[2],
                    ctx,
                    fresh,
                    allow_synth=False,
                )
                if then_feed is None and else_feed is None:
                    continue
                if then_feed is None:
                    then_feed = _resolve_feed(
                        lo_rhs.args[1],
                        hi_rhs.args[1],
                        ctx,
                        fresh,
                        allow_synth=True,
                    )
                if else_feed is None:
                    else_feed = _resolve_feed(
                        lo_rhs.args[2],
                        hi_rhs.args[2],
                        ctx,
                        fresh,
                        allow_synth=True,
                    )
                if then_feed is None or else_feed is None:
                    continue
                sites.append(
                    _Site(
                        lo_idx=lo_idx,
                        hi_idx=hi_idx,
                        cond=a.rhs.args[0],
                        then_feed=then_feed,
                        else_feed=else_feed,
                    )
                )
                claimed.add(i)
                claimed.add(j)
                break
            if i in claimed:
                break
    return sites


def _first_dynamic_index(block: TacBlock, dynamic_lhs: set[str]) -> int:
    for idx, cmd in enumerate(block.commands):
        lhs = getattr(cmd, "lhs", None)
        if isinstance(lhs, str) and canonical_symbol(lhs) in dynamic_lhs:
            return idx
    return len(block.commands)


def _dynamic_lhs_names(program: TacProgram) -> set[str]:
    """Canonical lhs names with more than one def (DSA-dynamic);
    havoc defs count too."""
    counts: dict[str, int] = {}
    for block in program.blocks:
        for cmd in block.commands:
            lhs = getattr(cmd, "lhs", None)
            if isinstance(lhs, str):
                c = canonical_symbol(lhs)
                counts[c] = counts.get(c, 0) + 1
    return {name for name, n in counts.items() if n > 1}


def coalesce_chunk_pairs(
    program: TacProgram,
    *,
    symbol_sorts: dict[str, str] | None = None,
) -> CoalesceChunkPairsResult:
    """Run pair discovery + re-anchor rounds to fixpoint."""
    sorts = symbol_sorts or {}
    total_hits = 0
    fresh_symbols: list[tuple[str, str]] = []
    while True:
        ctx = RewriteCtx(program, symbol_sorts=sorts)
        fresh = _FreshNames(program)
        dynamic_lhs = _dynamic_lhs_names(program)
        round_hits = 0
        new_blocks: list[TacBlock] = []
        for block in program.blocks:
            sites = _find_sites(block, ctx, fresh)
            if not sites:
                new_blocks.append(block)
                continue
            first_dyn = _first_dynamic_index(block, dynamic_lhs)
            commands: list[TacCmd] = list(block.commands)
            # Static-prefix inserts, applied bottom-up so indices hold.
            inserts: list[tuple[int, list[TacCmd]]] = []
            for site in sites:
                h_name = fresh.pick()
                h_rhs = ApplyExpr(
                    "Ite",
                    (site.cond, site.then_feed.value, site.else_feed.value),
                )
                new_defs: list[TacCmd] = []
                for feed in (site.then_feed, site.else_feed):
                    if feed.synth is not None:
                        new_defs.append(feed.synth)
                new_defs.append(
                    canonicalize_cmd(
                        AssignExpCmd(raw="", lhs=h_name, rhs=h_rhs)
                    )
                )
                # Insert before the pair's first def, but never inside
                # the dynamic suffix: a static H def between dynamics
                # would break the (static)*(dynamic)* block shape.
                at = min(site.lo_idx, site.hi_idx, first_dyn)
                inserts.append((at, new_defs))
                lo_cmd = commands[site.lo_idx]
                hi_cmd = commands[site.hi_idx]
                assert isinstance(lo_cmd, AssignExpCmd)
                assert isinstance(hi_cmd, AssignExpCmd)
                commands[site.lo_idx] = canonicalize_cmd(
                    replace(
                        lo_cmd,
                        raw="",
                        rhs=ApplyExpr(
                            "Mod", (SymbolRef(h_name), _TWO_TO_64_BV)
                        ),
                    )
                )
                commands[site.hi_idx] = canonicalize_cmd(
                    replace(
                        hi_cmd,
                        raw="",
                        rhs=ApplyExpr(
                            "Div", (SymbolRef(h_name), _TWO_TO_64_BV)
                        ),
                    )
                )
                round_hits += 1
            for at, defs in sorted(inserts, key=lambda t: t[0], reverse=True):
                commands[at:at] = defs
            new_blocks.append(replace(block, commands=commands))
        if not round_hits:
            break
        program = TacProgram(blocks=new_blocks)
        for name in fresh.minted:
            fresh_symbols.append((name, "bv256"))
            sorts = {**sorts, name: "bv256"}
        total_hits += round_hits
    return CoalesceChunkPairsResult(
        program=program,
        hits=total_hits,
        fresh_symbols=tuple(fresh_symbols),
    )
