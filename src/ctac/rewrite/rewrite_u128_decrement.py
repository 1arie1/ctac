"""Rewrite the chunked u128 decrement borrow chain into ``H_new = Sub(H, 1)``.

Input shape (post-simplify, post-carry-add, post-materialize-h-nonzero):

    R_low  = Mod(H, 2^64)
    R_hi   = Div(H, 2^64)
    B_lo   = Eq(R_low, 0)
    B_hi   = Eq(R_hi, 0)
    assume LNot(LAnd(B_lo, B_hi))             ; H >= 1 (chunked form)
    assume Ge(H, 1)                            ; from materialize_h_nonzero
    R_hi_dec = Ite(B_lo, Sub(R_hi, 1), R_hi)   ; new high after decrement
    TB       = Ge(R_low, 1)                    ; equivalent to !B_lo
    R_lo_dec = Ite(TB, IntSub(R_low, 1), 2^64-1)   ; new low after decrement

Output:

    R_low  = Mod(H, 2^64)
    R_hi   = Div(H, 2^64)
    ...    (B_lo, B_hi, TB DCE'd when no other consumers)
    H_new  = Sub(H, 1)                         ; bv256 register, fresh
    R_hi_dec = Div(H_new, 2^64)
    R_lo_dec = Mod(H_new, 2^64)

The original ``LNot(LAnd(...))`` assume is dropped (it's redundant with
``Ge(H, 1)``, which is in scope per the upstream materialize pass).

Soundness (per-rewrite, verifiable by rw-eq's rule-2 CHK):

``R_lo_dec``: original ``Ite(R_low >= 1, R_low - 1, 2^64-1)`` equals
``(H - 1) mod 2^64``.
- ``R_low >= 1``: low arm = R_low - 1 = (H % 2^64) - 1. Since R_low >= 1,
  no underflow, and ``(H - 1) % 2^64 = R_low - 1``.
- ``R_low == 0``: else arm = 2^64-1. Since ``Ge(H, 1)`` and
  ``R_low = 0``, ``H`` is a positive multiple of 2^64;
  ``(H - 1) % 2^64 = 2^64 - 1``.

``R_hi_dec``: original ``Ite(R_low == 0, R_hi - 1, R_hi)`` equals
``(H - 1) / 2^64``.
- ``R_low == 0``: high arm = R_hi - 1 = (H / 2^64) - 1.
  ``(H - 1) / 2^64 = H/2^64 - 1`` when R_low = 0 (clean borrow).
- ``R_low >= 1``: else arm = R_hi.
  ``(H - 1) / 2^64 = H/2^64`` (no borrow).

Both CHKs case-split on ``R_low == 0`` vs ``>= 1``; the
``Ge(H, 1)`` precondition rules out the ``H == 0`` ill-defined case.

Soundness of ``H_new = Sub(H, 1)``: bv ``Sub`` wraps mod 2^256 when
``H = 0``; the ``Ge(H, 1)`` precondition rules out the wrap, so
``H_new = H - 1`` in the int domain.

Gates: the matcher fires only when
- ``H`` has ``infer_expr_range`` lower bound >= 1 (provided by
  materialize_h_nonzero), AND
- the entire 8-cmd chain is in the same block.

Idempotent: skips when the chain's expected shapes are already
the post-rewrite Div / Mod form.
"""

from __future__ import annotations

from dataclasses import dataclass, replace

from ctac.analysis.symbols import canonical_symbol
from ctac.ast.nodes import (
    ApplyExpr,
    AssignExpCmd,
    AssumeExpCmd,
    ConstExpr,
    SymbolRef,
    TacCmd,
    TacExpr,
)
from ctac.ir.models import TacBlock, TacProgram
from ctac.rewrite.context import RewriteCtx
from ctac.rewrite.range_infer import infer_expr_range
from ctac.rewrite.rules.common import const_to_int
from ctac.rewrite.unparse import canonicalize_cmd

_U64_MAX = (1 << 64) - 1
_TWO_TO_64 = 1 << 64
_TWO_TO_64_BV = ConstExpr(f"{hex(_TWO_TO_64)}")
_ONE_BV = ConstExpr("0x1")


@dataclass(frozen=True)
class RewriteU128DecrementResult:
    """Outcome of :func:`rewrite_u128_decrement`."""

    program: TacProgram
    hits: int
    fresh_symbols: tuple[tuple[str, str], ...]


def _match_lo_dec(rhs: TacExpr) -> tuple[TacExpr, SymbolRef] | None:
    """Match ``Ite(<cond>, IntSub(low, 1), 2^64-1)``; return
    ``(cond_expr, low)``. ``cond_expr`` can be a SymbolRef (post
    ITE_PURIFY) or an inline ApplyExpr (pre-ITE_PURIFY)."""
    if not (isinstance(rhs, ApplyExpr) and rhs.op == "Ite" and len(rhs.args) == 3):
        return None
    cond, then_arm, else_arm = rhs.args
    if not (
        isinstance(then_arm, ApplyExpr)
        and then_arm.op == "IntSub"
        and len(then_arm.args) == 2
    ):
        return None
    low_ref, one = then_arm.args
    if not isinstance(low_ref, SymbolRef) or const_to_int(one) != 1:
        return None
    if const_to_int(else_arm) != _U64_MAX:
        return None
    return cond, low_ref


def _match_hi_dec(rhs: TacExpr) -> tuple[TacExpr, SymbolRef] | None:
    """Match ``Ite(<cond>, Sub(hi, 1), hi)``; return ``(cond_expr, hi)``.

    ``cond_expr`` can be a SymbolRef or an inline ApplyExpr."""
    if not (isinstance(rhs, ApplyExpr) and rhs.op == "Ite" and len(rhs.args) == 3):
        return None
    cond, then_arm, else_arm = rhs.args
    if not isinstance(else_arm, SymbolRef):
        return None
    if not (
        isinstance(then_arm, ApplyExpr)
        and then_arm.op == "Sub"
        and len(then_arm.args) == 2
    ):
        return None
    hi_ref, one = then_arm.args
    if not isinstance(hi_ref, SymbolRef) or const_to_int(one) != 1:
        return None
    if canonical_symbol(hi_ref.name) != canonical_symbol(else_arm.name):
        return None
    return cond, hi_ref


def _resolve_cmp_cond(
    cond: TacExpr, ctx: RewriteCtx, op: str, want_const: int
) -> SymbolRef | None:
    """Resolve ``cond`` (SymRef-or-inline) to ``<op>(X, want_const)``
    and return X."""
    if isinstance(cond, SymbolRef):
        cmp_expr = ctx.definition(cond.name)
    else:
        cmp_expr = cond
    return _match_cmp_against_const(cmp_expr, op, want_const)


def _match_chunk_def(
    expr: TacExpr | None, want_op: str
) -> SymbolRef | None:
    """If ``expr`` is ``<want_op>(H, 2^64)`` with H a SymbolRef and
    ``want_op`` in ``{"Mod", "Div"}``, return H."""
    if expr is None:
        return None
    if not (
        isinstance(expr, ApplyExpr)
        and expr.op == want_op
        and len(expr.args) == 2
    ):
        return None
    a, b = expr.args
    if const_to_int(b) != _TWO_TO_64:
        return None
    return a if isinstance(a, SymbolRef) else None


def _match_cmp_against_const(
    expr: TacExpr | None, op: str, want_const: int
) -> SymbolRef | None:
    """If ``expr`` is ``<op>(X, K)`` (or symmetric for commutative
    op) with K matching ``want_const``, return X."""
    if expr is None:
        return None
    if not (
        isinstance(expr, ApplyExpr)
        and expr.op == op
        and len(expr.args) == 2
    ):
        return None
    a, b = expr.args
    if isinstance(a, SymbolRef) and const_to_int(b) == want_const:
        return a
    if op == "Eq" and isinstance(b, SymbolRef) and const_to_int(a) == want_const:
        return b
    return None


def _match_lnot_land(cond: TacExpr) -> tuple[SymbolRef, SymbolRef] | None:
    """Match ``LNot(LAnd(b_lo, b_hi))`` with SymbolRef arms."""
    if not (
        isinstance(cond, ApplyExpr) and cond.op == "LNot" and len(cond.args) == 1
    ):
        return None
    inner = cond.args[0]
    if not (
        isinstance(inner, ApplyExpr) and inner.op == "LAnd" and len(inner.args) == 2
    ):
        return None
    a, b = inner.args
    if not (isinstance(a, SymbolRef) and isinstance(b, SymbolRef)):
        return None
    return a, b


@dataclass(frozen=True)
class _DecSite:
    block_id: str
    h_name: str
    h_expr: TacExpr  # the SymbolRef to H in the source program
    lo_dec_idx: int
    hi_dec_idx: int
    lnot_assume_idx: int | None  # may be None if no matching assume found
    r_lo_dec_name: str
    r_hi_dec_name: str


def rewrite_u128_decrement(
    program: TacProgram,
    *,
    symbol_sorts: dict[str, str] | None = None,
) -> RewriteU128DecrementResult:
    """Walk every block; for each matched u128 decrement chunked
    chain, rewrite to bv ``Sub`` on a fresh ``H<N>`` register."""
    ctx = RewriteCtx(program, symbol_sorts=symbol_sorts or {})

    sites: dict[str, list[_DecSite]] = {}

    for block in program.blocks:
        # Index helpers: AssignExpCmds by lhs canonical name, with idx.
        lo_dec_anchors: list[tuple[int, AssignExpCmd]] = []
        hi_dec_anchors: list[tuple[int, AssignExpCmd]] = []
        for idx, cmd in enumerate(block.commands):
            if not isinstance(cmd, AssignExpCmd):
                continue
            if _match_lo_dec(cmd.rhs) is not None:
                lo_dec_anchors.append((idx, cmd))
            if _match_hi_dec(cmd.rhs) is not None:
                hi_dec_anchors.append((idx, cmd))

        for lo_idx, lo_cmd in lo_dec_anchors:
            lo_match = _match_lo_dec(lo_cmd.rhs)
            assert lo_match is not None
            tb_cond, low_ref = lo_match
            ctx.set_position(block.id, lo_idx)

            # Resolve the TB cond (inline or SymRef) to Ge(low, 1).
            tb_low = _resolve_cmp_cond(tb_cond, ctx, "Ge", 1)
            if tb_low is None:
                continue
            if canonical_symbol(tb_low.name) != canonical_symbol(low_ref.name):
                continue

            # low's def: Mod(H, 2^64).
            h_from_low = _match_chunk_def(ctx.definition(low_ref.name), "Mod")
            if h_from_low is None:
                continue

            # Find matching hi-dec anchor: Ite(B_lo, Sub(hi, 1), hi)
            # where B_lo (inline or SymRef-resolved) is Eq(low_alias, 0)
            # and hi's def is Div(H, 2^64) with the same H.
            matched_hi: tuple[int, TacExpr, str] | None = None
            for hi_idx, hi_cmd in hi_dec_anchors:
                hi_match = _match_hi_dec(hi_cmd.rhs)
                if hi_match is None:
                    continue
                b_lo_cond, hi_ref = hi_match
                b_lo_target = _resolve_cmp_cond(b_lo_cond, ctx, "Eq", 0)
                if b_lo_target is None:
                    continue
                if canonical_symbol(b_lo_target.name) != canonical_symbol(
                    low_ref.name
                ):
                    continue
                h_from_hi = _match_chunk_def(ctx.definition(hi_ref.name), "Div")
                if h_from_hi is None:
                    continue
                if canonical_symbol(h_from_hi.name) != canonical_symbol(
                    h_from_low.name
                ):
                    continue
                matched_hi = (hi_idx, b_lo_cond, hi_cmd.lhs)
                break
            if matched_hi is None:
                continue

            # Range gate: Ge(H, 1) must be derivable.
            h_range = infer_expr_range(h_from_low, ctx)
            if h_range is None or h_range[0] is None or h_range[0] < 1:
                continue

            # Locate the ``assume LNot(LAnd(b_lo, b_hi))`` in this
            # block — drop it when present (the H_new def + Ge(H, 1)
            # subsumes its content). The match looks up each LAnd
            # operand's def chain to verify both refer to chunks of
            # this site's H. Optional — if missing (e.g. already
            # dropped on a previous pass), we proceed and emit the
            # rewrite without the drop.
            h_canon = canonical_symbol(h_from_low.name)
            lnot_idx: int | None = None
            for idx, cmd in enumerate(block.commands):
                if not isinstance(cmd, AssumeExpCmd):
                    continue
                m = _match_lnot_land(cmd.condition)
                if m is None:
                    continue
                a_ref, b_ref = m
                a_tgt = _match_cmp_against_const(
                    ctx.definition(a_ref.name), "Eq", 0
                )
                b_tgt = _match_cmp_against_const(
                    ctx.definition(b_ref.name), "Eq", 0
                )
                if a_tgt is None or b_tgt is None:
                    continue
                a_chunk_low = _match_chunk_def(ctx.definition(a_tgt.name), "Mod")
                a_chunk_hi = _match_chunk_def(ctx.definition(a_tgt.name), "Div")
                b_chunk_low = _match_chunk_def(ctx.definition(b_tgt.name), "Mod")
                b_chunk_hi = _match_chunk_def(ctx.definition(b_tgt.name), "Div")
                matched = False
                if (
                    a_chunk_low is not None
                    and b_chunk_hi is not None
                    and canonical_symbol(a_chunk_low.name) == h_canon
                    and canonical_symbol(b_chunk_hi.name) == h_canon
                ):
                    matched = True
                if (
                    a_chunk_hi is not None
                    and b_chunk_low is not None
                    and canonical_symbol(a_chunk_hi.name) == h_canon
                    and canonical_symbol(b_chunk_low.name) == h_canon
                ):
                    matched = True
                if not matched:
                    continue
                lnot_idx = idx
                break

            sites.setdefault(block.id, []).append(
                _DecSite(
                    block_id=block.id,
                    h_name=canonical_symbol(h_from_low.name),
                    h_expr=h_from_low,
                    lo_dec_idx=lo_idx,
                    hi_dec_idx=matched_hi[0],
                    lnot_assume_idx=lnot_idx,
                    r_lo_dec_name=lo_cmd.lhs,
                    r_hi_dec_name=matched_hi[2],
                )
            )

    if not sites:
        return RewriteU128DecrementResult(
            program=program, hits=0, fresh_symbols=()
        )

    taken: set[str] = set()
    for block in program.blocks:
        for cmd in block.commands:
            lhs = getattr(cmd, "lhs", None)
            if isinstance(lhs, str):
                taken.add(canonical_symbol(lhs))

    def _pick_h_name() -> str:
        n = 0
        while True:
            name = f"H{n}"
            if name not in taken:
                taken.add(name)
                return name
            n += 1

    fresh_symbols: list[tuple[str, str]] = []
    hits = 0
    new_blocks: list[TacBlock] = []
    for block in program.blocks:
        block_sites = sites.get(block.id, ())
        if not block_sites:
            new_blocks.append(block)
            continue
        block_sites = sorted(block_sites, key=lambda s: s.hi_dec_idx)

        drops: set[int] = set()
        replacements: dict[int, AssignExpCmd] = {}
        inserts_before: dict[int, list[TacCmd]] = {}
        for site in block_sites:
            h_new = _pick_h_name()
            fresh_symbols.append((h_new, "bv256"))
            h_new_cmd = canonicalize_cmd(
                AssignExpCmd(
                    raw="",
                    lhs=h_new,
                    rhs=ApplyExpr("Sub", (site.h_expr, _ONE_BV)),
                )
            )
            new_hi_cmd = canonicalize_cmd(
                AssignExpCmd(
                    raw="",
                    lhs=site.r_hi_dec_name,
                    rhs=ApplyExpr("Div", (SymbolRef(h_new), _TWO_TO_64_BV)),
                )
            )
            new_lo_cmd = canonicalize_cmd(
                AssignExpCmd(
                    raw="",
                    lhs=site.r_lo_dec_name,
                    rhs=ApplyExpr("Mod", (SymbolRef(h_new), _TWO_TO_64_BV)),
                )
            )
            # Insert H_new immediately before the hi-dec position
            # (earliest of the two replacements). Replace hi/lo defs;
            # drop the original LNot-LAnd assume.
            insert_idx = min(site.hi_dec_idx, site.lo_dec_idx)
            inserts_before.setdefault(insert_idx, []).append(h_new_cmd)
            replacements[site.hi_dec_idx] = new_hi_cmd
            replacements[site.lo_dec_idx] = new_lo_cmd
            if site.lnot_assume_idx is not None:
                drops.add(site.lnot_assume_idx)
            hits += 1

        new_cmds: list[TacCmd] = []
        for idx, cmd in enumerate(block.commands):
            for q in inserts_before.get(idx, ()):
                new_cmds.append(q)
            if idx in drops:
                continue
            if idx in replacements:
                new_cmds.append(replacements[idx])
            else:
                new_cmds.append(cmd)
        new_blocks.append(replace(block, commands=new_cmds))

    return RewriteU128DecrementResult(
        program=TacProgram(blocks=new_blocks),
        hits=hits,
        fresh_symbols=tuple(fresh_symbols),
    )


__all__ = ["RewriteU128DecrementResult", "rewrite_u128_decrement"]
