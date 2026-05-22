"""Rewrite the chunked-u64 carry-correct addition idiom into a
lift / op / split form over a fresh wide-int.

Input (the canonical SBF lowering of a u128 add, after simplify
has settled on Mod / SymRef-named carry / AddIte-distributed Ite):

    R_sum   = narrow(IntAdd(R_lo, R_b))       ; R_lo, R_b u64
    R_low   = Mod(R_sum, 2^64)
    R_carry = Lt(2^64-1, R_sum)
    R_hi    = narrow(Ite(R_carry,
                         IntAdd(narrow(BASE), 1),
                         narrow(BASE)))         ; BASE u64

Output (T_sum holds the unwrapped int-domain wide sum; R_low and
R_hi become its low and high 64-bit chunks):

    T_sum = IntAdd(IntMul(BASE, 2^64), IntAdd(R_lo, R_b))
    R_low = Mod(T_sum, 2^64)
    R_hi  = IntDiv(T_sum, 2^64)

``R_sum`` and ``R_carry`` are dropped (DCE handles the residual
cleanup after their only consumers — R_low's Mod and R_hi's Ite —
get rewritten to consume T_sum instead).

Why a rewrite (not a materialized assume): the goal is that
downstream sees ONLY the lift / op / split shape, so the next
concept recognizer (decrement, divmod, ceil-div) can pattern-match
on uniform u128 arithmetic. A second "merge" rewrite will then
collapse adjacent ``Mod(T, 2^64) / IntDiv(T, 2^64)``-then-recombine
round-trips, leaving only the lifted wide-int operations.

rw-eq verification (per the per-cmd walker):

* LHS ``R_sum`` vs RHS (no counterpart) — rule 9b lhs-only-DCE.
* LHS ``R_carry`` vs RHS (no counterpart) — rule 9b.
* RHS ``T_sum`` (fresh name) — rule 3 rhs-only-fresh, no CHK.
* LHS / RHS ``R_low`` paired — rule 2 ``CHK = Eq(Mod(R_sum, 2^64),
  Mod(T_sum, 2^64))``. Discharges via ``T_sum = BASE*2^64 + R_sum``
  so the two are equal mod 2^64.
* LHS / RHS ``R_hi`` paired — rule 2 ``CHK = Eq(narrow(Ite(R_carry,
  BASE+1, BASE)), IntDiv(T_sum, 2^64))``. Discharges via case-split
  on ``R_lo + R_b >= 2^64``.

Both CHKs are closed-form and small; z3 closes them in
milliseconds. The proof obligation that the original chunked-add
implements wide-int addition has been moved from the SMT of the
overall VC into two local rw-eq lemmas — exactly the "rw-eq as the
soundness gate, work pushed in rather than out" principle.

Range gates: strict. ``infer_expr_range`` must prove
``R_lo, R_b, BASE <= 2^64-1`` before the rewrite fires.

Idempotent: skips a chain whose T_sum-style def already exists.
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
from ctac.rewrite.context import RewriteCtx, _is_safe_narrow_apply
from ctac.rewrite.range_infer import infer_expr_range
from ctac.rewrite.rules.common import const_to_int
from ctac.rewrite.unparse import canonicalize_cmd

_U64_MAX = (1 << 64) - 1
_TWO_TO_64 = 1 << 64
_TWO_TO_64_INT = ConstExpr(f"{hex(_TWO_TO_64)}(int)")


@dataclass(frozen=True)
class RewriteU128CarryAddResult:
    """Outcome of :func:`rewrite_u128_carry_add`.

    Attributes:
        program: rewritten program.
        hits: count of chain sites rewritten.
        fresh_symbols: ``(name, sort)`` pairs to add to the symbol table.
    """

    program: TacProgram
    hits: int
    fresh_symbols: tuple[tuple[str, str], ...]


def _peel_narrow(expr: TacExpr) -> TacExpr:
    while _is_safe_narrow_apply(expr):
        assert isinstance(expr, ApplyExpr)
        expr = expr.args[1]
    return expr


def _is_const(expr: TacExpr, value: int) -> bool:
    v = const_to_int(expr)
    return v is not None and v == value


def _match_carry_ite(rhs: TacExpr) -> tuple[TacExpr, TacExpr] | None:
    """Match ``narrow(Ite(carry, IntAdd(narrow(BASE), 1), narrow(BASE)))``.

    Returns ``(carry_expr, BASE_after_peel)`` on success.
    """
    inner = _peel_narrow(rhs)
    if not (
        isinstance(inner, ApplyExpr)
        and inner.op == "Ite"
        and len(inner.args) == 3
    ):
        return None
    carry, then_arm, else_arm = inner.args
    base = _peel_narrow(else_arm)
    then_inner = _peel_narrow(then_arm)
    if not (
        isinstance(then_inner, ApplyExpr)
        and then_inner.op == "IntAdd"
        and len(then_inner.args) == 2
    ):
        return None
    a, b = then_inner.args
    a_peeled = _peel_narrow(a)
    b_peeled = _peel_narrow(b)
    if a_peeled == base and _is_const(b, 1):
        return carry, base
    if b_peeled == base and _is_const(a, 1):
        return carry, base
    return None


def _match_carry_def(rhs: TacExpr) -> TacExpr | None:
    """Match ``Lt(2^64-1, R_sum)``; return ``R_sum`` if matched."""
    if not (isinstance(rhs, ApplyExpr) and rhs.op == "Lt" and len(rhs.args) == 2):
        return None
    a, b = rhs.args
    if _is_const(a, _U64_MAX):
        return b
    return None


def _match_sum_def(rhs: TacExpr) -> tuple[TacExpr, TacExpr] | None:
    """Match ``narrow(IntAdd(R_lo, R_b))``; return ``(R_lo, R_b)``."""
    inner = _peel_narrow(rhs)
    if not (
        isinstance(inner, ApplyExpr)
        and inner.op == "IntAdd"
        and len(inner.args) == 2
    ):
        return None
    return inner.args[0], inner.args[1]


def _match_low_def(rhs: TacExpr, r_sum_canon: str) -> bool:
    """Match ``Mod(R_sum, 2^64)`` referencing ``R_sum`` by canonical name."""
    if not (isinstance(rhs, ApplyExpr) and rhs.op == "Mod" and len(rhs.args) == 2):
        return False
    a, b = rhs.args
    if not (isinstance(a, SymbolRef) and canonical_symbol(a.name) == r_sum_canon):
        return False
    return _is_const(b, _TWO_TO_64)


def _u64_bounded(expr: TacExpr, ctx: RewriteCtx) -> bool:
    rng = infer_expr_range(expr, ctx)
    if rng is None:
        return False
    lo, hi = rng
    if lo is None or hi is None:
        return False
    return lo >= 0 and hi <= _U64_MAX


def _build_t_sum_rhs(base: TacExpr, r_lo: TacExpr, r_b: TacExpr) -> TacExpr:
    """``IntAdd(IntMul(BASE, 2^64), IntAdd(R_lo, R_b))``."""
    return ApplyExpr(
        "IntAdd",
        (
            ApplyExpr("IntMul", (base, _TWO_TO_64_INT)),
            ApplyExpr("IntAdd", (r_lo, r_b)),
        ),
    )


def _pick_fresh_name(taken: set[str], prefix: str = "T_u128_") -> str:
    n = 0
    while True:
        name = f"{prefix}{n}"
        if name not in taken:
            taken.add(name)
            return name
        n += 1


@dataclass(frozen=True)
class _ChainSite:
    """One matched carry-add chain ready to be rewritten.

    ``carry_idx`` is ``None`` when the carry condition was inline in
    the R_hi Ite rather than named via a separate SymbolRef def.
    """

    block_id: str
    sum_idx: int  # cmd_index of ``R_sum = narrow(IntAdd(R_lo, R_b))``
    low_idx: int  # cmd_index of ``R_low = Mod(R_sum, 2^64)``
    carry_idx: int | None  # cmd_index of ``R_carry = Lt(...)`` if named
    hi_idx: int  # cmd_index of ``R_hi = narrow(Ite(...))``
    r_low_name: str
    r_hi_name: str
    base: TacExpr
    r_lo: TacExpr
    r_b: TacExpr


def rewrite_u128_carry_add(
    program: TacProgram,
    *,
    symbol_sorts: dict[str, str] | None = None,
) -> RewriteU128CarryAddResult:
    """Walk the program and rewrite every chunked-u64 carry-correct
    addition chain into the int-domain lift / op / split form."""
    ctx = RewriteCtx(program, symbol_sorts=symbol_sorts or {})

    # Find sites first; we'll splice the block in a second pass.
    sites: dict[str, list[_ChainSite]] = {}
    for block in program.blocks:
        for idx, cmd in enumerate(block.commands):
            if not (
                isinstance(cmd, AssignExpCmd) and isinstance(cmd.rhs, ApplyExpr)
            ):
                continue
            ite_match = _match_carry_ite(cmd.rhs)
            if ite_match is None:
                continue
            carry_expr, base = ite_match
            ctx.set_position(block.id, idx)

            # The carry condition can arrive either as a ``SymbolRef``
            # to a previously named bool (post-ITE_PURIFY shape) or as
            # the inline ``Lt(2^64-1, R_sum)`` expression (the
            # pre-ITE_PURIFY canonical shape that this pass actually
            # runs against). Resolve both forms to ``R_sum``.
            r_sum: TacExpr | None = None
            carry_idx: int | None = None
            if isinstance(carry_expr, SymbolRef):
                carry_def = ctx.definition(carry_expr.name)
                if carry_def is None:
                    continue
                r_sum = _match_carry_def(carry_def)
            elif isinstance(carry_expr, ApplyExpr):
                r_sum = _match_carry_def(carry_expr)
            if not isinstance(r_sum, SymbolRef):
                continue
            r_sum_canon = canonical_symbol(r_sum.name)

            sum_def = ctx.definition(r_sum.name)
            if sum_def is None:
                continue
            sum_args = _match_sum_def(sum_def)
            if sum_args is None:
                continue
            r_lo, r_b = sum_args

            # Locate the sibling ``R_low = Mod(R_sum, 2^64)`` and (if
            # the carry was a named SymbolRef) its def position by cmd
            # index in this block. ``carry_idx`` stays None when the
            # carry is inline — there's no separate carry assignment
            # to drop.
            low_idx: int | None = None
            sum_idx: int | None = None
            r_low_name: str | None = None
            carry_sym_canon: str | None = (
                canonical_symbol(carry_expr.name)
                if isinstance(carry_expr, SymbolRef)
                else None
            )
            for sib_idx, sib in enumerate(block.commands):
                if not isinstance(sib, AssignExpCmd):
                    continue
                if isinstance(sib.rhs, ApplyExpr):
                    if _match_low_def(sib.rhs, r_sum_canon):
                        if low_idx is not None:
                            # Multiple low-defs — ambiguous, bail.
                            low_idx = None
                            break
                        low_idx = sib_idx
                        r_low_name = sib.lhs
                if (
                    carry_sym_canon is not None
                    and canonical_symbol(sib.lhs) == carry_sym_canon
                ):
                    carry_idx = sib_idx
                if canonical_symbol(sib.lhs) == r_sum_canon:
                    sum_idx = sib_idx
            if low_idx is None or sum_idx is None or r_low_name is None:
                continue

            if not _u64_bounded(r_lo, ctx):
                continue
            if not _u64_bounded(r_b, ctx):
                continue
            if not _u64_bounded(base, ctx):
                continue

            sites.setdefault(block.id, []).append(
                _ChainSite(
                    block_id=block.id,
                    sum_idx=sum_idx,
                    low_idx=low_idx,
                    carry_idx=carry_idx,
                    hi_idx=idx,
                    r_low_name=r_low_name,
                    r_hi_name=cmd.lhs,
                    base=base,
                    r_lo=r_lo,
                    r_b=r_b,
                )
            )

    if not sites:
        return RewriteU128CarryAddResult(
            program=program, hits=0, fresh_symbols=()
        )

    # Allocate fresh names for each chain's T_sum, then rewrite.
    taken: set[str] = set()
    # Pre-populate ``taken`` from the existing symbol table-ish set.
    for block in program.blocks:
        for cmd in block.commands:
            lhs = getattr(cmd, "lhs", None)
            if isinstance(lhs, str):
                taken.add(canonical_symbol(lhs))

    fresh_symbols: list[tuple[str, str]] = []
    hits = 0
    new_blocks: list[TacBlock] = []
    for block in program.blocks:
        block_sites = sites.get(block.id, ())
        if not block_sites:
            new_blocks.append(block)
            continue
        # Order sites by sum_idx (earliest first) so the T_sum insertion
        # position is stable when there's more than one chain per block.
        block_sites = sorted(block_sites, key=lambda s: s.sum_idx)
        # Map cmd_index -> action to apply.
        # action = ("drop",) or ("replace", new_cmd) or ("insert_before", new_cmd).
        drops: set[int] = set()
        replacements: dict[int, AssignExpCmd] = {}
        inserts_before: dict[int, list[AssignExpCmd]] = {}
        for site in block_sites:
            t_sum_name = _pick_fresh_name(taken)
            fresh_symbols.append((t_sum_name, "int"))
            t_sum_rhs = _build_t_sum_rhs(site.base, site.r_lo, site.r_b)
            t_sum_cmd = canonicalize_cmd(
                AssignExpCmd(raw="", lhs=t_sum_name, rhs=t_sum_rhs)
            )
            new_low_cmd = canonicalize_cmd(
                AssignExpCmd(
                    raw="",
                    lhs=site.r_low_name,
                    rhs=ApplyExpr(
                        "Mod", (SymbolRef(t_sum_name), _TWO_TO_64_INT)
                    ),
                )
            )
            new_hi_cmd = canonicalize_cmd(
                AssignExpCmd(
                    raw="",
                    lhs=site.r_hi_name,
                    rhs=ApplyExpr(
                        "IntDiv", (SymbolRef(t_sum_name), _TWO_TO_64_INT)
                    ),
                )
            )
            # Drop R_sum and (if separately named) R_carry; replace
            # R_low and R_hi; insert T_sum just before where R_sum used
            # to live so it dominates both rewrites.
            drops.add(site.sum_idx)
            if site.carry_idx is not None:
                drops.add(site.carry_idx)
            replacements[site.low_idx] = new_low_cmd
            replacements[site.hi_idx] = new_hi_cmd
            inserts_before.setdefault(site.sum_idx, []).append(t_sum_cmd)
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

    return RewriteU128CarryAddResult(
        program=TacProgram(blocks=new_blocks),
        hits=hits,
        fresh_symbols=tuple(fresh_symbols),
    )


__all__ = [
    "RewriteU128CarryAddResult",
    "rewrite_u128_carry_add",
]
