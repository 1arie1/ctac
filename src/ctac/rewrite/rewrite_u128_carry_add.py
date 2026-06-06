"""Rewrite the chunked-u64 carry-correct addition idiom into a
fresh u128 ``half-register`` (``H<N>``) plus bv Mod / Div chunks.

Naming convention: ``H<N>`` is a bv256-typed register that holds
a u128 value (half of the bv256 width — hence "H"). ``Q<N>``
(reserved for upcoming rules) is a bv256 register holding a u64.
Both are bv registers; their operations are bv operations
(``Mod`` / ``Div``, not ``IntMod`` / ``IntDiv``). Int-domain
arithmetic appears only inside ``narrow(...)`` at the boundary.

Input (the canonical SBF lowering of a u128 add, after simplify
has settled on Mod / SymRef-named carry / AddIte-distributed Ite):

    R_sum   = narrow(IntAdd(R_lo, R_b))       ; R_lo, R_b u64
    R_low   = Mod(R_sum, 2^64)
    R_carry = Lt(2^64-1, R_sum)
    R_hi    = narrow(Ite(R_carry,
                         IntAdd(narrow(BASE), 1),
                         narrow(BASE)))         ; BASE u64

Output: fresh u128 half-register ``H<N>`` capturing the wide sum,
with an explicit u128 bound assume (derived, not invented); the
original ``R_low`` and ``R_hi`` chunks become bv ``Mod`` / ``Div``
of ``H<N>``:

    H<N>  = narrow(IntAdd(IntMul(BASE, 2^64), IntAdd(R_lo, R_b)))
    assume Le(H<N>, derived_hi)            ; from range-inference
    R_low = Mod(H<N>, 2^64)                ; bv Mod (bound obvious)
    R_hi  = Div(H<N>, 2^64)                ; bv Div

The ``narrow`` is sound only when the inner int expression is
provably in ``[0, 2^256-1]``; the rewrite checks this via
``infer_expr_range`` and bails when the bound can't be derived.

``R_sum`` and (if separately named) ``R_carry`` are left in place —
deleting defs is DCE's job, not a recognizer's. The chunk
intermediates can have consumers beyond this chain (e.g. a
previously purified ``Ite(TB, ...)`` overflow check elsewhere in
the block); an eager drop orphans such a use (use-before-def),
while a kept def stays well-formed and DCE clears it exactly when
it is actually dead.

Why a rewrite (not a materialized assume): the goal is that
downstream sees ONLY the lift / op / split shape, so the next
concept recognizer (decrement, divmod, ceil-div) can pattern-match
on uniform u128 arithmetic. A second "merge" rewrite will then
collapse adjacent ``Mod(H, 2^64) / Div(H, 2^64)``-then-recombine
round-trips, leaving only the lifted wide-int operations.

rw-eq verification (per the per-cmd walker):

* LHS / RHS ``R_sum`` paired identical — no CHK (DCE may later turn
  these into rule 9b lhs-only-DCE; both shapes discharge).
* LHS / RHS ``R_carry`` paired identical — same.
* RHS ``H<N>`` (fresh name) — rule 3 rhs-only-fresh, no CHK.
* RHS ``assume Le(H<N>, derived_hi)`` — rule 4 rhs-only-assume.
  CHK = ``Le(narrow(<int sum>), derived_hi)``. Discharges via the
  operand range bounds in scope (the rewrite gates the operand u64
  bounds before firing, so the int sum's bound is a derived
  arithmetic fact).
* LHS / RHS ``R_low`` paired — rule 2 ``CHK = Eq(Mod(R_sum, 2^64),
  Mod(H<N>, 2^64))``. Discharges via ``H<N> = BASE*2^64 + R_sum``
  so the two are equal mod 2^64.
* LHS / RHS ``R_hi`` paired — rule 2 ``CHK = Eq(narrow(Ite(R_carry,
  BASE+1, BASE)), Div(H<N>, 2^64))``. Discharges via case-split on
  ``R_lo + R_b >= 2^64``.

All CHKs are closed-form and small; z3 closes them in
milliseconds. The proof obligation that the original chunked-add
implements wide-int addition has been moved from the SMT of the
overall VC into local rw-eq lemmas — exactly the "rw-eq as the
soundness gate, work pushed in rather than out" principle.

Range gates: strict. ``infer_expr_range`` must prove
``R_lo, R_b, BASE <= 2^64-1`` AND derive a concrete upper bound on
the int-domain sum that fits in bv256 (i.e. the narrow is
provably safe) before the rewrite fires. Bounds are never invented.

Idempotent: a program already in the H<N>-narrow shape is a no-op
(the matcher only fires on the chunked carry-Ite shape).
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
from ctac.rewrite.context import RewriteCtx, _is_safe_narrow_apply
from ctac.rewrite.range_infer import infer_expr_range
from ctac.rewrite.rules.common import const_to_int
from ctac.rewrite.unparse import canonicalize_cmd

_U64_MAX = (1 << 64) - 1
_BV256_MAX = (1 << 256) - 1
_TWO_TO_64 = 1 << 64
_TWO_TO_64_INT = ConstExpr(f"{hex(_TWO_TO_64)}(int)")
_TWO_TO_64_BV = ConstExpr(f"{hex(_TWO_TO_64)}")  # bv-style (untagged)
_NARROW_FN = SymbolRef("safe_math_narrow_bv256:bif")


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


def _pick_fresh_name(taken: set[str], *, prefix: str = "H") -> str:
    """Pick ``<prefix><N>`` not present in ``taken``; default ``H<N>``
    for the u128 half-register."""
    n = 0
    while True:
        name = f"{prefix}{n}"
        if name not in taken:
            taken.add(name)
            return name
        n += 1


def _bv_const(value: int) -> ConstExpr:
    """Render ``value`` as an untagged bv-style hex literal."""
    return ConstExpr(f"{hex(value)}")


def _int_const(value: int) -> ConstExpr:
    """Render ``value`` as an ``(int)``-tagged hex literal."""
    return ConstExpr(f"{hex(value)}(int)")


@dataclass(frozen=True)
class _ChainSite:
    """One matched carry-add chain ready to be rewritten."""

    block_id: str
    sum_idx: int  # cmd_index of ``R_sum = narrow(IntAdd(R_lo, R_b))``
    low_idx: int  # cmd_index of ``R_low = Mod(R_sum, 2^64)``
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

            # Locate the sibling ``R_low = Mod(R_sum, 2^64)`` and the
            # ``R_sum`` def position by cmd index in this block.
            low_idx: int | None = None
            sum_idx: int | None = None
            r_low_name: str | None = None
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
        block_sites = sorted(block_sites, key=lambda s: s.sum_idx)
        replacements: dict[int, AssignExpCmd] = {}
        inserts_before: dict[int, list[TacCmd]] = {}
        for site in block_sites:
            # Derive the full int-sum's range. Bail unless we can
            # prove the sum fits in bv256 (the narrow precondition);
            # bounds are never invented.
            t_int_rhs = _build_t_sum_rhs(site.base, site.r_lo, site.r_b)
            t_int_range = infer_expr_range(t_int_rhs, ctx)
            if t_int_range is None:
                continue
            t_lo, t_hi = t_int_range
            if t_lo is None or t_hi is None:
                continue
            if t_hi > _BV256_MAX or t_lo < 0:
                continue

            # Partial sum (R_lo +int R_b): we materialize its bound
            # too so the partial intermediate's range is explicit in
            # the TAC and downstream rules don't have to re-derive it.
            partial_rhs = ApplyExpr("IntAdd", (site.r_lo, site.r_b))
            partial_range = infer_expr_range(partial_rhs, ctx)
            if (
                partial_range is None
                or partial_range[0] is None
                or partial_range[1] is None
            ):
                continue

            # BASE's bound. Materialize alongside the partial-sum
            # bound so the H<N> bound is *locally* provable from
            # in-scope facts (BASE_hi, partial_hi -> H<N>_hi) without
            # needing the reader to walk BASE's def chain. Skip if
            # BASE is already a literal (bound is trivially the
            # literal value).
            base_range = infer_expr_range(site.base, ctx)
            if (
                base_range is None
                or base_range[0] is None
                or base_range[1] is None
            ):
                continue
            base_is_const = isinstance(site.base, ConstExpr)

            h_name = _pick_fresh_name(taken, prefix="H")
            fresh_symbols.append((h_name, "bv256"))

            # Build the H<N>-narrow def: ``H = narrow(int_sum)``. The
            # ``narrow`` is sound because t_hi <= 2^256-1 and t_lo >= 0.
            narrow_rhs = ApplyExpr("Apply", (_NARROW_FN, t_int_rhs))
            h_cmd = canonicalize_cmd(
                AssignExpCmd(raw="", lhs=h_name, rhs=narrow_rhs)
            )
            # BASE bound: ``assume Le(BASE, base_hi)``. Without this,
            # H<N>'s bound's derivation routes through BASE's
            # arbitrary upstream def chain (e.g. on csb_lemma BASE is
            # ``I102 = IntMulDiv(R96, R90, 2^50)`` and the
            # ``infer_expr_range`` traversal needs the IntMulDiv
            # handler — fine for the encoder, opaque to a reader).
            # Materializing it here makes the bound visible locally.
            base_bound_cmd: TacCmd | None = None
            if not base_is_const:
                base_bound_cmd = canonicalize_cmd(
                    AssumeExpCmd(
                        raw="",
                        condition=ApplyExpr(
                            "Le",
                            (site.base, _bv_const(base_range[1])),
                        ),
                    )
                )
            # Partial-sum bound: ``assume Le(R_lo +int R_b, partial_hi)``.
            # Materializes the carry-precondition for the user: if the
            # partial sum exceeds u64 the carry bit fires, and the
            # explicit bound makes that visible to range inference and
            # to rw-eq's CHK without re-deriving from operand ranges.
            partial_bound_cmd = canonicalize_cmd(
                AssumeExpCmd(
                    raw="",
                    condition=ApplyExpr(
                        "Le",
                        (
                            partial_rhs,
                            _int_const(partial_range[1]),
                        ),
                    ),
                )
            )
            # H<N>'s u128-ish bound: ``assume Le(H<N>, t_hi)``. Tighter
            # than the bv256-sort default; not obvious from
            # ``H = narrow(...)`` alone. Locally derivable from the
            # BASE bound + partial-sum bound emitted just above.
            h_bound_cmd = canonicalize_cmd(
                AssumeExpCmd(
                    raw="",
                    condition=ApplyExpr(
                        "Le",
                        (SymbolRef(h_name), _bv_const(t_hi)),
                    ),
                )
            )
            new_low_cmd = canonicalize_cmd(
                AssignExpCmd(
                    raw="",
                    lhs=site.r_low_name,
                    rhs=ApplyExpr(
                        "Mod", (SymbolRef(h_name), _TWO_TO_64_BV)
                    ),
                )
            )
            new_hi_cmd = canonicalize_cmd(
                AssignExpCmd(
                    raw="",
                    lhs=site.r_hi_name,
                    rhs=ApplyExpr(
                        "Div", (SymbolRef(h_name), _TWO_TO_64_BV)
                    ),
                )
            )
            replacements[site.low_idx] = new_low_cmd
            replacements[site.hi_idx] = new_hi_cmd
            pre_h_cmds: list[TacCmd] = []
            if base_bound_cmd is not None:
                pre_h_cmds.append(base_bound_cmd)
            pre_h_cmds.append(partial_bound_cmd)
            pre_h_cmds.append(h_cmd)
            pre_h_cmds.append(h_bound_cmd)
            inserts_before.setdefault(site.sum_idx, []).extend(pre_h_cmds)
            hits += 1

        new_cmds: list[TacCmd] = []
        for idx, cmd in enumerate(block.commands):
            for q in inserts_before.get(idx, ()):
                new_cmds.append(q)
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
