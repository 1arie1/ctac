"""Rewrite the shifted-sum recombination of two negation gadgets
into a named ``neg128`` value plus a signed-limb composite.

The SBF lowering of the i128 negation (the cvlr mathint encode
boundary) recombines the two sign-extended negated limbs naively::

    n1    = narrow(Ite(Eq(lo, 0), hi, hi + 1))     ; un-borrow
    y     = Mod(n1, 2^w)
    g_hi  = Ite(Eq(y, 2^(w-1)), n1, wrap_256(-from_s<w>(y)))
    g_lo  = Ite(Eq(lo, 2^(w-1)), lo, wrap_256(-from_s<w>(lo)))
    R     = Add(ShiftLeft(g_hi, w), g_lo)

with ``(lo, hi)`` the ``Mod`` / ``Div``-by-``2^w`` chunks of an
``X`` provably in ``[0, 2^2w)``. The composite is NOT the s256
encoding of ``-X`` as an i128: each limb extends independently, so
a ``-2^w`` artifact appears whenever the negated lo limb has its
sign bit set, and the gadget MIN arms pass through unextended.
The full-domain closed form (z3-checked in the tests, no gates —
the MIN arms carry the exceptional encodings)::

    HN = Ite(Eq(X, 0), 0, IntSub(2^2w, X))         ; neg128(X), named
    R  = Ite(Eq(y, 2^(w-1)),  Add(ShiftLeft(n1, w), g_lo),
         Ite(Eq(lo, 2^(w-1)), Add(ShiftLeft(wrap_hi, w), lo),
              wrap_256(from_s<w>(Div(HN, 2^w)) * 2^w
                       + from_s<w>(Mod(HN, 2^w)))))

``HN`` is emitted in the materialized-negchunk Ite shape (the house
spelling of ``(-X) mod 2^2w`` — no fresh ``Mod`` atom; the guard
folds when a dominating ``X >= 1`` exists). Its chunk defs use the
reserved ``Q<N>`` u64-register prefix. The MIN arms keep the
original sub-expressions with the guard-decided gadget substituted
(each arm shrinks; nothing is dropped — the encodings are reachable
and only path knowledge like the source's band assumes prunes them,
which is the solver's job).

What this buys: ``neg128(X)`` becomes a first-class value
(extraction-pair anchor for the coalescer, ModDivPin fodder), and
the clean arm is ``Cmp(wrap_256(v), c)``-shaped with a derivable
range on ``v`` — WrapCompareLift's existing gate — so the source's
i128 band assumes lift to linear predicates on the signed-limb sum.

rw-eq: HN / Q chunks are rhs-only fresh assigns (rule 3); the
rewritten recombination def is one rule-2 CHK discharged by the
full-domain identity with the un-borrow / Mod / Div defs and the
X-range assume in scope (case split + linear + mod).
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
from ctac.rewrite.rules.common import DIV_OPS, MOD_OPS, const_to_int
from ctac.rewrite.rules.sign_extend import (
    _canon_sym,
    _eq_other_side,
    _match_neg_gadget,
    _Width,
)
from ctac.rewrite.unparse import canonicalize_cmd

_WRAP_NAME = "wrap_twos_complement_256:bif"
_UNWRAP_BY_BITS = {
    64: "unwrap_twos_complement_64:bif",
    128: "unwrap_twos_complement_128:bif",
}


@dataclass(frozen=True)
class NegS128RecombineResult:
    program: TacProgram
    hits: int
    fresh_symbols: tuple[tuple[str, str], ...]


def _match_shifted_sum(
    rhs: TacExpr,
) -> tuple[SymbolRef, SymbolRef, int, TacExpr] | None:
    """``Add(ShiftLeft(g_hi, w), g_lo)`` (either Add order); returns
    ``(g_hi, g_lo, w_bits, shift_const)``."""
    if not (
        isinstance(rhs, ApplyExpr) and rhs.op == "Add" and len(rhs.args) == 2
    ):
        return None
    for shl, other in (rhs.args, rhs.args[::-1]):
        if not (
            isinstance(shl, ApplyExpr)
            and shl.op == "ShiftLeft"
            and len(shl.args) == 2
            and isinstance(shl.args[0], SymbolRef)
            and isinstance(other, SymbolRef)
        ):
            continue
        bits = const_to_int(shl.args[1])
        if bits in _UNWRAP_BY_BITS:
            return shl.args[0], other, bits, shl.args[1]
    return None


def _match_unborrow(
    n1: TacExpr, ctx: RewriteCtx, width: _Width
) -> tuple[SymbolRef, SymbolRef] | None:
    """``narrow(Ite(g0, hi, hi + 1))`` with ``g0 <=> Eq(lo, 0)``;
    returns ``(lo, hi)``."""
    e = ctx.lookthrough(n1)
    if not (isinstance(e, ApplyExpr) and e.op == "Ite" and len(e.args) == 3):
        return None
    g0, then_arm, else_arm = e.args
    if not isinstance(then_arm, SymbolRef):
        return None
    if not (
        isinstance(else_arm, ApplyExpr)
        and else_arm.op in ("IntAdd", "Add")
        and len(else_arm.args) == 2
    ):
        return None
    a, b = else_arm.args
    if const_to_int(b) == 1 and _canon_sym(a) == _canon_sym(then_arm):
        pass
    elif const_to_int(a) == 1 and _canon_sym(b) == _canon_sym(then_arm):
        pass
    else:
        return None
    lo = _eq_other_side(ctx.lookthrough(g0), 0)
    if not isinstance(lo, SymbolRef):
        return None
    return lo, then_arm


def _chunk_source(
    sym: SymbolRef, ctx: RewriteCtx, width: _Width, ops: frozenset[str]
) -> SymbolRef | None:
    d = ctx.definition(sym.name)
    if not (
        isinstance(d, ApplyExpr)
        and d.op in ops
        and len(d.args) == 2
        and isinstance(d.args[0], SymbolRef)
        and const_to_int(d.args[1]) == width.full
    ):
        return None
    return d.args[0]


def _ranged_below(expr: TacExpr, ctx: RewriteCtx, bound: int) -> bool:
    rng = infer_expr_range(expr, ctx)
    if rng is None:
        return False
    lo, hi = rng
    return lo is not None and hi is not None and lo >= 0 and hi < bound


@dataclass(frozen=True)
class _Site:
    block_id: str
    idx: int
    x: SymbolRef
    bits: int
    cond_hi: TacExpr
    cond_lo: TacExpr
    n1: SymbolRef
    wrap_hi: TacExpr
    lo: SymbolRef
    g_lo: SymbolRef
    shift_const: TacExpr


def rewrite_neg_s128_recombine(
    program: TacProgram,
    *,
    symbol_sorts: dict[str, str] | None = None,
) -> NegS128RecombineResult:
    ctx = RewriteCtx(program, symbol_sorts=symbol_sorts or {})
    sites: list[_Site] = []
    for block in program.blocks:
        for idx, cmd in enumerate(block.commands):
            if not (
                isinstance(cmd, AssignExpCmd)
                and isinstance(cmd.rhs, ApplyExpr)
            ):
                continue
            top = _match_shifted_sum(cmd.rhs)
            if top is None:
                continue
            g_hi_sym, g_lo_sym, bits, shift_const = top
            hi_ite = ctx.lookthrough(g_hi_sym)
            lo_ite = ctx.lookthrough(g_lo_sym)
            m_hi = _match_neg_gadget(hi_ite, ctx)
            m_lo = _match_neg_gadget(lo_ite, ctx)
            if m_hi is None or m_lo is None:
                continue
            _y_hi, n1, w_hi = m_hi
            y_lo, _x_lo, w_lo = m_lo
            if w_hi is not w_lo or w_hi.bits != bits:
                continue
            if not isinstance(n1, SymbolRef):
                continue
            ub = _match_unborrow(n1, ctx, w_hi)
            if ub is None:
                continue
            lo_sym, hi_sym = ub
            if _canon_sym(y_lo) != _canon_sym(lo_sym):
                continue
            x_of_lo = _chunk_source(lo_sym, ctx, w_hi, MOD_OPS)
            x_of_hi = _chunk_source(hi_sym, ctx, w_hi, DIV_OPS)
            if (
                x_of_lo is None
                or x_of_hi is None
                or _canon_sym(x_of_lo) != _canon_sym(x_of_hi)
            ):
                continue
            x = x_of_lo
            ctx.set_position(block.id, idx)
            if not _ranged_below(x, ctx, 1 << (2 * bits)):
                continue
            assert isinstance(hi_ite, ApplyExpr)
            assert isinstance(lo_ite, ApplyExpr)
            sites.append(
                _Site(
                    block_id=block.id,
                    idx=idx,
                    x=x,
                    bits=bits,
                    cond_hi=hi_ite.args[0],
                    cond_lo=lo_ite.args[0],
                    n1=n1,
                    wrap_hi=hi_ite.args[2],
                    lo=lo_sym,
                    g_lo=g_lo_sym,
                    shift_const=shift_const,
                )
            )

    if not sites:
        return NegS128RecombineResult(program, 0, ())

    taken: set[str] = set()
    for block in program.blocks:
        for cmd in block.commands:
            lhs = getattr(cmd, "lhs", None)
            if isinstance(lhs, str):
                taken.add(canonical_symbol(lhs))

    def fresh(prefix: str) -> str:
        n = 0
        while True:
            name = f"{prefix}{n}"
            if name not in taken:
                taken.add(name)
                return name
            n += 1

    fresh_symbols: list[tuple[str, str]] = []
    hits = 0
    by_block: dict[str, list[_Site]] = {}
    for s in sites:
        by_block.setdefault(s.block_id, []).append(s)
    new_blocks: list[TacBlock] = []
    for block in program.blocks:
        block_sites = by_block.get(block.id)
        if not block_sites:
            new_blocks.append(block)
            continue
        commands: list[TacCmd] = list(block.commands)
        inserts: list[tuple[int, list[TacCmd]]] = []
        for site in block_sites:
            full2 = 1 << (2 * site.bits)
            w_const_bv = ConstExpr(hex(1 << site.bits))
            w_const_int = ConstExpr(f"{hex(1 << site.bits)}(int)")
            unwrap = SymbolRef(_UNWRAP_BY_BITS[site.bits])
            h_name = fresh("H")
            ql_name = fresh("Q")
            qh_name = fresh("Q")
            fresh_symbols.extend(
                [(h_name, "bv256"), (ql_name, "bv256"), (qh_name, "bv256")]
            )
            h_def = canonicalize_cmd(
                AssignExpCmd(
                    raw="",
                    lhs=h_name,
                    rhs=ApplyExpr(
                        "Ite",
                        (
                            ApplyExpr("Eq", (site.x, ConstExpr("0x0"))),
                            ConstExpr("0x0"),
                            ApplyExpr(
                                "IntSub",
                                (ConstExpr(f"{hex(full2)}(int)"), site.x),
                            ),
                        ),
                    ),
                )
            )
            ql_def = canonicalize_cmd(
                AssignExpCmd(
                    raw="",
                    lhs=ql_name,
                    rhs=ApplyExpr("Mod", (SymbolRef(h_name), w_const_bv)),
                )
            )
            qh_def = canonicalize_cmd(
                AssignExpCmd(
                    raw="",
                    lhs=qh_name,
                    rhs=ApplyExpr("Div", (SymbolRef(h_name), w_const_bv)),
                )
            )
            composite = ApplyExpr(
                "Apply",
                (
                    SymbolRef(_WRAP_NAME),
                    ApplyExpr(
                        "IntAdd",
                        (
                            ApplyExpr(
                                "IntMul",
                                (
                                    ApplyExpr(
                                        "Apply",
                                        (unwrap, SymbolRef(qh_name)),
                                    ),
                                    w_const_int,
                                ),
                            ),
                            ApplyExpr("Apply", (unwrap, SymbolRef(ql_name))),
                        ),
                    ),
                ),
            )

            def shifted_sum(hi_part: TacExpr, lo_part: TacExpr) -> TacExpr:
                return ApplyExpr(
                    "Add",
                    (
                        ApplyExpr(
                            "ShiftLeft", (hi_part, site.shift_const)
                        ),
                        lo_part,
                    ),
                )

            new_rhs = ApplyExpr(
                "Ite",
                (
                    site.cond_hi,
                    shifted_sum(site.n1, site.g_lo),
                    ApplyExpr(
                        "Ite",
                        (
                            site.cond_lo,
                            shifted_sum(site.wrap_hi, site.lo),
                            composite,
                        ),
                    ),
                ),
            )
            old = commands[site.idx]
            assert isinstance(old, AssignExpCmd)
            commands[site.idx] = canonicalize_cmd(
                replace(old, raw="", rhs=new_rhs)
            )
            inserts.append((site.idx, [h_def, ql_def, qh_def]))
            hits += 1
        for at, defs in sorted(inserts, key=lambda t: t[0], reverse=True):
            commands[at:at] = defs
        new_blocks.append(replace(block, commands=commands))

    return NegS128RecombineResult(
        program=TacProgram(blocks=new_blocks),
        hits=hits,
        fresh_symbols=tuple(fresh_symbols),
    )
