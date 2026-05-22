"""Materialize ``assume Ge(H, 1)`` from the chunked nonzero precondition.

Pattern (the canonical SBF-lowered "u128 H is nonzero" precondition
that gates a subsequent decrement / borrow chain):

    R_low = Mod(H, 2^64)
    R_hi  = Div(H, 2^64)
    B_lo  = Eq(R_low, 0)
    B_hi  = Eq(R_hi, 0)
    assume LNot(LAnd(B_lo, B_hi))         ; H's chunks aren't both zero

The pass leaves all of the above in place and *adds* ``assume
Ge(H, 1)`` immediately after the ``LNot(LAnd(...))`` assume.

The new assume is derivable: ``H = R_hi * 2^64 + R_low`` (the
Euclidean identity for the chunk extraction) plus the chunks being
non-negative means ``H = 0`` iff both chunks are zero. The
``LNot(LAnd(...))`` assume forbids that, so ``H >= 1``. rw-eq's
rule-4 rhs-only-assume CHK is exactly this case-split argument —
z3 closes it locally.

Why a separate pass (rather than rolled into the decrement
recognizer): ``Ge(H, 1)`` is an independently useful fact
once it lands in range inference. Future rules that look at H's
range (the u128 decrement, downstream concept recognizers, the
ceil-div lifter) get the bound without needing to re-discover it.
The decomposition matches the broader "rewrites are small, local,
composable" principle.

Pass placement: runs after the carry-add lift (so ``H`` exists as
a bv256 register) and before the decrement rewrite (which needs
``Ge(H, 1)`` in range inference to gate its bv ``Sub``).

Idempotent: skipped per-pattern if an identical ``Ge(H, 1)``
assume already follows.
"""

from __future__ import annotations

from dataclasses import dataclass, replace

from ctac.analysis.symbols import canonical_symbol
from ctac.ast.nodes import (
    ApplyExpr,
    AssumeExpCmd,
    ConstExpr,
    SymbolRef,
    TacCmd,
    TacExpr,
)
from ctac.ir.models import TacBlock, TacProgram
from ctac.rewrite.context import RewriteCtx
from ctac.rewrite.rules.common import const_to_int
from ctac.rewrite.unparse import canonicalize_cmd

_TWO_TO_64 = 1 << 64
_ONE_BV = ConstExpr("0x1")


@dataclass(frozen=True)
class MaterializeHNonzeroResult:
    """Outcome of :func:`materialize_h_nonzero`."""

    program: TacProgram
    hits: int


def _match_lnot_land(cond: TacExpr) -> tuple[TacExpr, TacExpr] | None:
    """Match ``LNot(LAnd(a, b))``; return ``(a, b)`` or ``None``."""
    if not (isinstance(cond, ApplyExpr) and cond.op == "LNot" and len(cond.args) == 1):
        return None
    inner = cond.args[0]
    if not (isinstance(inner, ApplyExpr) and inner.op == "LAnd" and len(inner.args) == 2):
        return None
    return inner.args[0], inner.args[1]


def _eq_zero_target(expr: TacExpr | None) -> SymbolRef | None:
    """If ``expr`` is ``Eq(X, 0)`` with X a SymbolRef, return X."""
    if expr is None:
        return None
    if not (isinstance(expr, ApplyExpr) and expr.op == "Eq" and len(expr.args) == 2):
        return None
    a, b = expr.args
    if isinstance(b, ConstExpr) and const_to_int(b) == 0 and isinstance(a, SymbolRef):
        return a
    if isinstance(a, ConstExpr) and const_to_int(a) == 0 and isinstance(b, SymbolRef):
        return b
    return None


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


def materialize_h_nonzero(
    program: TacProgram,
    *,
    symbol_sorts: dict[str, str] | None = None,
) -> MaterializeHNonzeroResult:
    """Walk every block; for each ``assume LNot(LAnd(B_lo, B_hi))``
    over chunks of the same H, insert ``assume Ge(H, 1)``
    immediately after."""
    ctx = RewriteCtx(program, symbol_sorts=symbol_sorts or {})

    insertions: dict[tuple[str, int], list[TacCmd]] = {}
    hits = 0

    for block in program.blocks:
        existing_assume_conds = {
            c.condition
            for c in block.commands
            if isinstance(c, AssumeExpCmd)
        }
        for idx, cmd in enumerate(block.commands):
            if not isinstance(cmd, AssumeExpCmd):
                continue
            m = _match_lnot_land(cmd.condition)
            if m is None:
                continue
            b_lo, b_hi = m
            if not (isinstance(b_lo, SymbolRef) and isinstance(b_hi, SymbolRef)):
                continue

            low_sym = _eq_zero_target(ctx.definition(b_lo.name))
            hi_sym = _eq_zero_target(ctx.definition(b_hi.name))
            if low_sym is None or hi_sym is None:
                continue

            h_from_low = _match_chunk_def(ctx.definition(low_sym.name), "Mod")
            h_from_hi = _match_chunk_def(ctx.definition(hi_sym.name), "Div")
            if h_from_low is None or h_from_hi is None:
                continue
            if canonical_symbol(h_from_low.name) != canonical_symbol(
                h_from_hi.name
            ):
                continue

            new_cond = ApplyExpr("Ge", (h_from_low, _ONE_BV))
            if new_cond in existing_assume_conds:
                continue
            insertions.setdefault((block.id, idx), []).append(
                canonicalize_cmd(AssumeExpCmd(raw="", condition=new_cond))
            )
            existing_assume_conds.add(new_cond)
            hits += 1

    if not insertions:
        return MaterializeHNonzeroResult(program=program, hits=0)

    new_blocks: list[TacBlock] = []
    for block in program.blocks:
        new_cmds: list[TacCmd] = []
        for idx, cmd in enumerate(block.commands):
            new_cmds.append(cmd)
            for q in insertions.get((block.id, idx), ()):
                new_cmds.append(q)
        new_blocks.append(replace(block, commands=new_cmds))
    return MaterializeHNonzeroResult(
        program=TacProgram(blocks=new_blocks), hits=hits
    )


__all__ = ["MaterializeHNonzeroResult", "materialize_h_nonzero"]
