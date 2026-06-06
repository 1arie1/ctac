"""Drop ``AssumeExpCmd`` commands whose condition is already
range-derivable from the surrounding context.

Pattern: ``assume Cmp(E, K)`` where ``K`` is a concrete constant
and ``infer_expr_range(E)`` proves the comparison is a tautology
(e.g. ``Le(E, K)`` with E's upper bound ≤ K). The assume carries
no information the range analysis can't reconstruct.

Motivating use: the ``rewrite_u128_carry_add`` pass materializes
explicit bounds on the partial sum (R_lo + R_b) and the BASE so
H's bound is locally provable. After downstream lifts collapse the
chunked encoding (chunk-merge + muldiv-to-V-Div), the intermediate
chunks (R_lo, BASE) become dead from the computation perspective
but stay alive via their bound assumes. Dropping the redundant
assumes lets DCE clear them.

Soundness: a tautological assume is by definition a no-op — it
adds no constraint to the program's feasible set. Dropping it
preserves semantics. rw-eq's rule-4b CHK is the assume's
condition, which discharges from the same range analysis the pass
used.

Range gates (per assume):

* ``Le(E, K)``: drop when ``hi(E) <= K``.
* ``Lt(E, K)``: drop when ``hi(E) < K``.
* ``Ge(E, K)``: drop when ``lo(E) >= K``.
* ``Gt(E, K)``: drop when ``lo(E) > K``.
* Symmetric ``Cmp(K, E)`` forms apply with operand order flipped.
* Otherwise: keep the assume.

Concrete-K only: a symbolic K would need a relational analysis
that ``infer_expr_range`` doesn't provide; conservatively skip.

Idempotent: a program with no range-redundant assumes is a no-op.
"""

from __future__ import annotations

from dataclasses import dataclass, replace

from ctac.ast.nodes import (
    ApplyExpr,
    AssumeExpCmd,
    ConstExpr,
    TacCmd,
    TacExpr,
)
from ctac.ir.models import TacBlock, TacProgram
from ctac.rewrite.context import RewriteCtx
from ctac.rewrite.range_infer import infer_expr_range
from ctac.rewrite.rules.common import const_to_int


@dataclass(frozen=True)
class DropRangeRedundantAssumesResult:
    """Outcome of :func:`drop_range_redundant_assumes`."""

    program: TacProgram
    hits: int


_CMP_OPS = frozenset({"Le", "Lt", "Ge", "Gt"})
_FLIPPED = {"Le": "Ge", "Lt": "Gt", "Ge": "Le", "Gt": "Lt"}


def _classify_cmp(
    cond: TacExpr,
) -> tuple[str, TacExpr, int] | None:
    """If ``cond`` is ``Cmp(E, K)`` or ``Cmp(K, E)`` with K a
    constant and the comparison in the set we handle, return
    ``(normalized_op, E, K)`` where ``normalized_op`` is the op as
    if E is the left operand."""
    if not (
        isinstance(cond, ApplyExpr)
        and cond.op in _CMP_OPS
        and len(cond.args) == 2
    ):
        return None
    a, b = cond.args
    b_v = const_to_int(b)
    if b_v is not None and not isinstance(a, ConstExpr):
        return cond.op, a, b_v
    a_v = const_to_int(a)
    if a_v is not None and not isinstance(b, ConstExpr):
        # Flip to put E on the left.
        return _FLIPPED[cond.op], b, a_v
    return None


def _is_tautology(op: str, lo: int | None, hi: int | None, k: int) -> bool:
    """``op`` is normalized to ``Cmp(E, K)``. Return True if E's
    range ``[lo, hi]`` makes the comparison trivially true."""
    if op == "Le":
        return hi is not None and hi <= k
    if op == "Lt":
        return hi is not None and hi < k
    if op == "Ge":
        return lo is not None and lo >= k
    if op == "Gt":
        return lo is not None and lo > k
    return False


def drop_range_redundant_assumes(
    program: TacProgram,
    *,
    symbol_sorts: dict[str, str] | None = None,
) -> DropRangeRedundantAssumesResult:
    """Walk every ``AssumeExpCmd``; drop those whose condition is
    a literal ``true`` (the degenerate tautology, typically left by
    ``EqReflexive`` / ``ArithConstFold`` folding the condition) or a
    range-tautological comparison against a constant."""
    ctx = RewriteCtx(program, symbol_sorts=symbol_sorts or {})

    drops: dict[str, set[int]] = {}
    hits = 0
    for block in program.blocks:
        for idx, cmd in enumerate(block.commands):
            if not isinstance(cmd, AssumeExpCmd):
                continue
            cond = cmd.condition
            if isinstance(cond, ConstExpr) and cond.value.strip() == "true":
                drops.setdefault(block.id, set()).add(idx)
                hits += 1
                continue
            classified = _classify_cmp(cmd.condition)
            if classified is None:
                continue
            op, e, k = classified
            ctx.set_position(block.id, idx)
            rng = infer_expr_range(e, ctx)
            if rng is None:
                continue
            if not _is_tautology(op, rng[0], rng[1], k):
                continue
            drops.setdefault(block.id, set()).add(idx)
            hits += 1

    if not drops:
        return DropRangeRedundantAssumesResult(program=program, hits=0)

    new_blocks: list[TacBlock] = []
    for block in program.blocks:
        block_drops = drops.get(block.id, set())
        if not block_drops:
            new_blocks.append(block)
            continue
        new_cmds: list[TacCmd] = [
            cmd
            for idx, cmd in enumerate(block.commands)
            if idx not in block_drops
        ]
        new_blocks.append(replace(block, commands=new_cmds))
    return DropRangeRedundantAssumesResult(
        program=TacProgram(blocks=new_blocks), hits=hits
    )


__all__ = [
    "DropRangeRedundantAssumesResult",
    "drop_range_redundant_assumes",
]
