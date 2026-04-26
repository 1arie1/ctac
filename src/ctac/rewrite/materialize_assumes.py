"""Selective ``assume`` materializer.

Surfaces facts that interval analysis already proves into explicit
TAC assume commands, so the SMT encoder doesn't have to re-derive
them at solve time. Strictly gated: every materialized assume comes
from :func:`infer_expr_range` returning a sufficient bound at the
relevant program point — nothing is invented.

Today the pass targets ``IntCeilDiv`` use sites, but it's structured
to grow. Adding a new axiomatized operator means appending a small
matcher / hint generator below; the framework around it stays the
same.

Pipeline placement: runs as the final phase of ``ctac rw``, after
all rewrites and DCE. This way:

- Range analysis sees the final post-rewrite program.
- Materialized assumes are validated end-to-end via ``ctac rw-eq``:
  each one becomes a rule-4 ``rhs-only-assume`` whose CHK must
  discharge under the orig program's existing constraints. If a
  materialized assume isn't implied by orig, rw-eq fails — the
  pass's gating bug would surface immediately.
"""

from __future__ import annotations

from dataclasses import dataclass, replace

from ctac.ast.nodes import (
    ApplyExpr,
    AssignExpCmd,
    AssumeExpCmd,
    ConstExpr,
    SymbolRef,
    TacCmd,
)
from ctac.ir.models import TacBlock, TacProgram
from ctac.rewrite.context import RewriteCtx
from ctac.rewrite.range_infer import infer_expr_range
from ctac.rewrite.unparse import canonicalize_cmd

_ZERO_INT = ConstExpr(value="0(int)")


@dataclass(frozen=True)
class MaterializeResult:
    """Outcome of :func:`materialize_assumes`.

    Attributes:
        program: program with assumes materialized.
        hits: per-kind counts (e.g.
            ``{"intceildiv_den_positive": 3, "intceildiv_lhs_nonneg": 2}``)
            so the rewriter's ``--report`` can summarize.
    """

    program: TacProgram
    hits: dict[str, int]


def materialize_assumes(
    program: TacProgram,
    *,
    symbol_sorts: dict[str, str] | None = None,
) -> MaterializeResult:
    """Walk ``program`` and materialize range-derived assumes around
    uses of axiomatized operators.

    Currently fires only on ``IntCeilDiv``. For each ``AssignExpCmd
    X = ... IntCeilDiv(a, b) ...`` (the IntCeilDiv may sit under
    ``Apply(safe_math_narrow_bv256:bif, ...)``, since R6's emission
    wraps it):

    - If interval analysis at the use site proves ``b > 0``,
      materialize ``assume Gt(b, 0)`` BEFORE the host.
    - If interval analysis on ``X``'s static definition proves
      ``X >= 0`` (which it does when ``a >= 0`` and ``b > 0``,
      via the IntCeilDiv range case in
      :mod:`ctac.rewrite.range_infer`), materialize
      ``assume Ge(X, 0)`` AFTER the host.

    Both bounds come strictly from :func:`infer_expr_range`. If the
    range query doesn't return a sufficient bound, no assume is
    materialized — the pass never invents a fact.

    Idempotent? No. Running twice produces duplicate assumes. Run
    once at the end of the rewrite pipeline.
    """
    ctx = RewriteCtx(program, symbol_sorts=symbol_sorts or {})

    insertions_before: dict[tuple[str, int], list[TacCmd]] = {}
    insertions_after: dict[tuple[str, int], list[TacCmd]] = {}
    hits: dict[str, int] = {}

    for block in program.blocks:
        for idx, cmd in enumerate(block.commands):
            if not isinstance(cmd, AssignExpCmd):
                continue
            inner = ctx.peel_narrow(cmd.rhs)
            if not (
                isinstance(inner, ApplyExpr)
                and inner.op == "IntCeilDiv"
                and len(inner.args) == 2
            ):
                continue
            a, b = inner.args
            ctx.set_position(block.id, idx)

            # Gate: ``b > 0`` must follow from interval analysis.
            den_range = infer_expr_range(b, ctx)
            if den_range is not None and den_range[0] > 0:
                insertions_before.setdefault((block.id, idx), []).append(
                    canonicalize_cmd(
                        AssumeExpCmd(
                            raw="",
                            condition=ApplyExpr("Gt", (b, _ZERO_INT)),
                        )
                    )
                )
                hits["intceildiv_den_positive"] = (
                    hits.get("intceildiv_den_positive", 0) + 1
                )

            # Gate: ``X >= 0`` must follow from interval analysis on X.
            # This routes through ctx.definition(X) → host's RHS, which
            # range_infer's IntCeilDiv case handles when ``a >= 0`` and
            # ``b > 0``. Sort fallback (bv256 → [0, 2^256-1]) also
            # applies, so for bv256-sorted X the bound is always
            # available; either way the source is interval analysis.
            lhs_range = infer_expr_range(SymbolRef(cmd.lhs), ctx)
            if lhs_range is not None and lhs_range[0] >= 0:
                insertions_after.setdefault((block.id, idx), []).append(
                    canonicalize_cmd(
                        AssumeExpCmd(
                            raw="",
                            condition=ApplyExpr(
                                "Ge", (SymbolRef(cmd.lhs), _ZERO_INT)
                            ),
                        )
                    )
                )
                hits["intceildiv_lhs_nonneg"] = (
                    hits.get("intceildiv_lhs_nonneg", 0) + 1
                )

    if not insertions_before and not insertions_after:
        return MaterializeResult(program=program, hits=hits)

    new_blocks: list[TacBlock] = []
    for block in program.blocks:
        new_cmds: list[TacCmd] = []
        for idx, cmd in enumerate(block.commands):
            for q in insertions_before.get((block.id, idx), ()):
                new_cmds.append(q)
            new_cmds.append(cmd)
            for q in insertions_after.get((block.id, idx), ()):
                new_cmds.append(q)
        new_blocks.append(replace(block, commands=new_cmds))
    return MaterializeResult(program=TacProgram(blocks=new_blocks), hits=hits)


__all__ = ["MaterializeResult", "materialize_assumes"]
