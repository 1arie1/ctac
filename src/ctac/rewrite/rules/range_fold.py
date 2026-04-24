"""Fold expressions to constants when interval inference pins them.

When ``infer_expr_range(expr)`` returns a singleton ``(v, v)``, the
expression evaluates to ``v`` in every reachable execution regardless
of shape. Replacing it with ``ConstExpr(v)`` is semantics-preserving
and unlocks downstream constant-folding, CP, and DCE.

Typical triggers:

- ``Sub(X, Y)`` where a dominating ``assume Eq(X, Y)`` gives
  ``ctx.diff_bounds(X, Y) = (0, 0)`` — the sub folds to ``0``.
- ``IntMul(X, ConstExpr("0x0"))`` — product range is ``(0, 0)``.
- ``Mod(X, K)`` where ``X`` is pinned — mod reduces to the dividend
  (range tightened in ``range_infer`` for this case).
- Any composition thereof, via the fixed-point driver.

The rule skips ``ConstExpr`` inputs (nothing to fold) and ``SymbolRef``
inputs (they alias a named value — let CP_ALIAS / DCE handle the
cleanup so we preserve symbolic names).
"""

from __future__ import annotations

from ctac.ast.nodes import ApplyExpr, ConstExpr, TacExpr
from ctac.rewrite.context import RewriteCtx
from ctac.rewrite.framework import Rule
from ctac.rewrite.range_infer import infer_expr_range


def _rewrite_range_fold(expr: TacExpr, ctx: RewriteCtx) -> TacExpr | None:
    # Only fold compound expressions; constants are already folded and
    # symbols alias a value that downstream CP can propagate on its own.
    if not isinstance(expr, ApplyExpr):
        return None
    r = infer_expr_range(expr, ctx)
    if r is None:
        return None
    lo, hi = r
    if lo != hi:
        return None
    # Emit the constant in hex for consistency with other rule outputs.
    if lo < 0:
        return None
    return ConstExpr(f"0x{lo:x}")


RANGE_FOLD = Rule(
    name="RangeFold",
    fn=_rewrite_range_fold,
    description=(
        "Fold an ApplyExpr to ConstExpr when infer_expr_range returns a "
        "non-negative singleton. Generalizes Sub(X, X) -> 0 and similar "
        "identities via interval inference."
    ),
)
