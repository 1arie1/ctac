"""R4a: div purification for non-constant divisors.

Replace ``Div(A, B)`` (or ``IntDiv(A, B)``) with a havoc'd variable
constrained by the two-sided Euclidean bound::

    B * X <= A
    A < B * (X + 1)

(plus ``X >= 0`` when ``A`` is known non-negative).

**Scope:** fires only when ``B`` is a *non-constant* expression with a
positive lower bound (via :func:`infer_expr_range`), and only at the top
of an :class:`AssignExpCmd`'s RHS — i.e. for commands of the form
``AssignExpCmd X Div(A, B)``. The host command's LHS ``X`` is reused as
the new havoc's name; the original ``AssignExpCmd`` is dropped and
replaced by ``AssignHavocCmd X`` followed by the boundary assumes.
Both ``Div`` and ``IntDiv`` are accepted; emitted arithmetic always uses
``IntMul`` / ``IntAdd`` with ``(int)``-tagged constants (Int-domain →
no bv-modular overflow).

**Safety:** the new havoc + assumes are inserted just before the command
currently being rewritten. Any ``SymbolRef`` reachable in ``A`` / ``B``
(after ``ctx.lookthrough``) must be DSA-static so its unique definition
dominates the rewrite position — sufficient to make the new assumes
use-after-def at the insertion point.
"""

from __future__ import annotations

from ctac.ast.nodes import ApplyExpr, AssignExpCmd, ConstExpr, SymbolRef, TacExpr
from ctac.rewrite.context import RewriteCtx, _is_safe_narrow_apply
from ctac.rewrite.framework import Rule
from ctac.rewrite.range_infer import infer_expr_range
from ctac.rewrite.rules.common import DIV_OPS, const_to_int


_ONE_INT = ConstExpr("0x1(int)")
_ZERO_INT = ConstExpr("0x0(int)")


def _all_refs_static(expr: TacExpr, ctx: RewriteCtx) -> bool:
    """True iff every data :class:`SymbolRef` in ``expr`` is DSA-static.

    ``Apply(safe_math_narrow_bvN:bif, E)`` only recurses into ``E`` — the
    function-symbol first argument is a builtin identifier, not a data ref.
    """
    if isinstance(expr, ConstExpr):
        return True
    if isinstance(expr, SymbolRef):
        return ctx.is_static(expr.name)
    if isinstance(expr, ApplyExpr):
        if _is_safe_narrow_apply(expr):
            return _all_refs_static(expr.args[1], ctx)
        return all(_all_refs_static(a, ctx) for a in expr.args)
    return False


def _rewrite_r4a(expr: TacExpr, ctx: RewriteCtx) -> TacExpr | None:
    # Fires only at the top-level RHS of `AssignExpCmd X Div(A, B)` so the
    # host LHS X can be reused as the new havoc name.
    host = ctx.current_cmd()
    if not (ctx.at_cmd_top() and isinstance(host, AssignExpCmd)):
        return None
    if not (isinstance(expr, ApplyExpr) and expr.op in DIV_OPS and len(expr.args) == 2):
        return None
    a, b = expr.args
    # Constant-divisor cases belong to R2 / R3 / R4; R4a focuses on the
    # non-constant-divisor case that those rules cannot handle.
    if const_to_int(b) is not None:
        return None
    b_range = infer_expr_range(b, ctx)
    if b_range is None or b_range[0] <= 0:
        return None
    a_use = ctx.lookthrough(a)
    b_use = ctx.lookthrough(b)
    if not (_all_refs_static(a_use, ctx) and _all_refs_static(b_use, ctx)):
        return None

    a_range = infer_expr_range(a_use, ctx)
    a_non_negative = a_range is not None and a_range[0] >= 0

    def build_assumes(t: SymbolRef) -> list[TacExpr]:
        bx = ApplyExpr("IntMul", (b_use, t))
        b_xplus1 = ApplyExpr("IntMul", (b_use, ApplyExpr("IntAdd", (t, _ONE_INT))))
        conds: list[TacExpr] = [
            ApplyExpr("Le", (bx, a_use)),
            ApplyExpr("Lt", (a_use, b_xplus1)),
        ]
        if a_non_negative:
            conds.append(ApplyExpr("Ge", (t, _ZERO_INT)))
        return conds

    # Reuse X as the havoc name; drop the original `X = Div(...)` command.
    result = ctx.emit_fresh_var(
        assumes_fn=build_assumes,
        sort="int",
        placement="current",
        reuse_name=host.lhs,
    )
    ctx.skip_current_cmd()
    return result


R4A_DIV_PURIFY = Rule(
    name="R4a",
    fn=_rewrite_r4a,
    description="Purify Div(A, B) with non-constant positive-range B into a fresh var with two-sided bounds.",
)
