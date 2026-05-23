"""Narrow copy / constant propagation.

CP: when a ``SymbolRef`` X has all defining RHSes equal to the same
``SymbolRef`` Y or ``ConstExpr`` c, rewrite X to Y or c at its use
sites. Two cases:

* **Static**: X has a unique ``AssignExpCmd`` def whose RHS is a
  SymRef/Const. The dominant one — R1-induced aliases (``R35 = R34``),
  constant defs from CFG-edit specialize / chain recognition /
  RangeFold's compound-only folding, etc.
* **Convergent dynamic**: X is DSA-dynamic with multiple defs that
  all share the same SymRef/Const RHS. Emerges after passes that
  hoist a common value before a branch and leave both branch defs as
  aliases of the hoisted name (see ``hoist_path_invariant_defs``);
  CP then propagates to use sites and DCE clears the dynamic defs.

Soundness:

* Static SymRef -> Y: Y dominates X's def (it was X's RHS); X's def
  dominates every use of X.
* Static SymRef -> ConstExpr: constants are universally available.
* Convergent dynamic same-RHS: at any use of X the value reaches from
  one of the defs; if every def writes the same value Y, X equals Y
  at every use. Each def's site already had Y available (Y is its
  RHS), and the use's join point is dominated by all defs, so Y
  reaches the use.

Snapshot-safety: this rule mutates RHSes of expressions it touches, so
must run in a phase that does not also contain CSE (whose RHS index
is taken once per iteration). The driver pipeline already isolates
CSE in its own phase; CP_ALIAS lives in ``simplify_pipeline``.
"""

from __future__ import annotations

from ctac.analysis.symbols import canonical_symbol
from ctac.ast.nodes import ApplyExpr, ConstExpr, SymbolRef, TacExpr
from ctac.rewrite.context import RewriteCtx
from ctac.rewrite.framework import Rule


def _canonical(expr: TacExpr) -> TacExpr:
    """DSA-suffix-stripped canonical form for structural equality."""
    if isinstance(expr, SymbolRef):
        return SymbolRef(canonical_symbol(expr.name))
    if isinstance(expr, ApplyExpr):
        return ApplyExpr(expr.op, tuple(_canonical(a) for a in expr.args))
    return expr


def _rewrite_cp(expr: TacExpr, ctx: RewriteCtx) -> TacExpr | None:
    if not isinstance(expr, SymbolRef):
        return None
    # Static case (the dominant one): unique def with SymRef/Const RHS.
    d = ctx.definition(expr.name)
    if isinstance(d, (SymbolRef, ConstExpr)):
        return d
    # Convergent dynamic case: all defs share the same SymRef/Const RHS.
    rhss = ctx.def_rhs_expressions(expr.name)
    if rhss is None or len(rhss) < 2:
        return None
    first = rhss[0]
    if not isinstance(first, (SymbolRef, ConstExpr)):
        return None
    first_canon = _canonical(first)
    for r in rhss[1:]:
        if _canonical(r) != first_canon:
            return None
    return first


CP_ALIAS = Rule(
    name="CP",
    fn=_rewrite_cp,
    description=(
        "Copy / constant propagation: replace SymbolRef X with its "
        "unique definition's RHS when that RHS is a SymbolRef or a "
        "ConstExpr."
    ),
)
