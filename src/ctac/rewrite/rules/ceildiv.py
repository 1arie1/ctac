"""R6: recognize Solana's 256-bit ceiling-division chain and replace by algebraic bounds.

**Pattern** (after N2/N4 have canonicalized bit-ops; all SymbolRef refs peeled
via :meth:`RewriteCtx.lookthrough`)::

    rhs     = IntAdd(R_floor_ref, Ite(LAnd(Eq(X2, 0), Eq(X1, 0)), 0, 1))
    R_floor = IntDiv(R_num, R_den)                        # narrow optional
    R_prod  = IntMul(R_floor_ref, R_den)                  # narrow optional
    R_trunc = Mod(R_prod, 2^64)
    R_high  = Sub(0, Div(R_prod, 2^64))
    X1      = Sub(R_high, Ite(Lt(R_num, R_trunc), 1, 0))
    X2      = Sub(R_num, R_trunc)

The top-level RHS may also be wrapped in a ``safe_math_narrow_bv256`` call.

**Rewrite** (for ``R_den > 0``, emitted as ``placement='current'``)::

    AssignHavocCmd T                                     # fresh
    AssumeExpCmd Ge(IntMul(R_den, T), R_num)             # T >= ceil(R_num/R_den)
    AssumeExpCmd Lt(IntMul(R_den, T), IntAdd(R_num, R_den)) # T < ceil + 1
    AssumeExpCmd Ge(T, 0)                                # when R_num >= 0

The six intermediate vars (R_floor, R_prod, R_trunc, R_high, X1, X2) become
dead after CP + DCE.
"""

from __future__ import annotations

from ctac.analysis.symbols import canonical_symbol
from ctac.ast.nodes import ApplyExpr, AssignExpCmd, ConstExpr, SymbolRef, TacExpr
from ctac.rewrite.context import RewriteCtx, _is_safe_narrow_apply
from ctac.rewrite.framework import Rule
from ctac.rewrite.range_infer import infer_expr_range
from ctac.rewrite.rules.common import const_to_int
from ctac.rewrite.rules.div_purify import _all_refs_static

_POW2_64 = 1 << 64
_ZERO_INT = ConstExpr("0x0(int)")


def _canonical_expr(expr: TacExpr) -> TacExpr:
    """Strip DSA version suffixes (``:N``) from all SymbolRef names recursively.

    Used for structural equality of references that may carry different
    meta-suffixes in the TAC source but denote the same symbol.
    """
    if isinstance(expr, SymbolRef):
        return SymbolRef(canonical_symbol(expr.name))
    if isinstance(expr, ApplyExpr):
        return ApplyExpr(expr.op, tuple(_canonical_expr(a) for a in expr.args))
    return expr


def _eq_modulo_meta(a: TacExpr, b: TacExpr) -> bool:
    return _canonical_expr(a) == _canonical_expr(b)


def _peel_narrow(expr: TacExpr) -> TacExpr:
    """Strip one outer ``safe_math_narrow_bv256`` Apply wrapper (if any)."""
    if _is_safe_narrow_apply(expr):
        assert isinstance(expr, ApplyExpr)
        return expr.args[1]
    return expr


def _const_eq(expr: TacExpr, value: int) -> bool:
    return isinstance(expr, ConstExpr) and const_to_int(expr) == value


def _match_ite(
    expr: TacExpr, *, then_val: int | None = None, else_val: int | None = None
) -> tuple[TacExpr, TacExpr, TacExpr] | None:
    if not (isinstance(expr, ApplyExpr) and expr.op == "Ite" and len(expr.args) == 3):
        return None
    cond, t, e = expr.args
    if then_val is not None and not _const_eq(t, then_val):
        return None
    if else_val is not None and not _const_eq(e, else_val):
        return None
    return cond, t, e


def _match_zero_zero_conj(cond: TacExpr) -> tuple[TacExpr, TacExpr] | None:
    """Match ``LAnd(Eq(X2, 0), Eq(X1, 0))`` (either arg order inside each Eq)."""
    if not (isinstance(cond, ApplyExpr) and cond.op == "LAnd" and len(cond.args) == 2):
        return None

    def _extract_eq_zero(e: TacExpr) -> TacExpr | None:
        if not (isinstance(e, ApplyExpr) and e.op == "Eq" and len(e.args) == 2):
            return None
        a, b = e.args
        if _const_eq(b, 0):
            return a
        if _const_eq(a, 0):
            return b
        return None

    a = _extract_eq_zero(cond.args[0])
    b = _extract_eq_zero(cond.args[1])
    if a is None or b is None:
        return None
    # Return (X2, X1) in the order (first arg = X2, second arg = X1) — matches the
    # plan's naming (X2 covers the remainder, X1 the sign-extended correction).
    return a, b


def _rewrite_r6(expr: TacExpr, ctx: RewriteCtx) -> TacExpr | None:
    # R6 fires only at the top-level RHS of an `AssignExpCmd` so the host LHS
    # (e.g. R164) can be reused as the new havoc name. Sub-expression matches
    # would mean the ceiling value is embedded deeper — not the pattern we
    # want to collapse.
    host = ctx.current_cmd()
    if not (ctx.at_cmd_top() and isinstance(host, AssignExpCmd)):
        return None
    # Outer: optional narrow wrapper around IntAdd(R_floor_ref, Ite(...))
    outer = _peel_narrow(expr)
    if not (isinstance(outer, ApplyExpr) and outer.op == "IntAdd" and len(outer.args) == 2):
        return None
    r_floor_ref, ite_01 = outer.args
    ite_match = _match_ite(ite_01, then_val=0, else_val=1)
    if ite_match is None:
        return None
    zero_check, _, _ = ite_match
    zz = _match_zero_zero_conj(zero_check)
    if zz is None:
        return None
    x2_ref, x1_ref = zz

    # Resolve R_floor via lookthrough -> IntDiv(R_num, R_den) (or Div)
    floor = ctx.lookthrough(r_floor_ref)
    if not (isinstance(floor, ApplyExpr) and floor.op in {"IntDiv", "Div"} and len(floor.args) == 2):
        return None
    r_num, r_den = floor.args

    # X2 = Sub(R_num, R_trunc)
    x2 = ctx.lookthrough(x2_ref)
    if not (isinstance(x2, ApplyExpr) and x2.op == "Sub" and len(x2.args) == 2):
        return None
    x2_num, x2_trunc_ref = x2.args

    # X1 = Sub(R_high, Ite(Lt(R_num, R_trunc), 1, 0))
    x1 = ctx.lookthrough(x1_ref)
    if not (isinstance(x1, ApplyExpr) and x1.op == "Sub" and len(x1.args) == 2):
        return None
    r_high_ref, sign_ite = x1.args
    sign_match = _match_ite(sign_ite, then_val=1, else_val=0)
    if sign_match is None:
        return None
    lt_cond, _, _ = sign_match
    if not (isinstance(lt_cond, ApplyExpr) and lt_cond.op == "Lt" and len(lt_cond.args) == 2):
        return None
    lt_num, lt_trunc_ref = lt_cond.args

    # R_high = Sub(0, Div(R_prod, 2^64))
    r_high = ctx.lookthrough(r_high_ref)
    if not (isinstance(r_high, ApplyExpr) and r_high.op == "Sub" and len(r_high.args) == 2):
        return None
    high_zero, high_div = r_high.args
    if not _const_eq(high_zero, 0):
        return None
    if not (isinstance(high_div, ApplyExpr) and high_div.op == "Div" and len(high_div.args) == 2):
        return None
    prod_ref_from_high, high_div_divisor = high_div.args
    if const_to_int(high_div_divisor) != _POW2_64:
        return None

    # R_trunc = Mod(R_prod, 2^64) — must match on both X1 and X2 sides
    trunc_x2 = ctx.lookthrough(x2_trunc_ref)
    trunc_x1 = ctx.lookthrough(lt_trunc_ref)
    if not (
        isinstance(trunc_x2, ApplyExpr)
        and trunc_x2.op == "Mod"
        and len(trunc_x2.args) == 2
    ):
        return None
    if not _eq_modulo_meta(trunc_x1, trunc_x2):
        return None
    prod_ref_from_trunc, trunc_mod_divisor = trunc_x2.args
    if const_to_int(trunc_mod_divisor) != _POW2_64:
        return None

    # Cross-check that R_prod references from the high-bits and trunc paths match.
    prod_high = ctx.lookthrough(prod_ref_from_high)
    prod_trunc = ctx.lookthrough(prod_ref_from_trunc)
    if not _eq_modulo_meta(prod_high, prod_trunc):
        return None
    # R_prod should be IntMul(R_floor_ref, R_den) (narrow already peeled by lookthrough).
    if not (
        isinstance(prod_high, ApplyExpr)
        and prod_high.op == "IntMul"
        and len(prod_high.args) == 2
    ):
        return None
    prod_floor_ref, prod_den_ref = prod_high.args

    # R_prod's floor matches the outer floor; its den matches R_den.
    if not _eq_modulo_meta(ctx.lookthrough(prod_floor_ref), floor):
        return None
    if not _eq_modulo_meta(ctx.lookthrough(prod_den_ref), ctx.lookthrough(r_den)):
        return None

    # R_num references throughout must agree (compare looked-through forms to
    # tolerate reference aliasing, but keep r_num / r_den in their original
    # form — typically SymbolRefs — so we can query direct range assumes and
    # emit cleaner assumes).
    r_num_peeled = ctx.lookthrough(r_num)
    if not _eq_modulo_meta(ctx.lookthrough(x2_num), r_num_peeled):
        return None
    if not _eq_modulo_meta(ctx.lookthrough(lt_num), r_num_peeled):
        return None

    # Precondition: R_den > 0. Try the pre-lookthrough form first (so direct
    # assumes like `R_den in [1, k]` are picked up) and fall back to the
    # expanded form.
    if not (_all_refs_static(r_num, ctx) and _all_refs_static(r_den, ctx)):
        return None
    den_range = infer_expr_range(r_den, ctx)
    if den_range is None:
        den_range = infer_expr_range(ctx.lookthrough(r_den), ctx)
    if den_range is None or den_range[0] <= 0:
        return None

    num_range = infer_expr_range(r_num, ctx)
    if num_range is None:
        num_range = infer_expr_range(r_num_peeled, ctx)
    num_non_negative = num_range is not None and num_range[0] >= 0

    def build_assumes(t: SymbolRef) -> list[TacExpr]:
        den_times_t = ApplyExpr("IntMul", (r_den, t))
        conds: list[TacExpr] = [
            ApplyExpr("Ge", (den_times_t, r_num)),
            ApplyExpr(
                "Lt",
                (den_times_t, ApplyExpr("IntAdd", (r_num, r_den))),
            ),
        ]
        if num_non_negative:
            conds.append(ApplyExpr("Ge", (t, _ZERO_INT)))
        return conds

    # Reuse the host AssignExpCmd's LHS as the havoc name; drop the original
    # chain-final assignment. The 6 intermediates (R_floor .. X2) become dead
    # once R_ceil no longer references them and DCE sweeps them up.
    result = ctx.emit_fresh_var(
        assumes_fn=build_assumes,
        sort="int",
        placement="current",
        reuse_name=host.lhs,
    )
    ctx.skip_current_cmd()
    return result


R6_CEILDIV = Rule(
    name="R6",
    fn=_rewrite_r6,
    description="Collapse the 256-bit ceiling-division chain into polynomial bounds on a fresh var.",
)
