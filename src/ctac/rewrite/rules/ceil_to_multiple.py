"""Recognize the SBF-chunked "ceil to multiple of K" idiom and lift it
to ``IntMul(K, IntCeilDiv(V, K))``.

Pattern (the second-stage chunked ceil-div emitted by Solana's
``CertoraFixed::ceil`` builtin — see the
``shares_to_burn_consistency`` benchmark for the full context, and
``journal/2026-05/2026-05-22-u128-lift-ceildiv-input-shape.md`` in
ctac-research for the upstream u128 lift that produces V)::

    R_floor_mul = IntMul(Div(V, K), K)                # or IntMul(K, Div(...)), commutative
    M_plus      = Apply(safe_math_narrow_bv256:bif, IntAdd(K, R_floor_mul))
    Cm          = Mod(M_plus, 2^64)                   # bv256 % bv-64
    R_rem       = Mod(V, K)
    B           = Eq(R_rem, 0)
    assume LOr(B, Le(M_plus, 2^64-1))                 # wrap-guard, load-bearing
    R_X         = Ite(B, R_floor_mul, Cm)             # HOST cmd

Rewrite (when the wrap-guard assume is in scope before the host)::

    R_X = Apply(safe_math_narrow_bv256:bif, IntMul(K, IntCeilDiv(V, K)))

The six chain intermediates (R_floor_mul, M_plus, Cm, R_rem, B + the
disjunctive assume itself) become dead after CP + DCE.

Soundness (the load on rw-eq's rule-2 same-lhs CHK):

- B-arm (V mod K == 0): R_X = R_floor_mul = (V/K)*K = V. And
  K*IntCeilDiv(V,K) = K*(V/K) = V when V mod K == 0. Equal.

- not-B-arm (V mod K >= 1): the disjunctive assume forces
  M_plus <= 2^64-1, so Cm = M_plus % 2^64 = M_plus, and
  M_plus = K + (V/K)*K = K*(V/K + 1) = K*IntCeilDiv(V, K). Equal.

The wrap-guard is the only non-structural soundness requirement; the
rule abstains if it isn't present as a prior ``LOr(B_ref, Le(M_plus_ref,
2^64-1))`` assume in the host's block. rw-eq verifies the equivalence
on the program's actual assume context as belt-and-suspenders.
"""

from __future__ import annotations

from ctac.analysis.symbols import canonical_symbol
from ctac.ast.nodes import (
    ApplyExpr,
    AssignExpCmd,
    AssumeExpCmd,
    ConstExpr,
    SymbolRef,
    TacExpr,
)
from ctac.rewrite.context import RewriteCtx, _is_safe_narrow_apply
from ctac.rewrite.framework import Rule
from ctac.rewrite.rules.common import DIV_OPS, MOD_OPS, MUL_OPS, const_to_int

_POW2_64 = 1 << 64
_BV64_MAX = _POW2_64 - 1


def _canonical_expr(expr: TacExpr) -> TacExpr:
    """Strip DSA version suffixes from every SymbolRef recursively."""
    if isinstance(expr, SymbolRef):
        return SymbolRef(canonical_symbol(expr.name))
    if isinstance(expr, ApplyExpr):
        return ApplyExpr(expr.op, tuple(_canonical_expr(a) for a in expr.args))
    return expr


def _eq_modulo_meta(a: TacExpr, b: TacExpr) -> bool:
    return _canonical_expr(a) == _canonical_expr(b)


def _const_eq(expr: TacExpr, value: int) -> bool:
    return isinstance(expr, ConstExpr) and const_to_int(expr) == value


def _peel_narrow(expr: TacExpr) -> TacExpr:
    if _is_safe_narrow_apply(expr):
        assert isinstance(expr, ApplyExpr)
        return expr.args[1]
    return expr


def _match_mod_with_const(
    expr: TacExpr, ctx: RewriteCtx
) -> tuple[TacExpr, int] | None:
    """``Mod(X, K_const)`` -> ``(X, K)`` after one lookthrough."""
    e = ctx.lookthrough(expr)
    if not (isinstance(e, ApplyExpr) and e.op in MOD_OPS and len(e.args) == 2):
        return None
    x, k_expr = e.args
    k = const_to_int(k_expr)
    if k is None or k <= 0:
        return None
    return x, k


def _match_floor_mul_k(
    expr: TacExpr, want_k: int, ctx: RewriteCtx
) -> TacExpr | None:
    """``IntMul(Div(V, K), K)`` (commutative) -> V (the SymbolRef or sub-expr)."""
    e = ctx.lookthrough(expr)
    if not (isinstance(e, ApplyExpr) and e.op in MUL_OPS and len(e.args) == 2):
        return None
    a, b = e.args
    # Identify (Div(...), K_const) — either arg order.
    if const_to_int(b) == want_k:
        div_side = a
    elif const_to_int(a) == want_k:
        div_side = b
    else:
        return None
    div = ctx.lookthrough(div_side)
    if not (isinstance(div, ApplyExpr) and div.op in DIV_OPS and len(div.args) == 2):
        return None
    v_inner, k_inner = div.args
    if const_to_int(k_inner) != want_k:
        return None
    return v_inner


def _resolve_eq_rem_ref(cond: TacExpr, ctx: RewriteCtx) -> TacExpr | None:
    """``cond`` is the Ite's condition; resolve it to ``Eq(R_rem, 0)`` and
    return ``R_rem``. Accepts:
      - inline ``Eq(R_rem, 0)`` / ``Eq(0, R_rem)``;
      - ``SymbolRef`` whose static def is one of the above.
    """
    e = ctx.lookthrough(cond) if isinstance(cond, SymbolRef) else cond
    if not (isinstance(e, ApplyExpr) and e.op == "Eq" and len(e.args) == 2):
        return None
    a, c = e.args
    if _const_eq(c, 0):
        return a
    if _const_eq(a, 0):
        return c
    return None


def _match_disjunctive_wrap_guard(
    cond: TacExpr,
    rem_ref_canon: TacExpr,
    m_plus_ref: TacExpr,
    ctx: RewriteCtx,
) -> bool:
    """Does ``cond`` have the shape ``LOr(B, Le(M_plus, 2^64-1))``?

    ``B`` is checked by resolving its underlying ``Eq(R_rem, 0)`` and
    comparing ``R_rem`` to ``rem_ref_canon`` (canonical). ``M_plus`` is
    compared modulo DSA suffix to ``m_plus_ref``.
    """
    if not (isinstance(cond, ApplyExpr) and cond.op == "LOr" and len(cond.args) == 2):
        return False
    for lhs, rhs in (cond.args, (cond.args[1], cond.args[0])):
        b_rem = _resolve_eq_rem_ref(lhs, ctx)
        if b_rem is None or not _eq_modulo_meta(b_rem, rem_ref_canon):
            continue
        if not (isinstance(rhs, ApplyExpr) and rhs.op == "Le" and len(rhs.args) == 2):
            continue
        target_ref, upper = rhs.args
        if const_to_int(upper) != _BV64_MAX:
            continue
        if _eq_modulo_meta(target_ref, m_plus_ref):
            return True
    return False


def _rewrite_ceil_to_multiple(expr: TacExpr, ctx: RewriteCtx) -> TacExpr | None:
    # Fire only at the top-level RHS of an AssignExpCmd — the rule replaces
    # the host's RHS, and the ladder intermediates become dead via DCE.
    host = ctx.current_cmd()
    if not (ctx.at_cmd_top() and isinstance(host, AssignExpCmd)):
        return None
    if not (isinstance(expr, ApplyExpr) and expr.op == "Ite" and len(expr.args) == 3):
        return None
    cond, then_arm, else_arm = expr.args

    # Resolve the cond to ``Eq(R_rem, 0)`` and extract ``R_rem``. Accepts
    # inline Eq (pre-ITE_PURIFY) or SymbolRef to an Eq def (post-purify).
    rem_ref = _resolve_eq_rem_ref(cond, ctx)
    if rem_ref is None:
        return None

    # R_rem = Mod(V, K)
    rem_match = _match_mod_with_const(rem_ref, ctx)
    if rem_match is None:
        return None
    v_from_rem, k = rem_match

    # then-arm = IntMul(Div(V, K), K) (any order). Compare V to V_from_rem.
    v_from_floor = _match_floor_mul_k(then_arm, k, ctx)
    if v_from_floor is None:
        return None
    if not _eq_modulo_meta(v_from_rem, v_from_floor):
        return None

    # else-arm = Mod(M_plus, 2^64)
    else_match = _match_mod_with_const(else_arm, ctx)
    if else_match is None:
        return None
    m_plus_ref, wrap_size = else_match
    if wrap_size != _POW2_64:
        return None

    # M_plus = narrow(IntAdd(K, R_floor_mul)) -- the narrow may or may
    # not be present syntactically; peel it if so.
    m_plus_def = _peel_narrow(ctx.lookthrough(m_plus_ref))
    if not (
        isinstance(m_plus_def, ApplyExpr)
        and m_plus_def.op == "IntAdd"
        and len(m_plus_def.args) == 2
    ):
        return None
    add_l, add_r = m_plus_def.args
    if const_to_int(add_l) == k:
        m_plus_addend = add_r
    elif const_to_int(add_r) == k:
        m_plus_addend = add_l
    else:
        return None
    # The addend must be the same IntMul(Div(V, K), K) shape as the
    # then-arm — either via SymRef alias to the same def, or structurally
    # equivalent inline.
    v_from_addend = _match_floor_mul_k(m_plus_addend, k, ctx)
    if v_from_addend is None or not _eq_modulo_meta(v_from_addend, v_from_rem):
        return None

    # Scan the host's block backward for the disjunctive wrap-guard assume.
    if ctx._cur_block is None or ctx._cur_cmd is None:
        return None
    block = ctx.program.block_by_id().get(ctx._cur_block)
    if block is None:
        return None
    have_guard = False
    for prev in block.commands[: ctx._cur_cmd]:
        if not isinstance(prev, AssumeExpCmd):
            continue
        if _match_disjunctive_wrap_guard(prev.condition, rem_ref, m_plus_ref, ctx):
            # NB: we compare the assume's B-side via its underlying ``R_rem``
            # (the operand of the Eq), not via the cond expression — the
            # source TAC has the Ite cond inlined and the assume's B as a
            # SymRef to the same Eq def, but both Eqs share R_rem.
            have_guard = True
            break
    if not have_guard:
        return None

    # All checks passed — emit ``Apply(safe_math_narrow_bv256:bif,
    # IntMul(K, IntCeilDiv(V, K)))``. Preserves the host's bv256 sort;
    # the narrow is a no-op given K*ceil(V/K) <= V + K and V is bv256.
    k_const = ConstExpr(f"0x{k:x}(int)")
    return ApplyExpr(
        "Apply",
        (
            SymbolRef("safe_math_narrow_bv256:bif"),
            ApplyExpr(
                "IntMul",
                (
                    k_const,
                    ApplyExpr("IntCeilDiv", (v_from_rem, k_const)),
                ),
            ),
        ),
    )


CEIL_TO_MULTIPLE = Rule(
    name="CeilToMultiple",
    fn=_rewrite_ceil_to_multiple,
    description=(
        "Ite(Eq(V%K,0), (V/K)*K, narrow(K + (V/K)*K) % 2^64) -> "
        "K *int IntCeilDiv(V, K) (under the wrap-guard assume "
        "LOr(B, Le(M_plus, 2^64-1))). Collapses the SBF-chunked "
        "u64 ceil-to-multiple idiom to the IntCeilDiv concept."
    ),
)

__all__ = ["CEIL_TO_MULTIPLE"]
