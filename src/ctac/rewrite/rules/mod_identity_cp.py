"""``Mod(X, M) -> X`` identity, both inline and SymRef-via-def.

Fires at any expression position when:

* ``Mod(X, M)`` appears inline AND ``infer_expr_range(X) ⊆ [0, M-1]``.
* A ``SymRef R`` whose unique static def is ``R = Mod(X, M)`` (same
  range condition). The SymRef position rewrites to X; CP_ALIAS
  then propagates the alias, and R's def becomes DCE-removable.

Motivation: u128 chunked encodings often emit
``R_lo = Mod(R_wide, 2^128)`` "narrow-to-low-128-bits" plus inline
``Mod(R_wide, 2^128) <= u64_max`` assertion shapes. When upstream
range analysis proves ``R_wide < 2^128`` (e.g. from a u128 quotient
of a u128-by-u64 division), both Mods are structurally identity.
The rule collapses each independently:

* ``R_lo = Mod(R_wide, 2^128); ...; assume Le(R_lo, K)`` becomes
  ``... assume Le(R_wide, K)`` (R_lo dies via CP + DCE).
* ``B = Le(Mod(R_wide, 2^128), K)`` becomes ``B = Le(R_wide, K)``
  (inline expression rewrite).

Soundness: the gate proves ``X``'s range ⊆ ``[0, M-1]`` via
``infer_expr_range``. Under that condition, ``Mod(X, M) = X``
holds. rw-eq's CHK at each rewrite site verifies the same
equivalence from the upstream bound on X.

Companion to (but distinct from) ``COPY_PROPAGATION`` / ``CP_ALIAS``
which propagates direct ``R = SymRef(Y)`` aliases without any range
gate. This rule lifts a non-trivial ``Mod`` def / inline expression
into an alias when range proves the Mod is identity.
"""

from __future__ import annotations

from ctac.ast.nodes import ApplyExpr, SymbolRef, TacExpr
from ctac.rewrite.context import RewriteCtx
from ctac.rewrite.framework import Rule
from ctac.rewrite.range_infer import infer_expr_range
from ctac.rewrite.rules.common import const_to_int


def _mod_args(
    expr: TacExpr, ctx: RewriteCtx
) -> tuple[TacExpr, TacExpr] | None:
    """Resolve ``expr`` to a ``Mod(X, M)`` ApplyExpr's args, either
    directly or via the unique static def of a SymRef. Returns
    ``(X, M_expr)`` or ``None``."""
    if isinstance(expr, ApplyExpr) and expr.op == "Mod" and len(expr.args) == 2:
        return expr.args[0], expr.args[1]
    if isinstance(expr, SymbolRef):
        d = ctx.definition(expr.name)
        if (
            isinstance(d, ApplyExpr)
            and d.op == "Mod"
            and len(d.args) == 2
        ):
            return d.args[0], d.args[1]
    return None


def _rewrite_mod_identity_cp(expr: TacExpr, ctx: RewriteCtx) -> TacExpr | None:
    """``Mod(X, M)`` (inline or via SymRef def) -> ``X`` when
    ``infer_expr_range(X) ⊆ [0, M-1]``."""
    args = _mod_args(expr, ctx)
    if args is None:
        return None
    x, m_expr = args
    m = const_to_int(m_expr)
    if m is None or m <= 0:
        return None
    rng = infer_expr_range(x, ctx)
    if rng is None or rng[0] is None or rng[1] is None:
        return None
    if rng[0] < 0 or rng[1] > m - 1:
        return None
    return x


MOD_IDENTITY_CP = Rule(
    name="ModIdentityCP",
    fn=_rewrite_mod_identity_cp,
    description=(
        "Mod(X, M) -> X when X's range proves the Mod is identity "
        "(X in [0, M-1]). Fires on inline ``Mod`` sub-expressions and "
        "on SymRefs whose def is ``Mod(X, M)``."
    ),
)

__all__ = ["MOD_IDENTITY_CP"]
