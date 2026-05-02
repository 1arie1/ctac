"""Rules for ``IntMul`` recognition and ``IntMulDiv`` introduction.

Two cooperating chain recognizers:

1. ``CHUNKED_MUL_BY_2N``: recognize SBF's u64 "extended-precision
   multiply by 2^N via chunks" idiom and replace with a clean
   ``IntMul(R, 2^N)`` in the int domain.

2. ``MUL_DIV_TO_MULDIV``: ``IntDiv(IntMul(a, b), c)`` ->
   ``IntMulDiv(a, b, c)``. The encoder (``sea_vc``) axiomatizes
   ``IntMulDiv`` with Euclidean bounds; this rule introduces the
   concept whenever a syntactic ``IntDiv`` of an ``IntMul`` shows up.

Composition: rule 1 normalizes the chunk pattern to ``IntMul``;
rule 2 then collapses ``IntDiv ∘ IntMul`` into the axiomatized
``IntMulDiv``. End-to-end on Solana fixed-point ratios (Q-format
LTV computations etc.) the chunk-shift-divide chain becomes one
``IntMulDiv`` node.

The chunked-mul shape from the SBF→TAC frontend
-------------------------------------------------

In u64 arithmetic, ``R << N`` for ``0 < N < M`` (where M = 64)
loses the top N bits of R. To preserve them, the frontend splits:

* low ``M-N`` bits of R, shifted up by N within u64 ::

      Mod(ShiftLeft(R, N), 2^M)

* top N bits of R (= ``(R mod 2^M) >> (M-N)``), placed at slot
  ``[M, M+N)`` ::

      IntMul(2^M, Div(Mod(R, 2^M), 2^(M-N)))

Their int-domain sum is exactly ``R * 2^N`` (under unsigned
semantics on R). Soundness of the rewrite:

  given M = M-N + N and R bv-typed unsigned in [0, 2^M),
  Mod(R << N, 2^M) + 2^M * (R mod 2^M) >> (M-N)
    = bits[N..M)(R) << N
    + bits[M-N..M)(R) << M
    = bits[0..M-N)(R) << N
    + bits[M-N..M)(R) << M             (since the high N bits of R << N
                                          = the bits at position [M-N, M)
                                          of R, which got truncated)
    = R << N
    = R * 2^N.

The pattern's constants (M, N) are matched literally. The two
arms must reference the *same* R (canonical equality).
"""

from __future__ import annotations

from ctac.ast.nodes import ApplyExpr, ConstExpr, TacExpr
from ctac.analysis.symbols import canonical_symbol
from ctac.rewrite.context import RewriteCtx
from ctac.rewrite.framework import Rule
from ctac.rewrite.rules.common import as_int_const, const_to_int, log2_if_pow2


_INT_ADD_OPS = frozenset({"IntAdd"})
_INT_DIV_OPS = frozenset({"IntDiv"})
_INT_MUL_OPS = frozenset({"IntMul"})


def _canonical_expr(expr: TacExpr) -> TacExpr:
    """Strip DSA suffixes from SymbolRefs recursively. Used to
    compare the two arms' R references for syntactic equality."""
    from ctac.ast.nodes import SymbolRef
    if isinstance(expr, SymbolRef):
        return SymbolRef(canonical_symbol(expr.name))
    if isinstance(expr, ApplyExpr):
        return ApplyExpr(expr.op, tuple(_canonical_expr(a) for a in expr.args))
    return expr


def _as_pow2(expr: TacExpr) -> int | None:
    """Return ``k`` if ``expr`` is a constant equal to ``2^k`` for
    some ``k >= 0``; else ``None``."""
    v = const_to_int(expr)
    if v is None:
        return None
    return log2_if_pow2(v)


def _try_chunk_arm(narrow_intmul_arg: TacExpr, ctx: RewriteCtx) -> tuple[TacExpr, int, int] | None:
    """Match the high-chunk arm: ``IntMul(2^M, Div(Mod(R, 2^M), 2^K))``
    (after lookthrough peels narrow / static defs).

    Returns ``(R_expr, M, K)`` on match, else ``None``.
    """
    inner = ctx.lookthrough(narrow_intmul_arg)
    if not (isinstance(inner, ApplyExpr) and inner.op in _INT_MUL_OPS and len(inner.args) == 2):
        return None
    a, b = inner.args
    # IntMul commutes; M is the power-of-2 factor, the other arg is the Div.
    M = _as_pow2(a)
    div_arg: TacExpr = b
    if M is None:
        M = _as_pow2(b)
        div_arg = a
    if M is None or M <= 0:
        return None
    div_arg = ctx.lookthrough(div_arg)
    if not (isinstance(div_arg, ApplyExpr) and div_arg.op == "Div" and len(div_arg.args) == 2):
        return None
    mod_arg, K_const = div_arg.args
    K = _as_pow2(K_const)
    if K is None or K < 0 or K >= M:
        return None
    mod_arg = ctx.lookthrough(mod_arg)
    if not (isinstance(mod_arg, ApplyExpr) and mod_arg.op == "Mod" and len(mod_arg.args) == 2):
        return None
    R_expr, mod_divisor = mod_arg.args
    M_inner = _as_pow2(mod_divisor)
    if M_inner != M:
        return None
    return R_expr, M, K


def _try_shift_arm(mod_shiftleft_arg: TacExpr, ctx: RewriteCtx) -> tuple[TacExpr, int, int] | None:
    """Match the low-chunk arm: ``Mod(ShiftLeft(R, N), 2^M)`` (or
    ``Mod(Shl(R, N), 2^M)``). Returns ``(R_expr, N, M)`` on match."""
    mod = ctx.lookthrough(mod_shiftleft_arg)
    if not (isinstance(mod, ApplyExpr) and mod.op == "Mod" and len(mod.args) == 2):
        return None
    sl, mod_divisor = mod.args
    M = _as_pow2(mod_divisor)
    if M is None or M <= 0:
        return None
    sl = ctx.lookthrough(sl)
    if not (isinstance(sl, ApplyExpr) and sl.op in ("ShiftLeft", "Shl") and len(sl.args) == 2):
        return None
    R_expr, N_const = sl.args
    # ShiftLeft's second operand is the shift count N itself, not 2^N.
    N = const_to_int(N_const)
    if N is None or N <= 0 or N >= M:
        return None
    return R_expr, N, M


def _rewrite_chunked_mul(expr: TacExpr, ctx: RewriteCtx) -> TacExpr | None:
    """Recognize the chunk-extended u64 multiply pattern:

        IntAdd(narrow(IntMul(2^M, Div(Mod(R, 2^M), 2^K))),
               Mod(ShiftLeft(R, N), 2^M))

    where ``K + N == M``, R is the same on both arms — and replace
    with ``IntMul(R, 2^N)`` in the int domain.

    Sound under unsigned semantics on R. Soundness derives from the
    bit-level identity in the module docstring.
    """
    if not (isinstance(expr, ApplyExpr) and expr.op in _INT_ADD_OPS and len(expr.args) == 2):
        return None
    a, b = expr.args
    # Try both arg orders.
    for high_arm, low_arm in ((a, b), (b, a)):
        chunk = _try_chunk_arm(high_arm, ctx)
        if chunk is None:
            continue
        R1, M1, K = chunk
        shift = _try_shift_arm(low_arm, ctx)
        if shift is None:
            continue
        R2, N, M2 = shift
        if M1 != M2:
            continue
        if K + N != M1:
            continue
        if _canonical_expr(R1) != _canonical_expr(R2):
            continue
        # The chunk decomposition computes 2^N * (R mod 2^M), NOT
        # 2^N * R. If R is bv256 with bits above M (e.g., bv256 with
        # value >= 2^64), the high bits are silently dropped by the
        # mods/shifts. Preserving `Mod(R, 2^M)` keeps the rewrite
        # sound without needing a range-fact on R. Downstream
        # simplification (RANGE_FOLD or analysis-aware passes) can
        # drop the `Mod` if R is provably bounded to [0, 2^M).
        template: ConstExpr = ConstExpr(f"0x{1 << M1:x}")
        for cand in (a, b):
            cand_inner = ctx.lookthrough(cand)
            if isinstance(cand_inner, ApplyExpr):
                for sub in cand_inner.args:
                    if isinstance(sub, ConstExpr):
                        template = sub
                        break
        m_const = as_int_const(template, 1 << M1)
        n_const = as_int_const(template, 1 << N)
        r_modded = ApplyExpr("Mod", (R1, m_const))
        return ApplyExpr("IntMul", (r_modded, n_const))
    return None


def _rewrite_mul_div_to_muldiv(expr: TacExpr, ctx: RewriteCtx) -> TacExpr | None:
    """``IntDiv(IntMul(a, b), c)`` -> ``IntMulDiv(a, b, c)``.

    The encoder axiomatizes ``IntMulDiv`` totally — for ``c > 0`` via
    Euclidean bounds, for ``c <= 0`` by tying it to z3's builtin
    ``div`` over ``(* a b)`` (see ``sea_vc.py:_int_mul_div_axiom_define_fun``).
    The rewrite is therefore semantics-preserving for **any** c
    (including ``c == 0`` and ``c < 0``), so no divisor-range gate
    is needed.

    ``narrow`` peeling on the numerator is sound: ``narrow`` is a
    type assertion (precondition that the value already fits in
    bv256), not a runtime mod. The encoder treats it as a no-op
    (``sea_vc.py:619-620``).
    """
    if not (isinstance(expr, ApplyExpr) and expr.op in _INT_DIV_OPS and len(expr.args) == 2):
        return None
    num, c = expr.args
    num_inner = ctx.lookthrough(num)
    if not (isinstance(num_inner, ApplyExpr) and num_inner.op in _INT_MUL_OPS and len(num_inner.args) == 2):
        return None
    a, b = num_inner.args
    return ApplyExpr("IntMulDiv", (a, b, c))


CHUNKED_MUL_BY_2N = Rule(
    name="ChunkedMul",
    fn=_rewrite_chunked_mul,
    description=(
        "Recognize SBF's chunk-extended u64 mul-by-2^N idiom: "
        "IntAdd(narrow(IntMul(2^M, Div(Mod(R, 2^M), 2^(M-N)))), "
        "Mod(ShiftLeft(R, N), 2^M)) -> IntMul(R, 2^N)."
    ),
)

MUL_DIV_TO_MULDIV = Rule(
    name="MulDiv",
    fn=_rewrite_mul_div_to_muldiv,
    description="IntDiv(IntMul(a, b), c) -> IntMulDiv(a, b, c).",
)
