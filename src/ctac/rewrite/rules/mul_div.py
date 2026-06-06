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
from ctac.rewrite.range_infer import infer_expr_range
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
    (see ``sea_vc.py:_peel_narrow``).
    """
    if not (isinstance(expr, ApplyExpr) and expr.op in _INT_DIV_OPS and len(expr.args) == 2):
        return None
    num, c = expr.args
    # through_equates: the frontend's summary-output protocol parks
    # the product in a value register and binds a havoc slot to it
    # (``assume Eq(slot, value)``); the dividend then names the slot.
    # The dominance-gated hop lets the matcher see the product; each
    # fire's rule-2 CHK discharges via the in-scope equate + value def.
    num_inner = ctx.lookthrough(num, through_equates=True)
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


_TWO_64 = 1 << 64


def _peel_int_bool(expr: TacExpr, ctx: RewriteCtx) -> TacExpr | None:
    """Unwrap the SBF 0/1-int bool convention: ``Ite(c, 1, 0)`` (after
    lookthrough) returns ``c``; a bare boolean expression returns
    itself. Returns None for anything else."""
    inner = ctx.lookthrough(expr)
    if (
        isinstance(inner, ApplyExpr)
        and inner.op == "Ite"
        and len(inner.args) == 3
        and const_to_int(inner.args[1]) == 1
        and const_to_int(inner.args[2]) == 0
    ):
        return inner.args[0]
    if isinstance(inner, ApplyExpr) and inner.op in {"Lt", "Le", "Gt", "Ge"}:
        return inner
    return None


def _match_lt(expr: TacExpr, ctx: RewriteCtx) -> tuple[TacExpr, TacExpr] | None:
    inner = ctx.lookthrough(expr)
    if isinstance(inner, ApplyExpr) and inner.op == "Lt" and len(inner.args) == 2:
        return inner.args[0], inner.args[1]
    if isinstance(inner, ApplyExpr) and inner.op == "Gt" and len(inner.args) == 2:
        return inner.args[1], inner.args[0]
    return None


def _in_range(expr: TacExpr, lo: int, hi: int, ctx: RewriteCtx) -> bool:
    rng = infer_expr_range(expr, ctx)
    if rng is None or rng[0] is None or rng[1] is None:
        return False
    return rng[0] >= lo and rng[1] <= hi


def _chunk_source(h: TacExpr, lo: TacExpr, ctx: RewriteCtx) -> TacExpr | None:
    """When ``h`` / ``l`` are the 2^64 chunk extracts of one wide value
    ``R`` (``Div(R, 2^64)`` / ``Mod(R, 2^64)`` in bv or int form, same
    canonical R), the reassembled pair IS ``R`` — return it."""
    h_in = ctx.lookthrough(h) if not isinstance(h, ApplyExpr) else h
    l_in = ctx.lookthrough(lo) if not isinstance(lo, ApplyExpr) else lo
    if not (
        isinstance(h_in, ApplyExpr)
        and h_in.op in {"Div", "IntDiv"}
        and len(h_in.args) == 2
        and const_to_int(h_in.args[1]) == _TWO_64
    ):
        return None
    if not (
        isinstance(l_in, ApplyExpr)
        and l_in.op in {"Mod", "IntMod"}
        and len(l_in.args) == 2
        and const_to_int(l_in.args[1]) == _TWO_64
    ):
        return None
    if l_in.args[0] != h_in.args[0]:
        return None
    return h_in.args[0]


def _wide_term(h: TacExpr, lo: TacExpr, ctx: RewriteCtx) -> TacExpr:
    src = _chunk_source(h, lo, ctx)
    if src is not None:
        return src
    return ApplyExpr(
        "IntAdd",
        (ApplyExpr("IntMul", (h, ConstExpr(f"{hex(_TWO_64)}(int)"))), lo),
    )


def _rewrite_chunked_u128_lt(expr: TacExpr, ctx: RewriteCtx) -> TacExpr | None:
    """The chunked-u128 lexicographic compare ladder:

        Ite(Eq(H, H'), lo_lt, hi_lt)

    where (after lookthrough and 0/1-int peeling) ``lo_lt`` compares
    ``L < L'`` and ``hi_lt`` compares ``H < H'`` over the same pair as
    the Eq — i.e. ``(H, L) <lex (H', L')``. Rewrites to the positional
    compare ``Lt(H*2^64 + L, H'*2^64 + L')``; when a side's chunks are
    the extracts of one wide value R, the side collapses to R itself.

    Gate: lexicographic == positional only when the low parts are
    inside the radix — ``L, L' in [0, 2^64)`` and ``H, H' >= 0``, all
    via dominating range facts. The arms keep the SBF 0/1-int
    convention when the input had it, so downstream Eq(_, 0) tests
    fold as before.
    """
    if not (isinstance(expr, ApplyExpr) and expr.op == "Ite" and len(expr.args) == 3):
        return None
    cond, then_e, else_e = expr.args
    cond_in = ctx.lookthrough(cond)
    if not (
        isinstance(cond_in, ApplyExpr)
        and cond_in.op == "Eq"
        and len(cond_in.args) == 2
    ):
        return None
    eq_a, eq_b = cond_in.args

    then_b = _peel_int_bool(then_e, ctx)
    else_b = _peel_int_bool(else_e, ctx)
    if then_b is None or else_b is None:
        return None
    # Arms wrapped in the 0/1 convention iff the input was.
    int_convention = not (
        isinstance(ctx.lookthrough(then_e), ApplyExpr)
        and ctx.lookthrough(then_e).op in {"Lt", "Le", "Gt", "Ge"}
    )

    lo_pair = _match_lt(then_b, ctx)
    hi_pair = _match_lt(else_b, ctx)
    if lo_pair is None or hi_pair is None:
        return None
    h_l, h_r = hi_pair
    # The Eq must test the same hi pair (either orientation).
    if not (
        (eq_a == h_l and eq_b == h_r) or (eq_a == h_r and eq_b == h_l)
    ):
        return None
    l_l, l_r = lo_pair

    int_max = (1 << 256) - 1
    if not (
        _in_range(l_l, 0, _TWO_64 - 1, ctx)
        and _in_range(l_r, 0, _TWO_64 - 1, ctx)
        and _in_range(h_l, 0, int_max, ctx)
        and _in_range(h_r, 0, int_max, ctx)
    ):
        return None

    wide = ApplyExpr(
        "Lt", (_wide_term(h_l, l_l, ctx), _wide_term(h_r, l_r, ctx))
    )
    if int_convention:
        return ApplyExpr(
            "Ite", (wide, ConstExpr("0x1"), ConstExpr("0x0"))
        )
    return wide


CHUNKED_U128_LT = Rule(
    name="ChunkedU128Lt",
    fn=_rewrite_chunked_u128_lt,
    description=(
        "Lift the chunked-u128 lexicographic compare ladder "
        "Ite(Eq(H,H'), L<L', H<H') to the positional "
        "Lt(H*2^64+L, H'*2^64+L'); chunk-extract sides collapse to "
        "their wide source. Gated on L, L' in [0, 2^64)."
    ),
)


# MULDIV_CONST_CANCEL: ``IntMulDiv(A, B, K)`` where the combined
# constant factor of ``A`` and ``B`` is divisible by the constant
# divisor ``K``. Each argument contributes (const, sym): a constant
# argument is (c, None); an argument resolving -- through equates and
# narrow annotations -- to ``IntMul(c, X)`` is (c, X); anything else
# is (1, arg). With total = cA * cB and K | total::
#
#     IntMulDiv(A, B, K) -> (total/K) * symA * symB
#
# The frontend's unit-scaling chains produce these in cascades::
#
#     R1699 = narrow(10^13 *int R148)        ; itself a prior cancel
#     assume R1699 == R412
#     muldiv(10^4, R412, 10^17) -> R148      ; 10^4 * 10^13 = 10^17
#
# Soundness: A*B = total * symA * symB = K * (total/K) * symA * symB
# exactly when K | total, and the floor of an exact quotient is the
# quotient regardless of operand signs -- no range gates needed.
# Each fire removes one nonlinear division term from the VC; equate
# hops are verified per use by rw-eq's rule-2 CHK.


def _const_sym_factor(
    e: TacExpr, ctx: RewriteCtx
) -> tuple[int, TacExpr | None, ConstExpr | None]:
    """Split an IntMulDiv argument into (const factor, symbolic
    factor, a ConstExpr usable as a formatting template)."""
    c = const_to_int(e)
    if c is not None and c > 0:
        assert isinstance(e, ConstExpr)
        return c, None, e
    inner = ctx.lookthrough(e, through_equates=True)
    if (
        isinstance(inner, ApplyExpr)
        and inner.op == "IntMul"
        and len(inner.args) == 2
    ):
        for c_expr, x in (
            (inner.args[0], inner.args[1]),
            (inner.args[1], inner.args[0]),
        ):
            cv = const_to_int(c_expr)
            if cv is not None and cv > 0:
                assert isinstance(c_expr, ConstExpr)
                return cv, x, c_expr
    return 1, e, None


def _rewrite_muldiv_const_cancel(
    expr: TacExpr, ctx: RewriteCtx
) -> TacExpr | None:
    if not (
        isinstance(expr, ApplyExpr)
        and expr.op == "IntMulDiv"
        and len(expr.args) == 3
    ):
        return None
    a, b, k_expr = expr.args
    k = const_to_int(k_expr)
    if k is None or k <= 1:
        return None
    a_c, a_sym, a_tmpl = _const_sym_factor(a, ctx)
    b_c, b_sym, b_tmpl = _const_sym_factor(b, ctx)
    total = a_c * b_c
    if total % k != 0:
        return None
    q = total // k
    template = a_tmpl or b_tmpl
    assert template is not None  # total % k == 0 with k > 1 needs a const
    syms = [sym for sym in (a_sym, b_sym) if sym is not None]
    result: TacExpr = as_int_const(template, q)
    if q == 1 and syms:
        result = syms[0]
        syms = syms[1:]
    for sym in syms:
        result = ApplyExpr("IntMul", (result, sym))
    return result


MULDIV_CONST_CANCEL = Rule(
    name="MulDivConstCancel",
    fn=_rewrite_muldiv_const_cancel,
    description=(
        "IntMulDiv(A, B, K) -> (cA*cB/K) * symA * symB when const K "
        "divides the combined constant factor of the arguments "
        "(equate- and narrow-aware). Exact division; removes a "
        "nonlinear division term."
    ),
)
