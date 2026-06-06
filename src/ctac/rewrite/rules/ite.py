"""Ite / boolean rewrite rules.

These collaborate to collapse patterns like::

    R98 = Ite(c1, Ite(c2, Ite(c3, Ite(c4, 0x0, 0x1), 0x1), 0x1), 0x1)
    assume Eq(R98, 0x1)

into a disjunction of the branch conditions. The trick is to distribute the
outer ``Eq`` into the ``Ite`` branches, fold ``Eq(const, const)`` to bool
literals, and collapse Ites whose branches are ``true``/``false``.

Individual rules are tiny and generally useful beyond this one pattern:
the driver's fixed-point loop composes them.
"""

from __future__ import annotations

from ctac.ast.nodes import ApplyExpr, ConstExpr, SymbolRef, TacExpr
from ctac.rewrite.context import RewriteCtx
from ctac.rewrite.framework import Rule
from ctac.rewrite.range_infer import infer_expr_range
from ctac.rewrite.rules.common import (
    MUL_OPS,
    as_int_const,
    const_to_int,
    eq_modulo_meta,
    reformat_const,
)

_TRUE = ConstExpr("true")
_FALSE = ConstExpr("false")


def _is_true(e: TacExpr) -> bool:
    return isinstance(e, ConstExpr) and e.value.strip() == "true"


def _is_false(e: TacExpr) -> bool:
    return isinstance(e, ConstExpr) and e.value.strip() == "false"


def _is_ite(e: TacExpr) -> bool:
    return isinstance(e, ApplyExpr) and e.op == "Ite" and len(e.args) == 3


def _rewrite_eq_reflexive(expr: TacExpr, _ctx: RewriteCtx) -> TacExpr | None:
    """``Eq(e, e)`` -> ``true`` for any pair equal modulo DSA meta
    suffixes (``Eq(R1211:20, R1211)`` names the same symbol twice).

    Specifically clears the ``Eq(X, X)`` shape that
    ``HAVOC_EQUATE_SUBST`` synthesizes when its substitution turns
    an `Eq(R, X)` equality assume into `Eq(X, X)`. The
    range-redundant-assume pass then drops the resulting
    ``assume true``."""
    if not (isinstance(expr, ApplyExpr) and expr.op == "Eq" and len(expr.args) == 2):
        return None
    a, b = expr.args
    if eq_modulo_meta(a, b):
        return _TRUE
    return None


def _rewrite_eq_const_fold(expr: TacExpr, _ctx: RewriteCtx) -> TacExpr | None:
    """``Eq(const, const)`` folds to ``true`` / ``false``."""
    if not (isinstance(expr, ApplyExpr) and expr.op == "Eq" and len(expr.args) == 2):
        return None
    a, b = expr.args
    if not (isinstance(a, ConstExpr) and isinstance(b, ConstExpr)):
        return None
    # Bool literal comparisons.
    a_true, a_false = _is_true(a), _is_false(a)
    b_true, b_false = _is_true(b), _is_false(b)
    if (a_true or a_false) and (b_true or b_false):
        return _TRUE if (a_true == b_true) else _FALSE
    va = const_to_int(a)
    vb = const_to_int(b)
    if va is None or vb is None:
        return None
    return _TRUE if va == vb else _FALSE


def _eq_leaf_will_fold(leaf: TacExpr, other: TacExpr) -> bool:
    """True iff ``Eq(leaf, other)`` will collapse via ``EqReflexive`` or
    ``EqFold``. Used as the cost gate for ``EQ_ITE_DIST``: distribution
    only pays off when at least one resulting branch fold-collapses,
    otherwise we just duplicate the Ite tree (and ``other``) for no win.
    """
    if leaf == other:
        return True  # EqReflexive
    if isinstance(leaf, ConstExpr) and isinstance(other, ConstExpr):
        return True  # EqFold
    return False


def _rewrite_eq_ite_distribute(expr: TacExpr, ctx: RewriteCtx) -> TacExpr | None:
    """``Eq(Ite(c, T, E), V)`` -> ``Ite(c, Eq(T, V), Eq(E, V))`` (and symmetric).

    Gated: fires only when at least one resulting branch equality will
    collapse via ``EqReflexive`` or ``EqFold``. Without this gate the rule
    distributes ``Eq`` across nested Ite definitions even when no leaf
    folds, duplicating both the Ite tree and ``V`` for no reduction.
    The motivating ``Eq(BigNestedIte, 0x1)`` pattern still fires because
    the inlined Ite has a constant else-leaf at every level.
    """
    if not (isinstance(expr, ApplyExpr) and expr.op == "Eq" and len(expr.args) == 2):
        return None
    a, b = expr.args
    a_lt = ctx.lookthrough(a)
    if _is_ite(a_lt):
        assert isinstance(a_lt, ApplyExpr)
        cond, then, els = a_lt.args
        if _eq_leaf_will_fold(then, b) or _eq_leaf_will_fold(els, b):
            return ApplyExpr(
                "Ite",
                (cond, ApplyExpr("Eq", (then, b)), ApplyExpr("Eq", (els, b))),
            )
    b_lt = ctx.lookthrough(b)
    if _is_ite(b_lt):
        assert isinstance(b_lt, ApplyExpr)
        cond, then, els = b_lt.args
        if _eq_leaf_will_fold(then, a) or _eq_leaf_will_fold(els, a):
            return ApplyExpr(
                "Ite",
                (cond, ApplyExpr("Eq", (a, then)), ApplyExpr("Eq", (a, els))),
            )
    return None


_ADD_OPS = frozenset({"Add", "IntAdd"})
_SUB_OPS = frozenset({"Sub", "IntSub"})


def _is_atomic_after_narrow(e: TacExpr, ctx: RewriteCtx) -> bool:
    """True iff ``e`` is a ``SymbolRef`` or ``ConstExpr`` once ``safe_math_narrow``
    wrappers are peeled. The cost gate for the Add/Sub-over-Ite distribution
    rules: distribution duplicates the non-Ite operand into both branches, so
    we fire only when that operand is "free to duplicate" (a single name or
    literal). Compound operands like ``narrow(muldiv(...))`` or a nested Ite
    would balloon the AST and rarely enable downstream folds, so we keep the
    surrounding op intact and let the encoder handle the Ite uniformly.
    """
    peeled = ctx.peel_narrow(e)
    return isinstance(peeled, (SymbolRef, ConstExpr))


def _rewrite_add_ite_distribute(expr: TacExpr, ctx: RewriteCtx) -> TacExpr | None:
    """``Add(Ite(c, T, E), Y)`` -> ``Ite(c, Add(T, Y), Add(E, Y))`` (and symmetric).

    Applies to both ``Add`` and ``IntAdd``, and peels
    ``safe_math_narrow_bvN`` wrappers so e.g. ``narrow(IntAdd(X,
    Ite(c, T, E)))`` also distributes. Distribution is sound in int,
    bv, and mixed semantics — the Ite selects an operand and the outer
    op commutes with branch selection.

    Cost-gated: fires when the non-Ite operand is atomic after peeling
    ``safe_math_narrow`` (a ``SymbolRef`` or ``ConstExpr``) — OR when
    both Ite arms are constants. Distributing across a compound
    operand duplicates it inside both arms and rarely enables a
    downstream fold, EXCEPT for the const-arm carry idiom
    ``IntAdd(X, Ite(c, 1, 0))``: there ``Ite(c, X + 1, X + 0)`` folds
    the else-arm back to ``X`` and is exactly the distributed shape
    the u128 carry-add matcher keys on (older Prover builds inline
    the hi-div into ``X`` instead of naming it, so the atomicity gate
    alone starves the lift cascade).
    """
    if not (isinstance(expr, ApplyExpr) and expr.op in _ADD_OPS and len(expr.args) == 2):
        return None

    def _const_arms(ite: ApplyExpr) -> bool:
        return isinstance(ite.args[1], ConstExpr) and isinstance(
            ite.args[2], ConstExpr
        )

    op = expr.op
    a, b = expr.args
    a_lt = ctx.peel_narrow(a)
    if _is_ite(a_lt):
        assert isinstance(a_lt, ApplyExpr)
        if _is_atomic_after_narrow(b, ctx) or _const_arms(a_lt):
            cond, then, els = a_lt.args
            return ApplyExpr(
                "Ite",
                (cond, ApplyExpr(op, (then, b)), ApplyExpr(op, (els, b))),
            )
    b_lt = ctx.peel_narrow(b)
    if _is_ite(b_lt):
        assert isinstance(b_lt, ApplyExpr)
        if _is_atomic_after_narrow(a, ctx) or _const_arms(b_lt):
            cond, then, els = b_lt.args
            return ApplyExpr(
                "Ite",
                (cond, ApplyExpr(op, (a, then)), ApplyExpr(op, (a, els))),
            )
    return None


def _rewrite_sub_ite_distribute_left(expr: TacExpr, ctx: RewriteCtx) -> TacExpr | None:
    """``Sub(Ite(c, T, E), Y)`` -> ``Ite(c, Sub(T, Y), Sub(E, Y))``.

    Applies to both ``Sub`` and ``IntSub``; peels narrows on the LHS.
    Sub is non-commutative, so LHS and RHS Ite are separate rules.

    Cost-gated like ``ADD_ITE_DIST``: ``Y`` must be atomic
    (``SymbolRef`` / ``ConstExpr``) after peeling narrow.
    """
    if not (isinstance(expr, ApplyExpr) and expr.op in _SUB_OPS and len(expr.args) == 2):
        return None
    op = expr.op
    a, b = expr.args
    a_lt = ctx.peel_narrow(a)
    if not _is_ite(a_lt):
        return None
    if not _is_atomic_after_narrow(b, ctx):
        return None
    assert isinstance(a_lt, ApplyExpr)
    cond, then, els = a_lt.args
    return ApplyExpr(
        "Ite",
        (cond, ApplyExpr(op, (then, b)), ApplyExpr(op, (els, b))),
    )


def _is_zero_const(e: TacExpr) -> bool:
    return isinstance(e, ConstExpr) and const_to_int(e) == 0


def _rewrite_add_sub_zero_fold(expr: TacExpr, _ctx: RewriteCtx) -> TacExpr | None:
    """Additive identity. ``Add(X, 0)``, ``IntAdd(X, 0)``, ``Sub(X, 0)``,
    ``IntSub(X, 0)`` -> ``X``; ``Add(0, X)`` / ``IntAdd(0, X)`` -> ``X``.

    Pairs with ``ADD_ITE_DIST`` / ``SUB_ITE_DIST_*``: distributing
    ``Y +/- Ite(c, K, 0)`` over the Ite produces a ``+/- 0`` arm that
    this rule retires. Without it the zombie arm sits inside the Ite
    forever and the outer narrow/Eq sees a structurally complex
    operand. Sound for both bv-modular (``X + 0`` mod 2^N = X) and
    Int (``X + 0`` = X) semantics. Sub-left-zero is *not* folded —
    that is unary negation, not identity.
    """
    if not isinstance(expr, ApplyExpr) or len(expr.args) != 2:
        return None
    a, b = expr.args
    if expr.op in _ADD_OPS:
        if _is_zero_const(b):
            return a
        if _is_zero_const(a):
            return b
        return None
    if expr.op in _SUB_OPS:
        if _is_zero_const(b):
            return a
        return None
    return None


def _rewrite_sub_ite_distribute_right(expr: TacExpr, ctx: RewriteCtx) -> TacExpr | None:
    """``Sub(X, Ite(c, T, E))`` -> ``Ite(c, Sub(X, T), Sub(X, E))``.

    Cost-gated like ``ADD_ITE_DIST``: ``X`` must be atomic
    (``SymbolRef`` / ``ConstExpr``) after peeling narrow.
    """
    if not (isinstance(expr, ApplyExpr) and expr.op in _SUB_OPS and len(expr.args) == 2):
        return None
    op = expr.op
    a, b = expr.args
    b_lt = ctx.peel_narrow(b)
    if not _is_ite(b_lt):
        return None
    if not _is_atomic_after_narrow(a, ctx):
        return None
    assert isinstance(b_lt, ApplyExpr)
    cond, then, els = b_lt.args
    return ApplyExpr(
        "Ite",
        (cond, ApplyExpr(op, (a, then)), ApplyExpr(op, (a, els))),
    )


_BV256_MOD = 1 << 256


def _rewrite_arith_const_fold(expr: TacExpr, _ctx: RewriteCtx) -> TacExpr | None:
    """Fold binary arithmetic / bitwise ops over two :class:`ConstExpr`
    operands. Covers Int and bv variants of Add/Sub/Mul/Div/Mod plus
    BWAnd, and the unsigned order comparisons Lt/Le/Gt/Ge (folding to
    bool literals, e.g. the frontend's ``assume Gt(10^4, 0)`` divisor
    guard). Result preserves the operand's type tag via
    :func:`as_int_const` (for Int ops) or :func:`reformat_const` (for
    bv ops).

    Sound by reduction to the standard arithmetic / bitwise
    semantics: Int ops are non-modular; bv ops wrap mod 2^256;
    Div/Mod abstain when the divisor is zero (the source code's
    behavior on Div-by-zero is the existing rule output, not a fold).
    Lt/Le/Gt/Ge order both bv and Int constants by their integer
    magnitude (bv values are non-negative). The signed Slt/Sle/Sgt/Sge
    forms are deliberately not folded here — they reinterpret the bv
    pattern and have no observed const-const occurrences.
    """
    if not (isinstance(expr, ApplyExpr) and len(expr.args) == 2):
        return None
    a, b = expr.args
    if not (isinstance(a, ConstExpr) and isinstance(b, ConstExpr)):
        return None
    va = const_to_int(a)
    vb = const_to_int(b)
    if va is None or vb is None:
        return None
    op = expr.op
    if op == "IntAdd":
        return as_int_const(a, va + vb)
    if op == "IntSub":
        return as_int_const(a, va - vb)
    if op == "IntMul":
        return as_int_const(a, va * vb)
    if op == "IntDiv" and vb != 0:
        return as_int_const(a, va // vb)
    if op == "IntMod" and vb != 0:
        return as_int_const(a, va % vb)
    if op == "Add":
        return reformat_const(a, (va + vb) % _BV256_MOD)
    if op == "Sub":
        return reformat_const(a, (va - vb) % _BV256_MOD)
    if op == "Mul":
        return reformat_const(a, (va * vb) % _BV256_MOD)
    if op == "Div" and vb != 0:
        return reformat_const(a, va // vb)
    if op == "Mod" and vb != 0:
        return reformat_const(a, va % vb)
    if op == "BWAnd":
        return reformat_const(a, va & vb)
    if op == "Lt":
        return _TRUE if va < vb else _FALSE
    if op == "Le":
        return _TRUE if va <= vb else _FALSE
    if op == "Gt":
        return _TRUE if va > vb else _FALSE
    if op == "Ge":
        return _TRUE if va >= vb else _FALSE
    return None


def _rewrite_mul_zero_one(expr: TacExpr, _ctx: RewriteCtx) -> TacExpr | None:
    """``X * 0`` -> ``0``, ``0 * X`` -> ``0``, ``X * 1`` -> ``X``,
    ``1 * X`` -> ``X``. Applies to both ``Mul`` and ``IntMul``.

    Soundness: ``bv * 0 ≡ 0 (mod 2^256)``, ``bv * 1 = bv``;
    ``Int * 0 = 0``, ``Int * 1 = Int``. Zero-absorption preserves the
    *constant* operand's type tag (so e.g. ``IntMul(X, 0(int))`` folds
    to ``0(int)``, not bare ``0``).
    """
    if not (isinstance(expr, ApplyExpr) and expr.op in MUL_OPS and len(expr.args) == 2):
        return None
    a, b = expr.args
    va = const_to_int(a)
    vb = const_to_int(b)
    if vb == 0:
        return b
    if va == 0:
        return a
    if vb == 1:
        return a
    if va == 1:
        return b
    return None


def _rewrite_int_mul_eq_zero(expr: TacExpr, ctx: RewriteCtx) -> TacExpr | None:
    """``Eq(IntMul(X, K), 0)`` -> ``Eq(X, 0)`` when ``K`` is a nonzero
    integer constant. Symmetric in Eq's operand order and in IntMul's
    operand order.

    Argues from integer (non-modular) multiplication semantics:
    ``X * K == 0`` iff ``X == 0 ∨ K == 0``; with ``K ≠ 0`` the disjunct
    on K is impossible, so the equivalence collapses to ``X == 0``.

    Unsound for the bv-modular ``Mul`` op — e.g. ``Mul(2^128, 2^128)``
    is ``0 mod 2^256`` with both operands nonzero. The rule restricts
    to ``IntMul`` for that reason.

    Lookthrough is applied to both Eq operands so the rule fires
    against the common shape where the IntMul arrives via a SymbolRef
    alias (a static def ``R = IntMul(...)`` then ``Eq(R, 0)``).
    """
    if not (isinstance(expr, ApplyExpr) and expr.op == "Eq" and len(expr.args) == 2):
        return None
    a, b = expr.args
    a_lt = ctx.lookthrough(a)
    b_lt = ctx.lookthrough(b)
    if _is_zero_const(b_lt):
        mul_expr, zero = a_lt, b
    elif _is_zero_const(a_lt):
        mul_expr, zero = b_lt, a
    else:
        return None
    if not (isinstance(mul_expr, ApplyExpr) and mul_expr.op == "IntMul" and len(mul_expr.args) == 2):
        return None
    arg1, arg2 = mul_expr.args
    v1 = const_to_int(arg1)
    v2 = const_to_int(arg2)
    if v2 is not None and v2 != 0:
        return ApplyExpr("Eq", (arg1, zero))
    if v1 is not None and v1 != 0:
        return ApplyExpr("Eq", (arg2, zero))
    return None


_ZERO_PRESERVING_FIRST_ARG = frozenset({
    "Div", "IntDiv",
    "Mod", "IntMod",
    "ShiftLeftLogical", "ShiftRightLogical", "ShiftRightArithmetical",
})
# f(0, ...) == 0: ops whose value is zero whenever their FIRST arg is zero.
# Div/Mod: standard semantics give 0/K = 0, 0 mod K = 0 (any K, including 0
# under SMT-LIB div-by-zero conventions; the rewrite doesn't introduce new
# UB because the original else-branch already evaluates the op).
# Shifts: 0 shifted by anything is 0.

_ZERO_PRESERVING_ANY_ARG = frozenset({
    "Mul", "IntMul",
    "BWAnd",
})
# f(..., 0, ...) == 0: ops whose value is zero whenever ANY arg is zero.
# Mul/IntMul: standard. BWAnd: bitwise AND with zero is zero.


def _is_zero_at_x(expr: TacExpr, x: TacExpr, ctx: RewriteCtx) -> bool:
    """True iff ``expr`` is structurally zero when ``x`` is zero.

    Sound under-approximation: walks zero-preserving op compositions
    (Div/Mod/shift in first arg; Mul/IntMul/BWAnd in any arg;
    IntMulDiv in either numerator arg) down to a leaf, returning True
    when the leaf is ``x``. Uses :meth:`RewriteCtx.lookthrough` to see
    through static-def aliases at every level — so a SymbolRef whose
    def is ``Div(X, K)`` is recognized as zero-at-X.

    Comparisons use :func:`eq_modulo_meta` so DSA version suffixes
    (``:N``) on the symbol's references don't defeat the match: the
    condition's ``X`` and the branch's ``X`` may be the same TAC
    register at different versions.
    """
    if eq_modulo_meta(expr, x):
        return True
    expr_lt = ctx.lookthrough(expr)
    if eq_modulo_meta(expr_lt, x):
        return True
    if not isinstance(expr_lt, ApplyExpr):
        return False
    if expr_lt.op in _ZERO_PRESERVING_FIRST_ARG and expr_lt.args:
        return _is_zero_at_x(expr_lt.args[0], x, ctx)
    if expr_lt.op in _ZERO_PRESERVING_ANY_ARG:
        return any(_is_zero_at_x(a, x, ctx) for a in expr_lt.args)
    if expr_lt.op == "IntMulDiv" and len(expr_lt.args) == 3:
        # IntMulDiv(a, b, c) = (a * b) / c; zero when a or b is zero.
        return _is_zero_at_x(expr_lt.args[0], x, ctx) or _is_zero_at_x(
            expr_lt.args[1], x, ctx
        )
    return False


def _rewrite_ite_zero_or_self(expr: TacExpr, ctx: RewriteCtx) -> TacExpr | None:
    """``Ite(Eq(X, 0), 0, F(X))`` -> ``F(X)`` and
    ``Ite(Eq(X, 0), F(X), 0)`` -> ``0``, where ``F(X)`` is any
    zero-preserving composition (``F(0) = 0``) — at minimum
    ``F = identity``, ``Div(X, _)``, ``IntMul(X, _)`` /
    ``IntMul(_, X)``, ``BWAnd``, ``Mod``, shifts, and ``IntMulDiv``
    with X as a numerator argument. See :func:`_is_zero_at_x`.

    Both shapes return ``els``: on the cond-true branch X is
    constrained to 0, so F(X) evaluates to 0 = the const-0 arm;
    on the cond-false branch the else arm is selected. Either way
    the result equals the else arm everywhere.

    Lookthrough is applied to the condition so the rule fires when
    the Ite condition arrives via a SymbolRef whose def is
    ``Eq(X, 0)`` (the typical ``B = X == 0`` shape), and inside the
    branch check via :func:`_is_zero_at_x` so a SymbolRef aliasing
    ``Div(X, K)`` is still recognized.
    """
    if not _is_ite(expr):
        return None
    assert isinstance(expr, ApplyExpr)
    cond, then, els = expr.args
    cond_lt = ctx.lookthrough(cond)
    if not (
        isinstance(cond_lt, ApplyExpr)
        and cond_lt.op == "Eq"
        and len(cond_lt.args) == 2
    ):
        return None
    a, b = cond_lt.args
    if _is_zero_const(b):
        x = a
    elif _is_zero_const(a):
        x = b
    else:
        return None
    # Shape 1: Ite(Eq(X,0), 0, F(X)) -> F(X) (= els)
    if _is_zero_const(then) and _is_zero_at_x(els, x, ctx):
        return els
    # Shape 2: Ite(Eq(X,0), F(X), 0) -> 0 (= els)
    if _is_zero_at_x(then, x, ctx) and _is_zero_const(els):
        return els
    return None


def _rewrite_ite_same(expr: TacExpr, _ctx: RewriteCtx) -> TacExpr | None:
    """``Ite(c, X, X)`` -> ``X``."""
    if not _is_ite(expr):
        return None
    assert isinstance(expr, ApplyExpr)
    _cond, then, els = expr.args
    if then == els:
        return then
    return None


def _rewrite_ite_shared_leaf(expr: TacExpr, _ctx: RewriteCtx) -> TacExpr | None:
    """Collapse a 3-arm Ite where the inner Ite shares a leaf with the outer.

    Four shapes, all type-agnostic (apply to bool, bv, int, bytemap RHSes
    alike). Soundness verified via z3: each form is propositionally
    equivalent to its rewrite under every assignment to (c, c', X, Y).

    * ``Ite(c, X, Ite(c', Y, X))`` -> ``Ite(¬c ∧ c', Y, X)``
    * ``Ite(c, X, Ite(c', X, Y))`` -> ``Ite(c ∨ c', X, Y)``
    * ``Ite(c, Ite(c', X, Y), X)`` -> ``Ite(c ∧ ¬c', Y, X)``
    * ``Ite(c, Ite(c', X, Y), Y)`` -> ``Ite(c ∧ c', X, Y)``

    Motivating case: SSA φ-merges over Reachability flags at join blocks
    with N>2 predecessors. When N-1 predecessors carry the same map
    value (the common case for a join after an inlined function call
    that doesn't modify the map on most arms), the nested-Ite encoding
    has the outer-then == inner-else (or symmetric) shape, and one
    layer collapses. Encoder-side ``_simplify_ite`` only handles the
    ``Ite(c, X, X)`` collapse (covered by ``IteSame``); this rule is
    the next-deepest structural simplification."""
    if not _is_ite(expr):
        return None
    assert isinstance(expr, ApplyExpr)
    cond, then, els = expr.args

    # Nested Ite in else arm: shapes 1 and 2.
    if _is_ite(els):
        assert isinstance(els, ApplyExpr)
        c2, then2, els2 = els.args
        # Shape 1: Ite(c, X, Ite(c', Y, X)) -> Ite(¬c ∧ c', Y, X)
        if then == els2:
            new_cond = ApplyExpr("LAnd", (ApplyExpr("LNot", (cond,)), c2))
            return ApplyExpr("Ite", (new_cond, then2, then))
        # Shape 2: Ite(c, X, Ite(c', X, Y)) -> Ite(c ∨ c', X, Y)
        if then == then2:
            new_cond = ApplyExpr("LOr", (cond, c2))
            return ApplyExpr("Ite", (new_cond, then, els2))

    # Nested Ite in then arm: shapes 3 and 4.
    if _is_ite(then):
        assert isinstance(then, ApplyExpr)
        c2, then2, els2 = then.args
        # Shape 3: Ite(c, Ite(c', X, Y), X) -> Ite(c ∧ ¬c', Y, X)
        if els == then2:
            new_cond = ApplyExpr("LAnd", (cond, ApplyExpr("LNot", (c2,))))
            return ApplyExpr("Ite", (new_cond, els2, els))
        # Shape 4: Ite(c, Ite(c', X, Y), Y) -> Ite(c ∧ c', X, Y)
        if els == els2:
            new_cond = ApplyExpr("LAnd", (cond, c2))
            return ApplyExpr("Ite", (new_cond, then2, els))

    return None


def _rewrite_ite_same_cond_nested(
    expr: TacExpr, _ctx: RewriteCtx
) -> TacExpr | None:
    """Prune a nested Ite that re-tests the outer's exact condition.

    * ``Ite(c, X, Ite(c, Y, Z))`` -> ``Ite(c, X, Z)`` — the inner is
      reached only when ``c`` is false, so its then-arm is dead.
    * ``Ite(c, Ite(c, X, Y), Z)`` -> ``Ite(c, X, Z)`` — symmetric.

    Type-agnostic and unconditionally sound (propositional: the inner
    test's outcome is fixed by the path that reaches it). Conditions
    compare by exact expression equality. Motivating case: the SBF
    saturating-sub lowering emits ``R = if TB { f } else { (if TB
    { 0 } else { 1 }) }`` — the else-arm's re-test is constant 1.
    """
    if not _is_ite(expr):
        return None
    assert isinstance(expr, ApplyExpr)
    cond, then, els = expr.args
    if _is_ite(els):
        assert isinstance(els, ApplyExpr)
        c2, _then2, els2 = els.args
        if c2 == cond:
            return ApplyExpr("Ite", (cond, then, els2))
    if _is_ite(then):
        assert isinstance(then, ApplyExpr)
        c2, then2, _els2 = then.args
        if c2 == cond:
            return ApplyExpr("Ite", (cond, then2, els))
    return None


def _rewrite_ite_bool(expr: TacExpr, _ctx: RewriteCtx) -> TacExpr | None:
    """Collapse Ite whose branches include a ``true`` / ``false`` literal."""
    if not _is_ite(expr):
        return None
    assert isinstance(expr, ApplyExpr)
    cond, then, els = expr.args
    if _is_true(then) and _is_false(els):
        return cond
    if _is_false(then) and _is_true(els):
        return ApplyExpr("LNot", (cond,))
    if _is_true(then):
        return ApplyExpr("LOr", (cond, els))
    if _is_false(then):
        return ApplyExpr("LAnd", (ApplyExpr("LNot", (cond,)), els))
    if _is_true(els):
        return ApplyExpr("LOr", (ApplyExpr("LNot", (cond,)), then))
    if _is_false(els):
        return ApplyExpr("LAnd", (cond, then))
    return None


_CMP_OPS = frozenset({"Ge", "Gt", "Le", "Lt", "Eq", "Ne"})


def _eval_cmp_from_range(
    cond: TacExpr, ctx: RewriteCtx
) -> bool | None:
    """Return True/False if ``cond`` is a comparison that range-inference
    decides unambiguously; None otherwise.

    Handles only binary comparisons whose operands both have an inferred
    range. No effort is made to reason about boolean combinations — those
    collapse via the driver's bottom-up traversal once the inner
    comparisons fold.
    """
    if not isinstance(cond, ApplyExpr) or cond.op not in _CMP_OPS or len(cond.args) != 2:
        return None
    a_r = infer_expr_range(cond.args[0], ctx)
    b_r = infer_expr_range(cond.args[1], ctx)
    if a_r is None or b_r is None:
        return None
    a_lo, a_hi = a_r
    b_lo, b_hi = b_r
    op = cond.op
    if op == "Ge":
        if a_lo >= b_hi:
            return True
        if a_hi < b_lo:
            return False
    elif op == "Gt":
        if a_lo > b_hi:
            return True
        if a_hi <= b_lo:
            return False
    elif op == "Le":
        if a_hi <= b_lo:
            return True
        if a_lo > b_hi:
            return False
    elif op == "Lt":
        if a_hi < b_lo:
            return True
        if a_lo >= b_hi:
            return False
    elif op == "Eq":
        if a_lo == a_hi == b_lo == b_hi:
            return True
        if a_hi < b_lo or b_hi < a_lo:
            return False
    elif op == "Ne":
        if a_hi < b_lo or b_hi < a_lo:
            return True
        if a_lo == a_hi == b_lo == b_hi:
            return False
    return None


def _rewrite_ite_cond_fold(expr: TacExpr, ctx: RewriteCtx) -> TacExpr | None:
    """``Ite(cond, then, else)`` -> ``then`` if range analysis proves ``cond``
    is always true, ``else`` if always false."""
    if not _is_ite(expr):
        return None
    assert isinstance(expr, ApplyExpr)
    cond, then, els = expr.args
    truth = _eval_cmp_from_range(cond, ctx)
    if truth is True:
        return then
    if truth is False:
        return els
    return None


_LNOT_CMP_FLIP = {"Lt": "Ge", "Le": "Gt", "Gt": "Le", "Ge": "Lt"}


def _rewrite_bool_absorb(expr: TacExpr, _ctx: RewriteCtx) -> TacExpr | None:
    """``LOr``/``LAnd``/``LNot`` simplifications with ``true``/``false`` and negated comparisons."""
    if not isinstance(expr, ApplyExpr):
        return None
    if expr.op == "LOr" and len(expr.args) == 2:
        a, b = expr.args
        if _is_true(a) or _is_true(b):
            return _TRUE
        if _is_false(a):
            return b
        if _is_false(b):
            return a
    elif expr.op == "LAnd" and len(expr.args) == 2:
        a, b = expr.args
        if _is_false(a) or _is_false(b):
            return _FALSE
        if _is_true(a):
            return b
        if _is_true(b):
            return a
    elif expr.op == "LNot" and len(expr.args) == 1:
        inner = expr.args[0]
        if _is_true(inner):
            return _FALSE
        if _is_false(inner):
            return _TRUE
        if isinstance(inner, ApplyExpr) and inner.op == "LNot" and len(inner.args) == 1:
            return inner.args[0]
        if (
            isinstance(inner, ApplyExpr)
            and inner.op in _LNOT_CMP_FLIP
            and len(inner.args) == 2
        ):
            return ApplyExpr(_LNOT_CMP_FLIP[inner.op], inner.args)
    return None


def _rewrite_demorgan(expr: TacExpr, _ctx: RewriteCtx) -> TacExpr | None:
    """De Morgan: ``LOr(!A, !B) -> !LAnd(A, B)``; ``LAnd(!A, !B) -> !LOr(A, B)``.

    Applied bottom-up, turns right-associated chains like
    ``LOr(!a, LOr(!b, LOr(!c, !d)))`` into ``!LAnd(a, LAnd(b, LAnd(c, d)))``.
    """
    if not isinstance(expr, ApplyExpr) or len(expr.args) != 2:
        return None
    if expr.op not in {"LOr", "LAnd"}:
        return None
    a, b = expr.args
    if not (
        isinstance(a, ApplyExpr) and a.op == "LNot" and len(a.args) == 1
        and isinstance(b, ApplyExpr) and b.op == "LNot" and len(b.args) == 1
    ):
        return None
    dual = "LAnd" if expr.op == "LOr" else "LOr"
    return ApplyExpr("LNot", (ApplyExpr(dual, (a.args[0], b.args[0])),))


EQ_CONST_FOLD = Rule(
    name="EqFold",
    fn=_rewrite_eq_const_fold,
    description="Eq(const, const) -> true|false.",
)
EQ_REFLEXIVE = Rule(
    name="EqReflexive",
    fn=_rewrite_eq_reflexive,
    description="Eq(e, e) -> true.",
)
EQ_ITE_DIST = Rule(
    name="EqIte",
    fn=_rewrite_eq_ite_distribute,
    description="Eq(Ite(c, T, E), V) -> Ite(c, Eq(T, V), Eq(E, V)).",
)
ADD_ITE_DIST = Rule(
    name="AddIte",
    fn=_rewrite_add_ite_distribute,
    description="Add(Ite(c, T, E), Y) -> Ite(c, Add(T, Y), Add(E, Y)) (and symmetric).",
)
SUB_ITE_DIST_LEFT = Rule(
    name="SubIteLeft",
    fn=_rewrite_sub_ite_distribute_left,
    description="Sub(Ite(c, T, E), Y) -> Ite(c, Sub(T, Y), Sub(E, Y)).",
)
SUB_ITE_DIST_RIGHT = Rule(
    name="SubIteRight",
    fn=_rewrite_sub_ite_distribute_right,
    description="Sub(X, Ite(c, T, E)) -> Ite(c, Sub(X, T), Sub(X, E)).",
)
ADD_SUB_ZERO_FOLD = Rule(
    name="AddSubZero",
    fn=_rewrite_add_sub_zero_fold,
    description=(
        "Additive identity: X + 0 -> X, 0 + X -> X, X - 0 -> X (for both "
        "Add/IntAdd and Sub/IntSub). Retires zero-arm zombies produced by "
        "ADD_ITE_DIST / SUB_ITE_DIST_* when an Ite arm is 0."
    ),
)
ARITH_CONST_FOLD = Rule(
    name="ArithConstFold",
    fn=_rewrite_arith_const_fold,
    description=(
        "Binary const-const fold for Add/Sub/Mul/Div/Mod/BWAnd in "
        "both Int and bv variants. bv ops wrap mod 2^256; Int ops "
        "are non-modular. Abstains on divisor-zero."
    ),
)
MUL_ZERO_ONE_FOLD = Rule(
    name="MulZeroOne",
    fn=_rewrite_mul_zero_one,
    description=(
        "X*0 -> 0, X*1 -> X (and symmetric) for both Mul and IntMul. "
        "Sound for bv-modular and Int."
    ),
)
INT_MUL_EQ_ZERO = Rule(
    name="IntMulEqZero",
    fn=_rewrite_int_mul_eq_zero,
    description=(
        "Eq(IntMul(X, K), 0) -> Eq(X, 0) when K is a nonzero integer "
        "constant. Lookthrough on both Eq operands; restricted to "
        "IntMul (not the modular bv Mul)."
    ),
)
ITE_ZERO_OR_SELF = Rule(
    name="IteZeroOrSelf",
    fn=_rewrite_ite_zero_or_self,
    description=(
        "Ite(Eq(X, 0), 0, X) -> X and Ite(Eq(X, 0), X, 0) -> 0. "
        "Both shapes collapse to the else arm. Lookthrough on cond."
    ),
)
ITE_SAME = Rule(
    name="IteSame",
    fn=_rewrite_ite_same,
    description="Ite(c, X, X) -> X.",
)
ITE_SAME_COND_NESTED = Rule(
    name="IteSameCondNested",
    fn=_rewrite_ite_same_cond_nested,
    description=(
        "Prune a nested Ite re-testing the outer's condition: "
        "Ite(c, X, Ite(c, Y, Z)) -> Ite(c, X, Z) and symmetric."
    ),
)
ITE_SHARED_LEAF = Rule(
    name="IteSharedLeaf",
    fn=_rewrite_ite_shared_leaf,
    description=(
        "Collapse 3-arm Ite where one inner-Ite leaf equals the outer's "
        "other arm: Ite(c, X, Ite(c', Y, X)) -> Ite(¬c ∧ c', Y, X), and "
        "the three other symmetric shapes."
    ),
)
ITE_BOOL = Rule(
    name="IteBool",
    fn=_rewrite_ite_bool,
    description="Collapse Ite with true/false literal branches into bool ops.",
)
ITE_COND_FOLD = Rule(
    name="IteCondFold",
    fn=_rewrite_ite_cond_fold,
    description=(
        "Ite(cond, T, E) -> T when range-inference proves cond is always "
        "true; -> E when always false. Uses infer_expr_range on both sides "
        "of a binary comparison."
    ),
)
BOOL_ABSORB = Rule(
    name="BoolAbsorb",
    fn=_rewrite_bool_absorb,
    description="LOr/LAnd absorb true/false; LNot of true/false/LNot collapses.",
)
DE_MORGAN = Rule(
    name="DeMorgan",
    fn=_rewrite_demorgan,
    description="LOr(!A, !B) -> !LAnd(A, B); dual for LAnd(!A, !B).",
)
