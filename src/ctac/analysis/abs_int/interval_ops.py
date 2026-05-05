"""Pure integer-interval arithmetic for the abs_int interval domain.

Both the rewriter (`ctac.rewrite.range_infer`) and the abs_int interval
domain compute operand intervals from their own contexts, then call the
primitives here. The math is pure: every function takes `Interval`s and
returns an `Interval`.

`None` for `lo` / `hi` denotes -inf / +inf; `Interval(None, None)` is
TOP. An empty intersection (lo > hi) is the BOT case the caller checks
for and treats as unreachable.
"""

from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class Interval:
    lo: int | None
    hi: int | None

    def is_top(self) -> bool:
        return self.lo is None and self.hi is None

    def is_bot(self) -> bool:
        return self.lo is not None and self.hi is not None and self.lo > self.hi

    def is_nonneg(self) -> bool:
        return self.lo is not None and self.lo >= 0

    def is_concrete(self) -> bool:
        return self.lo is not None and self.hi is not None


TOP = Interval(None, None)


def point(k: int) -> Interval:
    return Interval(k, k)


def bv_width_iv(width: int) -> Interval:
    return Interval(0, (1 << width) - 1)


def bool_iv() -> Interval:
    return Interval(0, 1)


def from_pair(p: tuple[int | None, int | None] | None) -> Interval:
    if p is None:
        return TOP
    return Interval(p[0], p[1])


def to_pair_strict(i: Interval) -> tuple[int, int] | None:
    """Tuple form preserving the rewriter's `infer_expr_range` API:
    only returns a pair when both bounds are concrete ints."""
    if i.lo is None or i.hi is None:
        return None
    return (i.lo, i.hi)


def meet(a: Interval, b: Interval) -> Interval:
    if a.lo is None:
        lo = b.lo
    elif b.lo is None:
        lo = a.lo
    else:
        lo = max(a.lo, b.lo)
    if a.hi is None:
        hi = b.hi
    elif b.hi is None:
        hi = a.hi
    else:
        hi = min(a.hi, b.hi)
    return Interval(lo, hi)


def join(a: Interval, b: Interval) -> Interval:
    """Convex-hull join. TOP absorbs."""
    lo = None if a.lo is None or b.lo is None else min(a.lo, b.lo)
    hi = None if a.hi is None or b.hi is None else max(a.hi, b.hi)
    return Interval(lo, hi)


def bv_clamp(interval: Interval, width: int) -> Interval:
    """Clamp an unwrapped-Int interval into the bv-``width`` domain
    ``[0, 2^width - 1]``. If ``interval`` already fits, return it
    unchanged — the bv result equals the unwrapped interval. For a
    singleton outside the bv range the precise wrapped value is
    ``v mod 2^width``, so return that as a point. Otherwise return
    the full bv range, the smallest sound overapproximation across
    the wraparound.

    Use this whenever lifting a bv``width`` op (e.g. TAC ``Add``,
    ``Sub``, ``Mul``) — the underlying ``add``/``sub``/``mul_nonneg``
    primitives compute in unbounded Int and would otherwise let
    constant folds escape the bv domain (e.g. ``Add(1, BV256_MAX)``
    folding to ``2^256``)."""
    bound = (1 << width) - 1
    if (
        interval.lo is not None
        and interval.lo >= 0
        and interval.hi is not None
        and interval.hi <= bound
    ):
        return interval
    if (
        interval.lo is not None
        and interval.hi is not None
        and interval.lo == interval.hi
    ):
        # Singleton outside the bv range: wrap precisely. Python's ``%``
        # returns a non-negative result for any sign of the dividend, so
        # this is sound for negative singletons (e.g. ``Sub(0, 1)``
        # unwrapped to -1) too.
        return point(interval.lo % (bound + 1))
    return bv_width_iv(width)


def add(a: Interval, b: Interval) -> Interval:
    lo = None if a.lo is None or b.lo is None else a.lo + b.lo
    hi = None if a.hi is None or b.hi is None else a.hi + b.hi
    return Interval(lo, hi)


def sub(a: Interval, b: Interval) -> Interval:
    lo = None if a.lo is None or b.hi is None else a.lo - b.hi
    hi = None if a.hi is None or b.lo is None else a.hi - b.lo
    return Interval(lo, hi)


def mul_nonneg(a: Interval, b: Interval) -> Interval | None:
    """Multiply two non-negative intervals. `None` when either operand
    isn't proved non-negative — caller falls back to TOP."""
    if not a.is_nonneg() or not b.is_nonneg():
        return None
    assert a.lo is not None and b.lo is not None
    lo = a.lo * b.lo
    hi = None if a.hi is None or b.hi is None else a.hi * b.hi
    return Interval(lo, hi)


def floor_div_by_pos_const(a: Interval, k: int) -> Interval | None:
    """`floor(a / k)` for positive constant `k`, non-negative numerator."""
    if k <= 0 or not a.is_nonneg():
        return None
    assert a.lo is not None
    lo = a.lo // k
    hi = None if a.hi is None else a.hi // k
    return Interval(lo, hi)


def mod_by_pos_const(a: Interval, k: int) -> Interval | None:
    """`a mod k` for positive constant `k`.

    When `a` is provably in `[0, k)` the mod is identity (returns `a`).
    Otherwise `[0, k - 1]`.
    """
    if k <= 0:
        return None
    if a.is_nonneg() and a.hi is not None and a.hi < k:
        return a
    return Interval(0, k - 1)


def ceil_div_nonneg(a: Interval, b: Interval) -> Interval | None:
    """`ceil(a / b)` for non-negative `a` and strictly positive `b`.

    Returns `None` when soundness conditions don't hold (negative `a`,
    non-positive `b`, or unbounded operands).
    """
    if (
        not a.is_nonneg()
        or b.lo is None
        or b.lo <= 0
        or a.hi is None
        or b.hi is None
    ):
        return None
    assert a.lo is not None
    a_lo, a_hi = a.lo, a.hi
    b_lo, b_hi = b.lo, b.hi
    lo = (a_lo + b_hi - 1) // b_hi if a_lo > 0 else 0
    hi = (a_hi + b_lo - 1) // b_lo
    return Interval(lo, hi)


def narrow_clamp(inner: Interval, width: int) -> Interval | None:
    """`safe_math_narrow_bvN(inner)` succeeds as identity when
    `inner ⊆ [0, 2^N - 1]`; otherwise returns `None` (failure)."""
    if inner.is_nonneg() and inner.hi is not None and inner.hi <= (1 << width) - 1:
        return inner
    return None
