"""Recognize contiguous bit masks used in TAC (e.g. BWAnd with a shifted run of 1 bits)."""


def shifted_contiguous_mask(n: int) -> tuple[int, int] | None:
    """
    If ``n == ((1 << w) - 1) << lo`` for some ``w >= 1`` and ``lo >= 0``, return ``(lo, w)``.

    Otherwise return ``None``. Unshifted low masks (``lo == 0``) are included so callers
    can distinguish ``(0, w)`` from non-masks; pretty-print and sea_vc only use ``lo > 0``
    for the shifted slice / div-mod-mul lowering.
    """
    if n <= 0:
        return None
    low = n & -n
    lo = low.bit_length() - 1
    shifted = n >> lo
    if shifted == 0:
        return None
    w = shifted.bit_length()
    if shifted != (1 << w) - 1:
        return None
    return (lo, w)
