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


def low_mask_width(n: int) -> int | None:
    """If ``n == 2^w - 1`` for ``w >= 0``, return ``w``.

    Example: ``0xff`` is the low 8-bit mask, returns ``8``.
    """
    if n < 0:
        return None
    x = n + 1
    if x <= 0:
        return None
    if x & (x - 1) != 0:
        return None
    return x.bit_length() - 1


def high_mask_clear_low_k(n: int, *, width: int = 256) -> int | None:
    """If ``n == (2^width - 2^k)`` for ``k >= 0`` (mask clearing low ``k`` bits), return ``k``.

    ``width`` defaults to 256 to match sea_vc's historical use. The mask pattern is:
    all bits set except the low ``k``.
    """
    if n < 0 or n >= (1 << width):
        return None
    diff = (1 << width) - n
    if diff <= 0:
        return None
    if diff & (diff - 1) != 0:
        return None
    return diff.bit_length() - 1
