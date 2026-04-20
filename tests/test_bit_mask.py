from ctac.ast.bit_mask import shifted_contiguous_mask


def test_shifted_contiguous_mask_example_from_plan() -> None:
    n = 70368744161280
    assert shifted_contiguous_mask(n) == (14, 32)


def test_shifted_contiguous_mask_low_only() -> None:
    assert shifted_contiguous_mask(0xFF) == (0, 8)


def test_shifted_contiguous_mask_single_bit() -> None:
    assert shifted_contiguous_mask(1 << 20) == (20, 1)


def test_shifted_contiguous_mask_rejects_sparse() -> None:
    assert shifted_contiguous_mask(0b1010) is None


def test_shifted_contiguous_mask_rejects_zero() -> None:
    assert shifted_contiguous_mask(0) is None
