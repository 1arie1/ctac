"""Tests for ctac.transform.pin_naming."""

from __future__ import annotations

from ctac.transform.pin_naming import (
    BlockNameTable,
    shorten_block_names,
    _informative_positions,
    _render_kept,
    _tokenize,
)


def test_empty_corpus():
    t = shorten_block_names([])
    assert t.short_by_full == {}
    assert t.full_by_short == {}


def test_simple_corpus_drops_constant_middle():
    """User's canonical example: 1_0_0_0 / 2_0_0_0 -> BLK_1 / BLK_2."""
    t = shorten_block_names(["1_0_0_0", "2_0_0_0"])
    assert t.short("1_0_0_0") == "BLK_1"
    assert t.short("2_0_0_0") == "BLK_2"


def test_corpus_with_varied_suffix_uses_double_underscore():
    """1_0_0_0_345 alongside 1_0_0_0 / 2_0_0_0 -> BLK_1__345."""
    t = shorten_block_names(["1_0_0_0", "2_0_0_0", "1_0_0_0_345"])
    assert t.short("1_0_0_0_345") == "BLK_1__345"
    # Bare 1_0_0_0 still BLK_1 since position 4 absence is informative
    assert t.short("1_0_0_0") == "BLK_1"
    assert t.short("2_0_0_0") == "BLK_2"


def test_real_tac_block_id_corpus():
    """Mirrors the actual corpus shape from request_elevation_group."""
    corpus = [
        "1_1_0_0_0_0",
        "2_1_0_0_0_0",
        "5_1_0_0_0_0",
        "5_1_0_0_0_3425",
        "146_1_0_0_0_1494",
        "87_1_0_0_0_0",
    ]
    t = shorten_block_names(corpus)
    # Position 5 varies (0, 0, 0, 3425, 1494, 0), position 0 varies.
    # Positions 1-4 are constant (1, 0, 0, 0) — dropped.
    assert t.short("1_1_0_0_0_0") == "BLK_1__0"
    assert t.short("5_1_0_0_0_3425") == "BLK_5__3425"
    assert t.short("146_1_0_0_0_1494") == "BLK_146__1494"


def test_shim_block_handled_per_half():
    """Splitcrit shim u_to_v: each half shortened independently."""
    corpus = [
        "146_1_0_0_0_1494",
        "149_1_0_0_0_3420",
        "146_1_0_0_0_1494_to_149_1_0_0_0_3420",
    ]
    t = shorten_block_names(corpus)
    assert t.short("146_1_0_0_0_1494_to_149_1_0_0_0_3420") == \
        "BLK_146__1494_to_149__3420"


def test_table_is_bidirectional():
    t = shorten_block_names(["1_0_0_0", "2_0_0_0"])
    assert t.full(t.short("1_0_0_0")) == "1_0_0_0"
    assert t.full("BLK_2") == "2_0_0_0"


def test_all_pairs_returns_full_to_short_mapping():
    t = shorten_block_names(["1_0_0_0", "2_0_0_0"])
    pairs = t.all_pairs()
    assert pairs == {"1_0_0_0": "BLK_1", "2_0_0_0": "BLK_2"}


def test_single_block_corpus_uses_full_id():
    """Degenerate: nothing varies, so falls back to BLK_<full_id>."""
    t = shorten_block_names(["1_0_0_0"])
    assert t.short("1_0_0_0") == "BLK_1_0_0_0"


def test_blocks_all_identical_handled():
    t = shorten_block_names(["a_b", "a_b"])
    # Same id appears twice in input; should map to same short, no collision.
    assert t.short("a_b") == "BLK_a_b"


def test_collision_fallback_disambiguates():
    """If two distinct fulls render to the same short, they get
    discriminator suffixes."""
    # Forge a corpus where the renderer collapses two distinct ids
    # to the same short. Hard to produce naturally; the most likely
    # case is when the leading underscore differs but tokens match.
    # Use stripped vs unstripped form (both _tokenize the same way).
    t = shorten_block_names(["_x", "x"])
    shorts = set(t.short_by_full.values())
    assert len(shorts) == 2  # collision avoided


def test_leading_underscore_stripped_in_tokenization():
    assert _tokenize("_146_1_0_0_0_1494") == ("146", "1", "0", "0", "0", "1494")
    assert _tokenize("146_1_0_0_0_1494") == ("146", "1", "0", "0", "0", "1494")
    assert _tokenize("") == ()
    assert _tokenize("_") == ()


def test_informative_positions_basic():
    lists = [("1", "0", "0"), ("2", "0", "0"), ("3", "0", "0")]
    assert _informative_positions(lists) == (True, False, False)


def test_informative_positions_with_absence():
    lists = [("1", "0", "0"), ("2", "0"), ("3", "0", "0", "x")]
    # pos 0: {1,2,3} — informative; pos 1: {0,0,0} — constant
    # pos 2: {0, None, 0} — informative (absence vs presence)
    # pos 3: {None, None, x} — informative
    info = _informative_positions(lists)
    assert info == (True, False, True, True)


def test_render_kept_consecutive_uses_single_underscore():
    info = (True, True, True)
    assert _render_kept(("a", "b", "c"), info) == "a_b_c"


def test_render_kept_gapped_uses_double_underscore():
    info = (True, False, False, True)
    assert _render_kept(("a", "0", "0", "b"), info) == "a__b"


def test_render_kept_returns_empty_when_no_informative():
    info = (False, False)
    assert _render_kept(("0", "0"), info) == ""


def test_block_name_table_is_frozen_dataclass():
    """Sanity: BlockNameTable is hashable / immutable interface."""
    t = shorten_block_names(["a"])
    assert isinstance(t, BlockNameTable)
    # Frozen dataclass — fields not directly settable
    try:
        t.short_by_full = {}  # type: ignore[misc]
        raised = False
    except Exception:
        raised = True
    assert raised
