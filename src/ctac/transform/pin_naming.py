"""Corpus-relative block-name shortening for ``ctac pin``.

TAC block IDs are tuples-as-strings like ``146_1_0_0_0_1494`` where most
positions hold a small canonical value (``1_0_0_0`` middle pattern) and
only a handful vary across the corpus. ``shorten_block_names`` finds
which token positions are informative (varying across blocks) and
renders each block keeping only those positions.

Single ``_`` separates consecutive kept positions; ``__`` (double)
marks a gap where one or more positions were dropped as constant —
so ``146_1_0_0_0_1494`` in a corpus where positions 1-4 are constant
becomes ``BLK_146__1494``.

Splitcrit shim blocks (``u_to_v``) are handled by shortening each
half independently against the whole-corpus informative-position
table, then re-joining with ``_to_``.
"""

from __future__ import annotations

from collections.abc import Iterable, Mapping
from dataclasses import dataclass


_SHIM_SEP = "_to_"
_BLK_PREFIX = "BLK_"


def _tokenize(block_id: str) -> tuple[str, ...]:
    """Split a block id into tokens.

    Strips a single leading ``_`` if present (a sanitization artifact
    when ids start with a digit) so it doesn't appear as a constant
    empty token at position 0.
    """
    s = block_id.lstrip("_")
    return tuple(s.split("_")) if s else ()


def _is_shim(block_id: str) -> bool:
    return _SHIM_SEP in block_id


def _split_shim(block_id: str) -> tuple[str, str]:
    u, v = block_id.split(_SHIM_SEP, 1)
    return u, v


def _informative_positions(token_lists: Iterable[tuple[str, ...]]) -> tuple[bool, ...]:
    """For each position i, ``True`` iff multiple distinct values appear
    across the input token lists. Absence (``i >= len(toks)``) counts as
    a distinct ``None`` value.
    """
    lists = list(token_lists)
    if not lists:
        return ()
    max_len = max((len(t) for t in lists), default=0)
    out: list[bool] = []
    for i in range(max_len):
        values: set[str | None] = set()
        for t in lists:
            values.add(t[i] if i < len(t) else None)
        out.append(len(values) > 1)
    return tuple(out)


def _render_kept(tokens: tuple[str, ...], informative: tuple[bool, ...]) -> str:
    """Render the informative-position tokens of ``tokens``, joining
    consecutive kept positions with single ``_`` and gapped kept
    positions with double ``__``.

    Returns the empty string if no positions are informative within
    this token list (caller falls back to the original id).
    """
    parts: list[str] = []
    last_kept = -2  # so first kept position never gets a gap marker
    for i, tok in enumerate(tokens):
        if i >= len(informative) or not informative[i]:
            continue
        sep = "__" if last_kept >= 0 and i > last_kept + 1 else (
            "_" if last_kept >= 0 else ""
        )
        parts.append(sep + tok)
        last_kept = i
    return "".join(parts)


@dataclass(frozen=True)
class BlockNameTable:
    """Bidirectional mapping between full block IDs and short names.

    Shortenings are corpus-relative: adding or removing block IDs from
    the corpus may change the assigned short names. Construct via
    :func:`shorten_block_names`.
    """

    short_by_full: Mapping[str, str]
    full_by_short: Mapping[str, str]

    def short(self, block_id: str) -> str:
        return self.short_by_full[block_id]

    def full(self, short: str) -> str:
        return self.full_by_short[short]

    def all_pairs(self) -> dict[str, str]:
        return dict(self.short_by_full)


def shorten_block_names(block_ids: Iterable[str]) -> BlockNameTable:
    """Compute a corpus-relative short name for each block id.

    Algorithm: gather all token lists (treating splitcrit shim halves
    as separate contributors); compute the informative-position mask;
    render each block keeping only informative positions, with ``__``
    separators across constant gaps.

    Falls back to ``BLK_<full_id>`` for any block whose informative-
    position projection is empty (e.g., a one-block corpus, or a
    block whose tokens are all constant across the corpus). This
    keeps the mapping injective.
    """
    # Dedupe while preserving first-seen order — the same block id mapped
    # twice would otherwise pick up a spurious collision discriminator.
    seen: set[str] = set()
    bids: list[str] = []
    for bid in block_ids:
        if bid not in seen:
            seen.add(bid)
            bids.append(bid)
    if not bids:
        return BlockNameTable(short_by_full={}, full_by_short={})

    # Collect all token lists. Shim halves contribute independently.
    contributors: list[tuple[str, ...]] = []
    for bid in bids:
        if _is_shim(bid):
            u, v = _split_shim(bid)
            contributors.append(_tokenize(u))
            contributors.append(_tokenize(v))
        else:
            contributors.append(_tokenize(bid))

    informative = _informative_positions(contributors)

    short_by_full: dict[str, str] = {}
    used: set[str] = set()
    for bid in bids:
        if _is_shim(bid):
            u, v = _split_shim(bid)
            u_short = _render_kept(_tokenize(u), informative) or u
            v_short = _render_kept(_tokenize(v), informative) or v
            short = f"{_BLK_PREFIX}{u_short}{_SHIM_SEP}{v_short}"
        else:
            rendered = _render_kept(_tokenize(bid), informative)
            short = f"{_BLK_PREFIX}{rendered}" if rendered else f"{_BLK_PREFIX}{bid}"

        # Disambiguate collisions by appending a discriminator. Should be
        # rare given the corpus-relative algorithm, but the renderer's
        # gap-marker collapse can produce ties (e.g. two blocks differing
        # only in dropped positions).
        if short in used:
            i = 2
            while f"{short}#{i}" in used:
                i += 1
            short = f"{short}#{i}"
        used.add(short)
        short_by_full[bid] = short

    full_by_short = {s: f for f, s in short_by_full.items()}
    return BlockNameTable(short_by_full=short_by_full, full_by_short=full_by_short)
