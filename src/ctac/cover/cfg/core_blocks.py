"""Project a z3 unsat-core back to TAC block IDs.

`ctac smt --unsat-core` emits named asserts of the shape
``_<block_id>__<idx>_<kind>`` for facts attributable to a specific
block (assumes, static defs, lemmas) plus a few universal axioms
(``bytemap_select_range_*``, ``dynamic_def_*``) that have no block id
and are skipped here.

When the cover-singleton path returns UNSAT with a core, the union
of block IDs the core mentions is the *minimal block set whose
conjunction makes the path infeasible*. The cover uses that set as
a *forbid clause* in the completeness probe: any future path
containing the same block set is also infeasible, so we don't need
to enumerate its equivalents one-by-one.
"""
from __future__ import annotations

import re

from ctac.ir.models import NBId


# Named asserts in ctac smt2 look like:
#   _<block_id>__<idx>_<kind>
# where <block_id> is 6 underscore-separated decimals (e.g.
# "0_0_0_0_0_0"). The `__` doubled-underscore separates the block
# id from the local index + kind tag.
_NAMED_RE = re.compile(r'_(\d+(?:_\d+){5})__')


def parse_core(stdout: str) -> list[str]:
    """Parse the `(get-unsat-core)` response from z3's stdout.

    z3 emits the core as a list of names inside parentheses on its
    own line. Bare names contain no whitespace; we tolerate optional
    surrounding whitespace and newlines."""
    # Find the core block: first top-level `(...)` after `unsat`.
    s = stdout
    i = s.find('(', s.find('unsat'))
    if i < 0:
        return []
    depth = 0
    j = i
    while j < len(s):
        c = s[j]
        if c == '(':
            depth += 1
        elif c == ')':
            depth -= 1
            if depth == 0:
                break
        j += 1
    inner = s[i + 1:j]
    return [name for name in inner.split() if name]


def core_to_blocks(core_names: list[str]) -> set[NBId]:
    """Extract block IDs from a list of named-assert names.

    Universal axioms (no block id in their name) are skipped silently.
    The returned set is the union of block ids referenced anywhere
    in the core."""
    out: set[NBId] = set()
    for name in core_names:
        m = _NAMED_RE.search(name)
        if m:
            out.add(m.group(1))
    return out


def core_blocks_from_stdout(stdout: str) -> set[NBId]:
    """Convenience: parse + project in one call."""
    return core_to_blocks(parse_core(stdout))
