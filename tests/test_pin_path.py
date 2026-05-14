"""Unit tests for ctac.transform.pin_path."""

from __future__ import annotations

import pytest

from ctac.parse import parse_string
from ctac.transform.pin_path import choose_random_path, drop_set_for_path


def _wrap(blocks_text: str, *, syms: str = "B0:bool\n\tB1:bool") -> str:
    return f"""TACSymbolTable {{
\tUserDefined {{
\t}}
\tBuiltinFunctions {{
\t}}
\tUninterpretedFunctions {{
\t}}
\t{syms}
}}
Program {{
{blocks_text}
}}
Axioms {{
}}
Metas {{
  "0": []
}}
"""


# entry → {a, b}; a → {c, d}; b → exit; c → exit; d → exit; exit → ∅.
# Four entry-to-exit paths: e-a-c-exit, e-a-d-exit, e-b-exit (×1),
# e-a-{c,d}-exit when forced through a.
_TAC_RICH = _wrap(
    "\tBlock e Succ [a, b] {\n"
    "\t\tJumpiCmd a b B0\n"
    "\t}\n"
    "\tBlock a Succ [c, d] {\n"
    "\t\tJumpiCmd c d B1\n"
    "\t}\n"
    "\tBlock b Succ [exit] {\n"
    "\t\tJumpCmd exit\n"
    "\t}\n"
    "\tBlock c Succ [exit] {\n"
    "\t\tJumpCmd exit\n"
    "\t}\n"
    "\tBlock d Succ [exit] {\n"
    "\t\tJumpCmd exit\n"
    "\t}\n"
    "\tBlock exit Succ [] {\n"
    "\t\tNoSuchCmd\n"
    "\t}\n"
)


def _program(src: str = _TAC_RICH):
    return parse_string(src, path="<s>").program


def test_choose_random_path_anchor_forces_inclusion():
    """An anchor on a unique-path branch forces that branch."""
    p = _program()
    # Anchor `b`: only one feasible path goes through b → exit.
    path = choose_random_path(p, ("b",), seed=0)
    assert path == ("e", "b", "exit")


def test_choose_random_path_seed_is_deterministic():
    """Same seed → same path on a CFG with branch choices."""
    p = _program()
    a = choose_random_path(p, ("a",), seed=42)
    b = choose_random_path(p, ("a",), seed=42)
    assert a == b
    assert a[0] == "e" and a[1] == "a" and a[-1] == "exit"
    assert a[2] in ("c", "d")


def test_choose_random_path_different_seeds_can_diverge():
    """Across many seeds we should hit both feasible branches at `a`."""
    p = _program()
    second_blocks = {
        choose_random_path(p, ("a",), seed=s)[2] for s in range(20)
    }
    assert second_blocks == {"c", "d"}


def test_choose_random_path_chain_of_anchors():
    """Anchors `a` and `d` force the path through both, in topo order."""
    p = _program()
    path = choose_random_path(p, ("a", "d"), seed=0)
    assert path == ("e", "a", "d", "exit")


def test_choose_random_path_auto_topo_sorts_user_order():
    """User supplies anchors in reverse topo order; auto-sort fixes it."""
    p = _program()
    # `d` before `a` is wrong topo order; auto-sort produces `a, d`.
    path = choose_random_path(p, ("d", "a"), seed=0)
    assert path == ("e", "a", "d", "exit")


def test_choose_random_path_rejects_unknown_anchor():
    p = _program()
    with pytest.raises(ValueError, match="not in program"):
        choose_random_path(p, ("zz",), seed=0)


def test_choose_random_path_rejects_unreachable_anchor_chain():
    """`c` and `d` are both terminal-leading; one cannot reach the other."""
    p = _program()
    # After topo-sort, anchors are (c, d) — neither reachable from the
    # other. Validation should reject.
    with pytest.raises(ValueError, match="not reachable from"):
        choose_random_path(p, ("c", "d"), seed=0)


def test_choose_random_path_entry_as_anchor():
    """Anchor at the entry block is a no-op (already on the path)."""
    p = _program()
    path = choose_random_path(p, ("e",), seed=0)
    assert path[0] == "e"
    assert path[-1] == "exit"


def test_choose_random_path_dedups_anchor_list():
    p = _program()
    path = choose_random_path(p, ("a", "a", "d"), seed=0)
    assert path == ("e", "a", "d", "exit")


def test_drop_set_for_path_returns_source_order():
    p = _program()
    chosen = ("e", "a", "c", "exit")
    dropped = drop_set_for_path(p, chosen)
    # Source-order blocks in _TAC_RICH: e, a, b, c, d, exit. Off-path
    # = b, d.
    assert dropped == ("b", "d")
