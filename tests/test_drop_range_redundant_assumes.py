"""Unit tests for ``ctac.rewrite.drop_range_redundant_assumes``."""

from __future__ import annotations

from ctac.ast.nodes import AssumeExpCmd
from ctac.parse import parse_string
from ctac.rewrite.drop_range_redundant_assumes import (
    drop_range_redundant_assumes,
)


def _wrap(body: str, *, syms: str) -> str:
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
\tBlock e Succ [] {{
{body}
\t}}
}}
Axioms {{
}}
Metas {{
  "0": []
}}
"""


def _assume_count(prog):
    return sum(
        1
        for b in prog.blocks
        for cmd in b.commands
        if isinstance(cmd, AssumeExpCmd)
    )


def test_drops_le_when_range_proves_it():
    """``assume Le(X, 0xff)`` with X provably ≤ 0xff drops."""
    body = (
        "\t\tAssignHavocCmd X\n"
        "\t\tAssumeExpCmd Le(X 0xff)\n"   # tight bound (load-bearing)
        "\t\tAssumeExpCmd Le(X 0xffff)\n"  # redundant: tighter bound above
        "\t\tAssertCmd false\n"
    )
    tac = parse_string(_wrap(body, syms="X:bv256"), path="<s>")
    res = drop_range_redundant_assumes(
        tac.program, symbol_sorts=tac.symbol_sorts
    )
    assert res.hits == 1
    # The 0xff assume stays; the redundant 0xffff one is dropped.
    assert _assume_count(res.program) == 1


def test_drops_ge_when_range_proves_it():
    """``assume Ge(X, 0)`` is trivially true for bv256 sort."""
    body = (
        "\t\tAssignHavocCmd X\n"
        "\t\tAssumeExpCmd Ge(X 0x0)\n"
        "\t\tAssertCmd false\n"
    )
    tac = parse_string(_wrap(body, syms="X:bv256"), path="<s>")
    res = drop_range_redundant_assumes(
        tac.program, symbol_sorts=tac.symbol_sorts
    )
    assert res.hits == 1


def test_drops_lt_strict():
    """``assume Lt(X, 0x100)`` with X provably ≤ 0xff (hence < 0x100)."""
    body = (
        "\t\tAssignHavocCmd X\n"
        "\t\tAssumeExpCmd Le(X 0xff)\n"
        "\t\tAssumeExpCmd Lt(X 0x100)\n"
        "\t\tAssertCmd false\n"
    )
    tac = parse_string(_wrap(body, syms="X:bv256"), path="<s>")
    res = drop_range_redundant_assumes(
        tac.program, symbol_sorts=tac.symbol_sorts
    )
    assert res.hits == 1


def test_keeps_non_redundant():
    """A real bound that range inference can't already prove stays."""
    body = (
        "\t\tAssignHavocCmd X\n"
        "\t\tAssumeExpCmd Le(X 0xff)\n"
        "\t\tAssertCmd false\n"
    )
    tac = parse_string(_wrap(body, syms="X:bv256"), path="<s>")
    res = drop_range_redundant_assumes(
        tac.program, symbol_sorts=tac.symbol_sorts
    )
    # The Le(X, 0xff) is the source of X's tight bound; bv256 sort
    # alone gives [0, 2^256-1] which exceeds 0xff. So the assume is
    # the load-bearing constraint and must stay.
    assert res.hits == 0


def test_keeps_non_const_rhs():
    """``assume Le(X, Y)`` with symbolic Y: pass doesn't handle
    relational facts, abstains."""
    body = (
        "\t\tAssignHavocCmd X\n"
        "\t\tAssignHavocCmd Y\n"
        "\t\tAssumeExpCmd Le(X Y)\n"
        "\t\tAssertCmd false\n"
    )
    tac = parse_string(_wrap(body, syms="X:bv256\n\tY:bv256"), path="<s>")
    res = drop_range_redundant_assumes(
        tac.program, symbol_sorts=tac.symbol_sorts
    )
    assert res.hits == 0


def test_idempotent():
    """Running twice produces no further hits."""
    body = (
        "\t\tAssignHavocCmd X\n"
        "\t\tAssumeExpCmd Le(X 0xff)\n"
        "\t\tAssumeExpCmd Le(X 0xffff)\n"
        "\t\tAssertCmd false\n"
    )
    tac = parse_string(_wrap(body, syms="X:bv256"), path="<s>")
    once = drop_range_redundant_assumes(
        tac.program, symbol_sorts=tac.symbol_sorts
    )
    twice = drop_range_redundant_assumes(
        once.program, symbol_sorts=tac.symbol_sorts
    )
    assert twice.hits == 0


def test_drops_literal_true_assume():
    """``assume true`` (left behind by condition folding) drops;
    ``assume false`` is load-bearing and stays."""
    body = (
        "\t\tAssignHavocCmd X\n"
        "\t\tAssumeExpCmd true\n"
        "\t\tAssumeExpCmd false\n"
        "\t\tAssertCmd false\n"
    )
    tac = parse_string(_wrap(body, syms="X:bv256"), path="<s>")
    res = drop_range_redundant_assumes(
        tac.program, symbol_sorts=tac.symbol_sorts
    )
    assert res.hits == 1
    assert _assume_count(res.program) == 1
