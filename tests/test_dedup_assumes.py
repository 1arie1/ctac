"""Unit tests for ``ctac.rewrite.dedup_assumes``."""

from __future__ import annotations

from ctac.ast.nodes import AssumeExpCmd
from ctac.parse import parse_string
from ctac.rewrite.dedup_assumes import dedup_assumes


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


def _assumes(prog):
    return [
        cmd.condition
        for b in prog.blocks
        for cmd in b.commands
        if isinstance(cmd, AssumeExpCmd)
    ]


def test_verbatim_duplicate_dropped():
    body = (
        "\t\tAssignHavocCmd X\n"
        "\t\tAssumeExpCmd Le(X 0xff)\n"
        "\t\tAssumeExpCmd Le(X 0xff)\n"
    )
    tac = parse_string(_wrap(body, syms="X:bv256"), path="<s>")
    res = dedup_assumes(tac.program)
    assert res.duplicates_dropped == 1
    assert len(_assumes(res.program)) == 1


def test_flipped_orientation_duplicate_dropped():
    """``X <= Y`` then ``Y >= X``: one fact, two spellings."""
    body = (
        "\t\tAssignHavocCmd X\n"
        "\t\tAssignHavocCmd Y\n"
        "\t\tAssumeExpCmd Le(X Y)\n"
        "\t\tAssumeExpCmd Ge(Y X)\n"
    )
    tac = parse_string(_wrap(body, syms="X:bv256\n\tY:bv256"), path="<s>")
    res = dedup_assumes(tac.program)
    assert res.duplicates_dropped == 1


def test_meta_suffix_duplicate_dropped():
    body = (
        "\t\tAssignHavocCmd X\n"
        "\t\tAssumeExpCmd Le(X:20 0xff)\n"
        "\t\tAssumeExpCmd Le(X 0xff)\n"
    )
    tac = parse_string(_wrap(body, syms="X:bv256"), path="<s>")
    res = dedup_assumes(tac.program)
    assert res.duplicates_dropped == 1


def test_resolution_pair_collapses_to_payload():
    """(!B | P) and (B | P) resolve to P."""
    body = (
        "\t\tAssignHavocCmd X\n"
        "\t\tAssignHavocCmd Y\n"
        "\t\tAssignExpCmd B Eq(X 0x0)\n"
        "\t\tAssumeExpCmd LOr(LNot(B) Eq(Y 0x5))\n"
        "\t\tAssumeExpCmd LOr(B Eq(Y 0x5))\n"
    )
    tac = parse_string(
        _wrap(body, syms="X:bv256\n\tY:bv256\n\tB:bool"), path="<s>"
    )
    res = dedup_assumes(tac.program)
    assert res.pairs_resolved == 1
    conds = _assumes(res.program)
    assert len(conds) == 1
    assert conds[0].op == "Eq"


def test_resolution_pair_comparison_complement():
    """(Lt(X, Y) | P) and (Ge(X, Y) | P) resolve via comparison
    complement (Ge flip-normalizes to Le, !Lt == flipped Le)."""
    body = (
        "\t\tAssignHavocCmd X\n"
        "\t\tAssignHavocCmd Y\n"
        "\t\tAssignHavocCmd Z\n"
        "\t\tAssumeExpCmd LOr(Lt(X Y) Eq(Z 0x1))\n"
        "\t\tAssumeExpCmd LOr(Ge(X Y) Eq(Z 0x1))\n"
    )
    tac = parse_string(
        _wrap(body, syms="X:bv256\n\tY:bv256\n\tZ:bv256"), path="<s>"
    )
    res = dedup_assumes(tac.program)
    assert res.pairs_resolved == 1
    conds = _assumes(res.program)
    assert len(conds) == 1
    assert conds[0].op == "Eq"


def test_different_payloads_no_resolution():
    body = (
        "\t\tAssignHavocCmd X\n"
        "\t\tAssignHavocCmd Y\n"
        "\t\tAssignExpCmd B Eq(X 0x0)\n"
        "\t\tAssumeExpCmd LOr(LNot(B) Eq(Y 0x5))\n"
        "\t\tAssumeExpCmd LOr(B Eq(Y 0x6))\n"
    )
    tac = parse_string(
        _wrap(body, syms="X:bv256\n\tY:bv256\n\tB:bool"), path="<s>"
    )
    res = dedup_assumes(tac.program)
    assert res.pairs_resolved == 0
    assert len(_assumes(res.program)) == 2


def test_redefinition_invalidates_duplicate():
    """A def of a read symbol between the two occurrences makes the
    second a different fact — kept."""
    body = (
        "\t\tAssignHavocCmd Y\n"
        "\t\tAssignExpCmd X Add(Y 0x1)\n"
        "\t\tAssumeExpCmd Le(X 0xff)\n"
        "\t\tAssignExpCmd X Add(Y 0x2)\n"
        "\t\tAssumeExpCmd Le(X 0xff)\n"
    )
    tac = parse_string(_wrap(body, syms="X:bv256\n\tY:bv256"), path="<s>")
    res = dedup_assumes(tac.program)
    assert res.duplicates_dropped == 0
    assert len(_assumes(res.program)) == 2


def test_resolvent_serializes_canonically():
    """The replaced assume's raw text is rebuilt (stale raw would
    round-trip the old guarded condition)."""
    body = (
        "\t\tAssignHavocCmd X\n"
        "\t\tAssignHavocCmd Y\n"
        "\t\tAssignExpCmd B Eq(X 0x0)\n"
        "\t\tAssumeExpCmd LOr(LNot(B) Eq(Y 0x5))\n"
        "\t\tAssumeExpCmd LOr(B Eq(Y 0x5))\n"
    )
    tac = parse_string(
        _wrap(body, syms="X:bv256\n\tY:bv256\n\tB:bool"), path="<s>"
    )
    res = dedup_assumes(tac.program)
    kept = next(
        cmd
        for b in res.program.blocks
        for cmd in b.commands
        if isinstance(cmd, AssumeExpCmd)
    )
    assert "LOr" not in kept.raw
