"""Unit tests for ``ctac.rewrite.materialize_h_nonzero``."""

from __future__ import annotations

from ctac.ast.nodes import (
    ApplyExpr,
    AssumeExpCmd,
    ConstExpr,
    SymbolRef,
)
from ctac.parse import parse_string
from ctac.rewrite.materialize_h_nonzero import materialize_h_nonzero


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


_BODY = (
    "\t\tAssignHavocCmd H\n"
    "\t\tAssignExpCmd Lo Mod(H 0x10000000000000000)\n"
    "\t\tAssignExpCmd Hi Div(H 0x10000000000000000)\n"
    "\t\tAssignExpCmd Blo Eq(Lo 0x0)\n"
    "\t\tAssignExpCmd Bhi Eq(Hi 0x0)\n"
    "\t\tAssumeExpCmd LNot(LAnd(Blo Bhi))\n"
    "\t\tAssertCmd Le(Lo 0xffffffffffffffff)\n"
)
_SYMS = "H:bv256\n\tLo:bv256\n\tHi:bv256\n\tBlo:bool\n\tBhi:bool"


def test_materializes_ge_h_one():
    """The pass adds ``assume Ge(H, 1)`` after the LNot(LAnd) assume."""
    tac = parse_string(_wrap(_BODY, syms=_SYMS), path="<s>")
    res = materialize_h_nonzero(tac.program, symbol_sorts=tac.symbol_sorts)
    assert res.hits == 1
    # The new assume should follow the original LNot(LAnd) assume.
    cmds = list(res.program.blocks[0].commands)
    lnot_idx = None
    ge_idx = None
    for i, c in enumerate(cmds):
        if not isinstance(c, AssumeExpCmd):
            continue
        cond = c.condition
        if isinstance(cond, ApplyExpr) and cond.op == "LNot":
            lnot_idx = i
        if (
            isinstance(cond, ApplyExpr)
            and cond.op == "Ge"
            and len(cond.args) == 2
            and cond.args[0] == SymbolRef("H")
            and isinstance(cond.args[1], ConstExpr)
        ):
            ge_idx = i
    assert lnot_idx is not None and ge_idx is not None
    assert ge_idx == lnot_idx + 1


def test_idempotent():
    """Running the pass twice produces no further hits."""
    tac = parse_string(_wrap(_BODY, syms=_SYMS), path="<s>")
    once = materialize_h_nonzero(tac.program, symbol_sorts=tac.symbol_sorts)
    twice = materialize_h_nonzero(once.program, symbol_sorts=tac.symbol_sorts)
    assert twice.hits == 0


def test_skip_when_chunks_belong_to_different_H():
    """Two different H sources: chunks of A and B; pass abstains."""
    body = (
        "\t\tAssignHavocCmd A\n"
        "\t\tAssignHavocCmd B\n"
        "\t\tAssignExpCmd Lo Mod(A 0x10000000000000000)\n"
        "\t\tAssignExpCmd Hi Div(B 0x10000000000000000)\n"
        "\t\tAssignExpCmd Blo Eq(Lo 0x0)\n"
        "\t\tAssignExpCmd Bhi Eq(Hi 0x0)\n"
        "\t\tAssumeExpCmd LNot(LAnd(Blo Bhi))\n"
        "\t\tAssertCmd Le(Lo 0xffffffffffffffff)\n"
    )
    syms = (
        "A:bv256\n\tB:bv256\n\tLo:bv256\n\tHi:bv256\n\t"
        "Blo:bool\n\tBhi:bool"
    )
    tac = parse_string(_wrap(body, syms=syms), path="<s>")
    res = materialize_h_nonzero(tac.program, symbol_sorts=tac.symbol_sorts)
    assert res.hits == 0


def test_skip_when_chunks_not_mod_div():
    """If the chunks aren't of the expected ``Mod(H, 2^64)`` /
    ``Div(H, 2^64)`` form, the pass skips."""
    body = (
        "\t\tAssignHavocCmd H\n"
        "\t\tAssignExpCmd Lo BWAnd(H 0xff)\n"
        "\t\tAssignExpCmd Hi Div(H 0x10000000000000000)\n"
        "\t\tAssignExpCmd Blo Eq(Lo 0x0)\n"
        "\t\tAssignExpCmd Bhi Eq(Hi 0x0)\n"
        "\t\tAssumeExpCmd LNot(LAnd(Blo Bhi))\n"
        "\t\tAssertCmd Le(Lo 0xffffffffffffffff)\n"
    )
    tac = parse_string(_wrap(body, syms=_SYMS), path="<s>")
    res = materialize_h_nonzero(tac.program, symbol_sorts=tac.symbol_sorts)
    assert res.hits == 0
