"""Unit tests for ``ctac.rewrite.rewrite_u128_decrement``."""

from __future__ import annotations

from ctac.ast.nodes import ApplyExpr, AssignExpCmd, SymbolRef
from ctac.parse import parse_string
from ctac.rewrite.rewrite_u128_decrement import rewrite_u128_decrement


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


def _named_assigns(prog) -> dict[str, AssignExpCmd]:
    out: dict[str, AssignExpCmd] = {}
    for block in prog.blocks:
        for cmd in block.commands:
            if isinstance(cmd, AssignExpCmd):
                out[cmd.lhs] = cmd
    return out


# Canonical decrement chain shape with inline carry Cmps + named B
# (the pre-ITE_PURIFY shape the pass actually runs against).
_BODY_INLINE_TB = (
    "\t\tAssignHavocCmd H\n"
    "\t\tAssumeExpCmd Ge(H 0x1)\n"
    "\t\tAssumeExpCmd Le(H 0xffffffffffffffffffffffffffffffff)\n"
    "\t\tAssignExpCmd Lo Mod(H 0x10000000000000000)\n"
    "\t\tAssignExpCmd Hi Div(H 0x10000000000000000)\n"
    "\t\tAssignExpCmd Blo Eq(Lo 0x0)\n"
    "\t\tAssignExpCmd Bhi Eq(Hi 0x0)\n"
    "\t\tAssumeExpCmd LNot(LAnd(Blo Bhi))\n"
    "\t\tAssignExpCmd Rhi_dec Ite(Blo Sub(Hi 0x1) Hi)\n"
    "\t\tAssignExpCmd Rlo_dec "
    "Ite(Ge(Lo 0x1) IntSub(Lo 0x1) 0xffffffffffffffff)\n"
    "\t\tAssertCmd Le(Rlo_dec 0xffffffffffffffff)\n"
)
_SYMS = (
    "H:bv256\n\tLo:bv256\n\tHi:bv256\n\tBlo:bool\n\tBhi:bool\n"
    "\tRhi_dec:bv256\n\tRlo_dec:bv256"
)


def test_chain_rewritten_to_h_sub_one():
    """The full chain collapses to ``H_new = Sub(H, 1)`` plus chunk
    extracts, with the LNot(LAnd) assume dropped."""
    tac = parse_string(_wrap(_BODY_INLINE_TB, syms=_SYMS), path="<s>")
    res = rewrite_u128_decrement(
        tac.program, symbol_sorts=tac.symbol_sorts
    )
    assert res.hits == 1
    # A fresh H<N> register is allocated.
    assert len(res.fresh_symbols) == 1
    h_new_name, sort = res.fresh_symbols[0]
    assert sort == "bv256"
    assert h_new_name.startswith("H")
    cmds = _named_assigns(res.program)
    # H_new = Sub(H, 1).
    h_new_rhs = cmds[h_new_name].rhs
    assert isinstance(h_new_rhs, ApplyExpr) and h_new_rhs.op == "Sub"
    assert h_new_rhs.args[0] == SymbolRef("H")
    # Rhi_dec, Rlo_dec are bv chunks of H_new.
    rhi_rhs = cmds["Rhi_dec"].rhs
    assert isinstance(rhi_rhs, ApplyExpr) and rhi_rhs.op == "Div"
    assert rhi_rhs.args[0] == SymbolRef(h_new_name)
    rlo_rhs = cmds["Rlo_dec"].rhs
    assert isinstance(rlo_rhs, ApplyExpr) and rlo_rhs.op == "Mod"
    assert rlo_rhs.args[0] == SymbolRef(h_new_name)


def test_drops_lnot_assume():
    """The redundant ``LNot(LAnd(B_lo, B_hi))`` assume gets dropped."""
    from ctac.ast.nodes import AssumeExpCmd

    tac = parse_string(_wrap(_BODY_INLINE_TB, syms=_SYMS), path="<s>")
    res = rewrite_u128_decrement(
        tac.program, symbol_sorts=tac.symbol_sorts
    )
    for block in res.program.blocks:
        for cmd in block.commands:
            if not isinstance(cmd, AssumeExpCmd):
                continue
            cond = cmd.condition
            assert not (
                isinstance(cond, ApplyExpr) and cond.op == "LNot"
            ), "LNot(LAnd) assume should have been dropped"


def test_no_h_lower_bound_skips():
    """Without ``Ge(H, 1)`` in scope (range gate fails) the pass
    refuses to fire — bv ``Sub(H, 1)`` would wrap at H=0."""
    body = (
        "\t\tAssignHavocCmd H\n"
        # No Ge(H, 1) assume — range gate fails.
        "\t\tAssignExpCmd Lo Mod(H 0x10000000000000000)\n"
        "\t\tAssignExpCmd Hi Div(H 0x10000000000000000)\n"
        "\t\tAssignExpCmd Blo Eq(Lo 0x0)\n"
        "\t\tAssignExpCmd Bhi Eq(Hi 0x0)\n"
        "\t\tAssumeExpCmd LNot(LAnd(Blo Bhi))\n"
        "\t\tAssignExpCmd Rhi_dec Ite(Blo Sub(Hi 0x1) Hi)\n"
        "\t\tAssignExpCmd Rlo_dec "
        "Ite(Ge(Lo 0x1) IntSub(Lo 0x1) 0xffffffffffffffff)\n"
        "\t\tAssertCmd Le(Rlo_dec 0xffffffffffffffff)\n"
    )
    tac = parse_string(_wrap(body, syms=_SYMS), path="<s>")
    res = rewrite_u128_decrement(
        tac.program, symbol_sorts=tac.symbol_sorts
    )
    # H's lower bound is 0 (no assume), so the gate fails.
    assert res.hits == 0
