"""Unit tests for ``ctac.rewrite.rewrite_u128_carry_add``."""

from __future__ import annotations

from ctac.ast.nodes import (
    ApplyExpr,
    AssignExpCmd,
    AssumeExpCmd,
    SymbolRef,
)
from ctac.parse import parse_string
from ctac.rewrite.rewrite_u128_carry_add import rewrite_u128_carry_add


def _wrap(body: str, *, syms: str) -> str:
    return f"""TACSymbolTable {{
\tUserDefined {{
\t}}
\tBuiltinFunctions {{
\t\tsafe_math_narrow_bv256:JSON{{"#class":"vc.data.TACBuiltInFunction.SafeMathNarrow.Implicit","returnSort":{{"bits":256}}}}
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


# The canonical post-simplify SBF carry-add shape used by these tests:
#
#   R_lo, R_b   = u64 inputs
#   BASE        = u64 high-half input
#   R_sum       = narrow(IntAdd(R_lo, R_b))
#   R_low       = Mod(R_sum, 2^64)
#   carry       = Lt(2^64-1, R_sum)        (inline OR named via SymRef)
#   R_hi        = narrow(Ite(carry, IntAdd(narrow(BASE), 1), narrow(BASE)))


def _body_inline_carry(syms_have_named_carry: bool = False) -> str:
    return (
        "\t\tAssignHavocCmd Rlo\n"
        "\t\tAssumeExpCmd Le(Rlo 0xffffffffffffffff)\n"
        "\t\tAssignHavocCmd Rb\n"
        "\t\tAssumeExpCmd Le(Rb 0xffffffffffffffff)\n"
        "\t\tAssignHavocCmd Base\n"
        "\t\tAssumeExpCmd Le(Base 0xffffffffffffffff)\n"
        "\t\tAssignExpCmd Rsum Apply(safe_math_narrow_bv256:bif IntAdd(Rlo Rb))\n"
        "\t\tAssignExpCmd Rlow Mod(Rsum 0x10000000000000000)\n"
        "\t\tAssignExpCmd Rhi Apply(safe_math_narrow_bv256:bif Ite("
        "Lt(0xffffffffffffffff Rsum) "
        "IntAdd(Apply(safe_math_narrow_bv256:bif Base) 0x1) "
        "Apply(safe_math_narrow_bv256:bif Base)))\n"
        "\t\tAssertCmd Le(Rhi 0xffffffffffffffff)\n"
    )


def _body_named_carry() -> str:
    return (
        "\t\tAssignHavocCmd Rlo\n"
        "\t\tAssumeExpCmd Le(Rlo 0xffffffffffffffff)\n"
        "\t\tAssignHavocCmd Rb\n"
        "\t\tAssumeExpCmd Le(Rb 0xffffffffffffffff)\n"
        "\t\tAssignHavocCmd Base\n"
        "\t\tAssumeExpCmd Le(Base 0xffffffffffffffff)\n"
        "\t\tAssignExpCmd Rsum Apply(safe_math_narrow_bv256:bif IntAdd(Rlo Rb))\n"
        "\t\tAssignExpCmd Rlow Mod(Rsum 0x10000000000000000)\n"
        "\t\tAssignExpCmd Carry Lt(0xffffffffffffffff Rsum)\n"
        "\t\tAssignExpCmd Rhi Apply(safe_math_narrow_bv256:bif Ite("
        "Carry "
        "IntAdd(Apply(safe_math_narrow_bv256:bif Base) 0x1) "
        "Apply(safe_math_narrow_bv256:bif Base)))\n"
        "\t\tAssertCmd Le(Rhi 0xffffffffffffffff)\n"
    )


_SYMS = (
    "Rlo:bv256\n\tRb:bv256\n\tBase:bv256\n\tRsum:bv256\n\tRlow:bv256\n"
    "\tRhi:bv256\n\tCarry:bool"
)


def test_inline_carry_chain_rewritten():
    """Inline ``Lt`` in the Ite cond is matched and rewritten into a
    fresh bv256 ``H<N>`` half-register with explicit bounds and bv
    Mod / Div on R_low / R_hi."""
    tac = parse_string(_wrap(_body_inline_carry(), syms=_SYMS), path="<s>")
    res = rewrite_u128_carry_add(tac.program, symbol_sorts=tac.symbol_sorts)
    assert res.hits == 1
    # Exactly one fresh symbol: the H<N> bv256 half-register.
    assert len(res.fresh_symbols) == 1
    h_name, sort = res.fresh_symbols[0]
    assert sort == "bv256"
    assert h_name.startswith("H")
    cmds = _named_assigns(res.program)
    # Rsum dropped.
    assert "Rsum" not in cmds
    # H<N> = narrow(int_sum).
    h_rhs = cmds[h_name].rhs
    assert isinstance(h_rhs, ApplyExpr) and h_rhs.op == "Apply"
    narrow_fn, narrow_arg = h_rhs.args
    assert (
        isinstance(narrow_fn, SymbolRef)
        and narrow_fn.name.startswith("safe_math_narrow_bv")
    )
    assert isinstance(narrow_arg, ApplyExpr) and narrow_arg.op == "IntAdd"
    # Rlow = bv Mod(H<N>, 2^64); Rhi = bv Div(H<N>, 2^64).
    rlow_rhs = cmds["Rlow"].rhs
    assert isinstance(rlow_rhs, ApplyExpr) and rlow_rhs.op == "Mod"
    assert rlow_rhs.args[0] == SymbolRef(h_name)
    rhi_rhs = cmds["Rhi"].rhs
    assert isinstance(rhi_rhs, ApplyExpr) and rhi_rhs.op == "Div"
    assert rhi_rhs.args[0] == SymbolRef(h_name)


def test_named_carry_chain_drops_carry_def():
    """When the carry is named via a SymbolRef def, the def is dropped."""
    tac = parse_string(_wrap(_body_named_carry(), syms=_SYMS), path="<s>")
    res = rewrite_u128_carry_add(tac.program, symbol_sorts=tac.symbol_sorts)
    assert res.hits == 1
    cmds = _named_assigns(res.program)
    assert "Carry" not in cmds  # dropped along with Rsum
    assert "Rsum" not in cmds


def test_range_gate_blocks_overlarge_base():
    """Base with no proven u64 bound: rewrite skipped."""
    body = (
        "\t\tAssignHavocCmd Rlo\n"
        "\t\tAssumeExpCmd Le(Rlo 0xffffffffffffffff)\n"
        "\t\tAssignHavocCmd Rb\n"
        "\t\tAssumeExpCmd Le(Rb 0xffffffffffffffff)\n"
        "\t\tAssignHavocCmd Base\n"
        # No bound on Base — bv256 sort range alone is too wide for the gate.
        "\t\tAssignExpCmd Rsum Apply(safe_math_narrow_bv256:bif IntAdd(Rlo Rb))\n"
        "\t\tAssignExpCmd Rlow Mod(Rsum 0x10000000000000000)\n"
        "\t\tAssignExpCmd Rhi Apply(safe_math_narrow_bv256:bif Ite("
        "Lt(0xffffffffffffffff Rsum) "
        "IntAdd(Apply(safe_math_narrow_bv256:bif Base) 0x1) "
        "Apply(safe_math_narrow_bv256:bif Base)))\n"
        "\t\tAssertCmd Le(Rhi 0xffffffffffffffff)\n"
    )
    tac = parse_string(_wrap(body, syms=_SYMS), path="<s>")
    res = rewrite_u128_carry_add(tac.program, symbol_sorts=tac.symbol_sorts)
    assert res.hits == 0


def test_idempotent_on_already_rewritten_form():
    """A program already in H<N>-narrow / bv-Mod / bv-Div shape is a
    no-op — the matcher only fires on the chunked carry-Ite shape."""
    body = (
        "\t\tAssignHavocCmd Rlo\n"
        "\t\tAssumeExpCmd Le(Rlo 0xffffffffffffffff)\n"
        "\t\tAssignHavocCmd Rb\n"
        "\t\tAssumeExpCmd Le(Rb 0xffffffffffffffff)\n"
        "\t\tAssignHavocCmd Base\n"
        "\t\tAssumeExpCmd Le(Base 0xffffffffffffffff)\n"
        "\t\tAssignExpCmd H0 Apply(safe_math_narrow_bv256:bif "
        "IntAdd(IntMul(Base 0x10000000000000000(int)) IntAdd(Rlo Rb)))\n"
        "\t\tAssumeExpCmd Le(H0 0x100000000000000000000000000000000)\n"
        "\t\tAssignExpCmd Rlow Mod(H0 0x10000000000000000)\n"
        "\t\tAssignExpCmd Rhi Div(H0 0x10000000000000000)\n"
        "\t\tAssertCmd Le(Rhi 0xffffffffffffffff)\n"
    )
    syms = (
        "Rlo:bv256\n\tRb:bv256\n\tBase:bv256\n\tH0:bv256\n"
        "\tRlow:bv256\n\tRhi:bv256"
    )
    tac = parse_string(_wrap(body, syms=syms), path="<s>")
    res = rewrite_u128_carry_add(tac.program, symbol_sorts=tac.symbol_sorts)
    assert res.hits == 0
    assert _named_assigns(res.program).keys() == _named_assigns(tac.program).keys()


def test_emits_three_bound_assumes():
    """The rewrite emits three new assume commands: the BASE bound,
    the partial-sum bound (R_lo + R_b ≤ derived), and H<N>'s
    u128-ish bound — together they make H<N>'s upper bound locally
    derivable without walking BASE's upstream def chain."""
    tac = parse_string(_wrap(_body_inline_carry(), syms=_SYMS), path="<s>")
    res = rewrite_u128_carry_add(tac.program, symbol_sorts=tac.symbol_sorts)
    assert res.hits == 1
    pre_assumes = sum(
        1
        for block in tac.program.blocks
        for cmd in block.commands
        if isinstance(cmd, AssumeExpCmd)
    )
    post_assumes = sum(
        1
        for block in res.program.blocks
        for cmd in block.commands
        if isinstance(cmd, AssumeExpCmd)
    )
    assert post_assumes == pre_assumes + 3


def test_original_assumes_preserved():
    """All original AssumeExpCmds remain after the rewrite (the two new
    ones — partial-sum bound + H<N> bound — are checked separately in
    ``test_emits_partial_sum_bound_and_h_bound``)."""
    tac = parse_string(_wrap(_body_inline_carry(), syms=_SYMS), path="<s>")
    original_assumes = {
        cmd.condition
        for block in tac.program.blocks
        for cmd in block.commands
        if isinstance(cmd, AssumeExpCmd)
    }
    res = rewrite_u128_carry_add(tac.program, symbol_sorts=tac.symbol_sorts)
    post_assumes = {
        cmd.condition
        for block in res.program.blocks
        for cmd in block.commands
        if isinstance(cmd, AssumeExpCmd)
    }
    # Every original assume is still present.
    assert original_assumes <= post_assumes
