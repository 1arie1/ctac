"""Equate-aware definition lookup (``RewriteCtx.resolve_equate`` /
``lookthrough(through_equates=True)``).

The frontend's summary-output protocol pre-allocates havoc slots and
binds them with ``assume Eq(slot, value)``; recognizers opting in can
chase def structure across that wall, gated on the equate dominating
the query position. The program is never rewritten by the chase —
only by the fires it enables, each carrying its own rw-eq CHK.
"""

from __future__ import annotations

from ctac.ast.nodes import ApplyExpr, AssignExpCmd
from ctac.parse import parse_string
from ctac.rewrite.context import RewriteCtx
from ctac.rewrite.framework import rewrite_program
from ctac.rewrite.rules import MUL_DIV_TO_MULDIV


def _wrap_blocks(blocks: str, *, syms: str) -> str:
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
{blocks}
}}
Axioms {{
}}
Metas {{
  "0": []
}}
"""


_SYMS = "X:bv256\n\tA:bv256\n\tB:bv256\n\tV:bv256\n\tQ:bv256\n\tc:bool"


def _linear_program(eq_order_slot_first: bool) -> str:
    eq = "Eq(X V)" if eq_order_slot_first else "Eq(V X)"
    return _wrap_blocks(
        "\tBlock e Succ [b1] {\n"
        "\t\tAssignHavocCmd X\n"
        "\t\tAssignHavocCmd A\n"
        "\t\tAssignHavocCmd B\n"
        "\t\tJumpCmd b1\n"
        "\t}\n"
        "\tBlock b1 Succ [] {\n"
        "\t\tAssignExpCmd V Apply(safe_math_narrow_bv256:bif IntMul(A B))\n"
        f"\t\tAssumeExpCmd {eq}\n"
        "\t\tAssignExpCmd Q Apply(safe_math_narrow_bv256:bif IntDiv(X 0x5(int)))\n"
        "\t}",
        syms=_SYMS,
    )


def _assigns(prog) -> dict[str, AssignExpCmd]:
    return {
        cmd.lhs: cmd
        for block in prog.blocks
        for cmd in block.commands
        if isinstance(cmd, AssignExpCmd)
    }


def test_resolve_equate_dominance_gating():
    tac = parse_string(_linear_program(True), path="<s>")
    ctx = RewriteCtx(tac.program, symbol_sorts=tac.symbol_sorts)
    # Query after the equate (b1, cmd 2): hop is live.
    ctx.set_position("b1", 2)
    assert ctx.resolve_equate("X") == "V"
    # Query before the equate (b1, cmd 0): not dominated, no hop.
    ctx.set_position("b1", 0)
    assert ctx.resolve_equate("X") is None
    # No position: no hop.
    ctx.set_position(None, None)
    assert ctx.resolve_equate("X") is None
    # Non-slot symbol: no hop.
    ctx.set_position("b1", 2)
    assert ctx.resolve_equate("V") is None


def test_lookthrough_through_equates_is_opt_in():
    tac = parse_string(_linear_program(True), path="<s>")
    ctx = RewriteCtx(tac.program, symbol_sorts=tac.symbol_sorts)
    ctx.set_position("b1", 2)
    from ctac.ast.nodes import SymbolRef

    # Default: the slot is a havoc, lookthrough stops at it.
    assert ctx.lookthrough(SymbolRef("X")) == SymbolRef("X")
    # Opted in: hops the equate, then expands V's def and peels narrow.
    inner = ctx.lookthrough(SymbolRef("X"), through_equates=True)
    assert isinstance(inner, ApplyExpr) and inner.op == "IntMul"


def test_muldiv_fires_through_equate_both_orders():
    for slot_first in (True, False):
        tac = parse_string(_linear_program(slot_first), path="<s>")
        res = rewrite_program(
            tac.program, (MUL_DIV_TO_MULDIV,), symbol_sorts=tac.symbol_sorts
        )
        q_rhs = _assigns(res.program)["Q"].rhs
        assert isinstance(q_rhs, ApplyExpr) and q_rhs.op == "Apply"
        inner = q_rhs.args[1]
        assert isinstance(inner, ApplyExpr) and inner.op == "IntMulDiv", (
            f"slot_first={slot_first}: {inner!r}"
        )


def test_muldiv_no_fire_when_equate_does_not_dominate():
    # Diamond: the equate lives on one branch; the div sits at the
    # join, which the equate block does not dominate.
    src = _wrap_blocks(
        "\tBlock e Succ [b1, b2] {\n"
        "\t\tAssignHavocCmd X\n"
        "\t\tAssignHavocCmd A\n"
        "\t\tAssignHavocCmd B\n"
        "\t\tAssignHavocCmd c\n"
        "\t\tAssignExpCmd V Apply(safe_math_narrow_bv256:bif IntMul(A B))\n"
        "\t\tJumpiCmd b1 b2 c\n"
        "\t}\n"
        "\tBlock b1 Succ [b3] {\n"
        "\t\tAssumeExpCmd Eq(X V)\n"
        "\t\tJumpCmd b3\n"
        "\t}\n"
        "\tBlock b2 Succ [b3] {\n"
        "\t\tJumpCmd b3\n"
        "\t}\n"
        "\tBlock b3 Succ [] {\n"
        "\t\tAssignExpCmd Q Apply(safe_math_narrow_bv256:bif IntDiv(X 0x5(int)))\n"
        "\t}",
        syms=_SYMS,
    )
    tac = parse_string(src, path="<s>")
    res = rewrite_program(
        tac.program, (MUL_DIV_TO_MULDIV,), symbol_sorts=tac.symbol_sorts
    )
    q_rhs = _assigns(res.program)["Q"].rhs
    inner = q_rhs.args[1] if isinstance(q_rhs, ApplyExpr) else q_rhs
    assert isinstance(inner, ApplyExpr) and inner.op == "IntDiv"


def test_both_slots_equate_is_skipped():
    # X and Y are both pure havoc slots: chase direction would be
    # ambiguous, so the equate is not indexed.
    src = _wrap_blocks(
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd X\n"
        "\t\tAssignHavocCmd Y\n"
        "\t\tAssumeExpCmd Eq(X Y)\n"
        "\t\tAssignExpCmd Q Apply(safe_math_narrow_bv256:bif IntDiv(X 0x5(int)))\n"
        "\t}",
        syms="X:bv256\n\tY:bv256\n\tQ:bv256",
    )
    tac = parse_string(src, path="<s>")
    ctx = RewriteCtx(tac.program, symbol_sorts=tac.symbol_sorts)
    ctx.set_position("e", 3)
    assert ctx.resolve_equate("X") is None
    assert ctx.resolve_equate("Y") is None
