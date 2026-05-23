"""Unit tests for ``hoist_path_invariant_defs``."""

from __future__ import annotations

from ctac.ast.nodes import AssignExpCmd, SymbolRef
from ctac.parse import parse_string
from ctac.rewrite.hoist_path_invariant_defs import hoist_path_invariant_defs


def _wrap(body: str, *, syms: str) -> str:
    return f"""TACSymbolTable {{
\tUserDefined {{
\t}}
\tBuiltinFunctions {{
\t\tsafe_math_narrow_bv256:JSON{{"#class":"vc.data.TACBuiltInFunction.SafeMathNarrow","returnSort":{{"#class":"tac.Tag.Bit256"}}}}
\t}}
\tUninterpretedFunctions {{
\t}}
\t{syms}
}}
Program {{
{body}
}}
Axioms {{
}}
Metas {{
  "0": []
}}
"""


def _find_assign(program, lhs):
    """Return list of (block_id, cmd_idx, AssignExpCmd) for the named lhs."""
    out = []
    for block in program.blocks:
        for idx, cmd in enumerate(block.commands):
            if isinstance(cmd, AssignExpCmd) and cmd.lhs == lhs:
                out.append((block.id, idx, cmd))
    return out


def test_muldiv_equal_divisor_hoists() -> None:
    """``B = R26 == R32; if B { X = R24 } else { X = muldiv(R24, R32, R26) }``
    Both branch RHSes equal under the cond; the muldiv hoists to entry
    and both branch defs alias it."""
    bv64max = "0xffffffffffffffff"
    body = (
        "\tBlock e Succ [t, f] {\n"
        "\t\tAssignHavocCmd R24\n"
        f"\t\tAssumeExpCmd Le(R24 {bv64max})\n"
        "\t\tAssignHavocCmd R26\n"
        f"\t\tAssumeExpCmd LAnd(Ge(R26 0x1) Le(R26 0x14))\n"
        "\t\tAssignHavocCmd R32\n"
        f"\t\tAssumeExpCmd Le(R32 0xa)\n"
        "\t\tAssignExpCmd B Eq(R26 R32)\n"
        "\t\tJumpiCmd t f B\n"
        "\t}\n"
        "\tBlock t Succ [j] {\n"
        "\t\tAssignExpCmd X R24\n"
        "\t\tJumpCmd j\n"
        "\t}\n"
        "\tBlock f Succ [j] {\n"
        "\t\tAssignExpCmd X IntMulDiv(R24 R32 R26)\n"
        "\t\tJumpCmd j\n"
        "\t}\n"
        "\tBlock j Succ [] {\n"
        "\t\tAssertCmd Le(X 0xffff)\n"
        "\t}"
    )
    syms = (
        "R24:bv256\n\tR26:bv256\n\tR32:bv256\n\tB:bool\n\tX:bv256"
    )
    tac = parse_string(_wrap(body, syms=syms), path="<s>")
    res = hoist_path_invariant_defs(
        tac.program, symbol_sorts=tac.symbol_sorts
    )
    assert res.hits == 1, res
    assert len(res.fresh_symbols) == 1
    hv_name, hv_sort = res.fresh_symbols[0]
    assert hv_sort == "bv256"
    # Both branches' X now reference the hoisted name.
    x_defs = _find_assign(res.program, "X")
    assert len(x_defs) == 2
    for _, _, cmd in x_defs:
        assert cmd.rhs == SymbolRef(hv_name), cmd


def test_narrow_zero_mul_hoists() -> None:
    """``B = R36 == 0; if B { X = 0 } else { X = narrow(K * R36) }``
    The narrow-mul hoists; both branches alias the hoisted name."""
    body = (
        "\tBlock e Succ [t, f] {\n"
        "\t\tAssignHavocCmd R36\n"
        "\t\tAssumeExpCmd Le(R36 0xa)\n"
        "\t\tAssignExpCmd B Eq(R36 0x0)\n"
        "\t\tJumpiCmd t f B\n"
        "\t}\n"
        "\tBlock t Succ [j] {\n"
        "\t\tAssignExpCmd X 0x0\n"
        "\t\tJumpCmd j\n"
        "\t}\n"
        "\tBlock f Succ [j] {\n"
        "\t\tAssignExpCmd X "
        "Apply(safe_math_narrow_bv256:bif IntMul(0x4000(int) R36))\n"
        "\t\tJumpCmd j\n"
        "\t}\n"
        "\tBlock j Succ [] {\n"
        "\t\tAssertCmd Le(X 0xffffffff)\n"
        "\t}"
    )
    syms = "R36:bv256\n\tB:bool\n\tX:bv256"
    tac = parse_string(_wrap(body, syms=syms), path="<s>")
    res = hoist_path_invariant_defs(
        tac.program, symbol_sorts=tac.symbol_sorts
    )
    assert res.hits == 1, res
    assert len(res.fresh_symbols) == 1
    hv_name, _ = res.fresh_symbols[0]
    x_defs = _find_assign(res.program, "X")
    assert len(x_defs) == 2
    for _, _, cmd in x_defs:
        assert cmd.rhs == SymbolRef(hv_name)


def test_non_positive_divisor_abstains() -> None:
    """When the muldiv's divisor's range allows 0, the pattern can't
    fire (the muldiv-axiom only holds for positive divisors)."""
    bv64max = "0xffffffffffffffff"
    body = (
        "\tBlock e Succ [t, f] {\n"
        "\t\tAssignHavocCmd R24\n"
        f"\t\tAssumeExpCmd Le(R24 {bv64max})\n"
        "\t\tAssignHavocCmd R26\n"
        f"\t\tAssumeExpCmd Le(R26 0x14)\n"  # no lower bound on R26
        "\t\tAssignHavocCmd R32\n"
        f"\t\tAssumeExpCmd Le(R32 0xa)\n"
        "\t\tAssignExpCmd B Eq(R26 R32)\n"
        "\t\tJumpiCmd t f B\n"
        "\t}\n"
        "\tBlock t Succ [j] {\n"
        "\t\tAssignExpCmd X R24\n"
        "\t\tJumpCmd j\n"
        "\t}\n"
        "\tBlock f Succ [j] {\n"
        "\t\tAssignExpCmd X IntMulDiv(R24 R32 R26)\n"
        "\t\tJumpCmd j\n"
        "\t}\n"
        "\tBlock j Succ [] {\n"
        "\t\tAssertCmd Le(X 0xffff)\n"
        "\t}"
    )
    syms = "R24:bv256\n\tR26:bv256\n\tR32:bv256\n\tB:bool\n\tX:bv256"
    tac = parse_string(_wrap(body, syms=syms), path="<s>")
    res = hoist_path_invariant_defs(
        tac.program, symbol_sorts=tac.symbol_sorts
    )
    assert res.hits == 0
