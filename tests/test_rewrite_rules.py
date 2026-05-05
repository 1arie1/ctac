"""Unit tests for N1, R1, R2, R3, CP rules."""

from __future__ import annotations

from ctac.ast.nodes import AssignExpCmd, ApplyExpr, ConstExpr, SymbolRef
from ctac.parse import parse_string
from ctac.rewrite import default_pipeline, rewrite_program
from ctac.rewrite.rules import (
    CP_ALIAS,
    N1_SHIFTED_BWAND,
    R2_DIV_FUSE,
    R3_DIV_MUL_CANCEL,
    R4_DIV_IN_CMP,
)


def _tac(body: str, *, syms: str = "R0:bv256\n\tR1:bv256\n\tR2:bv256") -> str:
    return f"""TACSymbolTable {{
\tUserDefined {{
\t}}
\tBuiltinFunctions {{
\t\tsafe_math_narrow_bv256:JSON{{"x":1}}
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


def _rhs(res_program, lhs: str):
    for b in res_program.blocks:
        for cmd in b.commands:
            if isinstance(cmd, AssignExpCmd) and cmd.lhs == lhs:
                return cmd.rhs
    raise AssertionError(f"no assignment for {lhs}")


def test_r2_fuses_nested_const_div():
    tac = parse_string(
        _tac(
            "\t\tAssignExpCmd R1 Div(R0 0x4)\n\t\tAssignExpCmd R2 Div(R1 0x8)",
        ),
        path="<s>",
    )
    res = rewrite_program(tac.program, (R2_DIV_FUSE,))
    assert res.hits_by_rule == {"R2": 1}
    rhs = _rhs(res.program, "R2")
    assert isinstance(rhs, ApplyExpr) and rhs.op == "Div"
    assert isinstance(rhs.args[0], SymbolRef) and rhs.args[0].name == "R0"
    assert isinstance(rhs.args[1], ConstExpr) and rhs.args[1].value == "0x20"


def test_r2_respects_op_kind():
    # Outer Div, inner IntDiv -> should not fuse (different semantic domains).
    tac = parse_string(
        _tac(
            "\t\tAssignExpCmd R1 IntDiv(R0 0x4)\n\t\tAssignExpCmd R2 Div(R1 0x8)",
        ),
        path="<s>",
    )
    res = rewrite_program(tac.program, (R2_DIV_FUSE,))
    assert res.hits_by_rule == {}


def test_r3_cancels_common_factor():
    tac = parse_string(
        _tac(
            "\t\tAssignExpCmd R1 Mul(0x4 R0)\n\t\tAssignExpCmd R2 Div(R1 0x4)",
        ),
        path="<s>",
    )
    res = rewrite_program(tac.program, (R3_DIV_MUL_CANCEL,))
    assert res.hits_by_rule == {"R3": 1}
    assert _rhs(res.program, "R2") == SymbolRef("R0")


def test_r3_cancels_when_const_on_right():
    tac = parse_string(
        _tac(
            "\t\tAssignExpCmd R1 Mul(R0 0x4)\n\t\tAssignExpCmd R2 Div(R1 0x4)",
        ),
        path="<s>",
    )
    res = rewrite_program(tac.program, (R3_DIV_MUL_CANCEL,))
    assert res.hits_by_rule == {"R3": 1}
    assert _rhs(res.program, "R2") == SymbolRef("R0")


def test_r3_cancels_factor_in_nested_mul():
    """Div(Mul(A, Mul(c, B)), c) -> Mul(A, B)."""
    tac = parse_string(
        _tac(
            "\t\tAssignExpCmd R1 Mul(R0 Mul(0x4 R2))\n\t\tAssignExpCmd R3 Div(R1 0x4)",
            syms="R0:bv256\n\tR1:bv256\n\tR2:bv256\n\tR3:bv256",
        ),
        path="<s>",
    )
    res = rewrite_program(tac.program, (R3_DIV_MUL_CANCEL,))
    assert res.hits_by_rule.get("R3", 0) == 1
    rhs = _rhs(res.program, "R3")
    assert isinstance(rhs, ApplyExpr) and rhs.op == "Mul"
    assert rhs.args == (SymbolRef("R0"), SymbolRef("R2"))


def test_r3_cancels_factor_through_static_def_and_narrow():
    """Factor peels across SymbolRef defs and safe_math_narrow wrappers."""
    tac_src = _tac(
        """\t\tAssignHavocCmd R13
\t\tAssignHavocCmd R53
\t\tAssignExpCmd I66 IntMul(0x4000(int) R13)
\t\tAssignExpCmd R67 Apply(safe_math_narrow_bv256:bif I66)
\t\tAssignExpCmd I73 IntMul(R53 R67)
\t\tAssignExpCmd R76 IntDiv(I73 0x4000)""",
        syms="R13:bv256\n\tR53:bv256\n\tI66:bv256\n\tR67:bv256\n\tI73:bv256\n\tR76:bv256",
    )
    tac = parse_string(tac_src, path="<s>")
    res = rewrite_program(tac.program, (R3_DIV_MUL_CANCEL,))
    assert res.hits_by_rule.get("R3", 0) == 1
    rhs = _rhs(res.program, "R76")
    # 2^14 factor peels out of R67 -> R13; R76 RHS is IntMul(R53, R13).
    assert isinstance(rhs, ApplyExpr) and rhs.op == "IntMul"
    assert rhs.args == (SymbolRef("R53"), SymbolRef("R13"))


def test_r3_full_numerator_is_factor():
    """Div(c, c) collapses to 1 when the entire numerator equals the factor."""
    tac = parse_string(
        _tac("\t\tAssignExpCmd R1 Div(0x4 0x4)"),
        path="<s>",
    )
    res = rewrite_program(tac.program, (R3_DIV_MUL_CANCEL,))
    assert res.hits_by_rule.get("R3", 0) == 1
    rhs = _rhs(res.program, "R1")
    assert isinstance(rhs, ConstExpr)
    assert int(rhs.value, 0) == 1


def test_r3_partial_const_factor():
    """Div(Mul(2c, A), c) -> Mul(2, A); the constant factor is only partially consumed."""
    tac = parse_string(
        _tac("\t\tAssignExpCmd R1 Mul(0x8 R0)\n\t\tAssignExpCmd R2 Div(R1 0x4)"),
        path="<s>",
    )
    res = rewrite_program(tac.program, (R3_DIV_MUL_CANCEL,))
    assert res.hits_by_rule.get("R3", 0) == 1
    rhs = _rhs(res.program, "R2")
    # 0x8 / 0x4 = 0x2 -> Mul(0x2, R0)
    assert isinstance(rhs, ApplyExpr) and rhs.op == "Mul"
    assert isinstance(rhs.args[0], ConstExpr)
    assert int(rhs.args[0].value, 0) == 2


def test_r3_does_not_cancel_mismatched_constant():
    tac = parse_string(
        _tac(
            "\t\tAssignExpCmd R1 Mul(0x4 R0)\n\t\tAssignExpCmd R2 Div(R1 0x8)",
        ),
        path="<s>",
    )
    res = rewrite_program(tac.program, (R3_DIV_MUL_CANCEL,))
    assert res.hits_by_rule == {}


def test_n1_expands_shifted_bwand():
    tac = parse_string(
        _tac(
            "\t\tAssignExpCmd R1 BWAnd(R0 0x3fffffffc000)",
        ),
        path="<s>",
    )
    res = rewrite_program(tac.program, (N1_SHIFTED_BWAND,))
    assert res.hits_by_rule == {"N1": 1}
    rhs = _rhs(res.program, "R1")
    # Mul(Mod(Div(R0, 0x4000), 0x100000000), 0x4000)
    assert isinstance(rhs, ApplyExpr) and rhs.op == "Mul"
    inner_mod = rhs.args[0]
    assert isinstance(inner_mod, ApplyExpr) and inner_mod.op == "Mod"
    inner_div = inner_mod.args[0]
    assert isinstance(inner_div, ApplyExpr) and inner_div.op == "Div"
    assert isinstance(inner_div.args[0], SymbolRef) and inner_div.args[0].name == "R0"


def test_n1_skips_lo_zero_mask():
    # Mask 0xff has lo=0 — unshifted low mask. Rule intentionally skips.
    tac = parse_string(
        _tac(
            "\t\tAssignExpCmd R1 BWAnd(R0 0xff)",
        ),
        path="<s>",
    )
    res = rewrite_program(tac.program, (N1_SHIFTED_BWAND,))
    assert res.hits_by_rule == {}


def test_r1_collapses_bitfield_with_dominating_range():
    tac_src = _tac(
        """\t\tAssignHavocCmd R0
\t\tAssumeExpCmd Le(R0 0xffffffff)
\t\tAssignExpCmd R1 IntMul(0x4000(int) R0)
\t\tAssignExpCmd R2 Apply(safe_math_narrow_bv256:bif R1)
\t\tAssignExpCmd R3 BWAnd(R2 0x3fffffffc000)""",
        syms="R0:bv256\n\tR1:bv256\n\tR2:bv256\n\tR3:bv256",
    )
    tac = parse_string(tac_src, path="<s>")
    res = rewrite_program(tac.program, default_pipeline, symbol_sorts=tac.symbol_sorts)
    # N1 + R1 + CP should fire at least once each; DCE happens outside rewrite.
    assert res.hits_by_rule.get("N1", 0) == 1
    assert res.hits_by_rule.get("R1", 0) == 1
    # R3 RHS is now SymbolRef(R2) via R1; CP may further rewrite uses elsewhere.
    assert _rhs(res.program, "R3") == SymbolRef("R2")


def test_r1_requires_range_to_fit():
    # R0 <= 0xffffffffffff (2^48-1) does not fit in 2^46 window; R1 must not fire.
    tac_src = _tac(
        """\t\tAssignHavocCmd R0
\t\tAssumeExpCmd Le(R0 0xffffffffffff)
\t\tAssignExpCmd R1 IntMul(0x4000(int) R0)
\t\tAssignExpCmd R2 Apply(safe_math_narrow_bv256:bif R1)
\t\tAssignExpCmd R3 BWAnd(R2 0x3fffffffc000)""",
        syms="R0:bv256\n\tR1:bv256\n\tR2:bv256\n\tR3:bv256",
    )
    tac = parse_string(tac_src, path="<s>")
    res = rewrite_program(tac.program, default_pipeline, symbol_sorts=tac.symbol_sorts)
    assert res.hits_by_rule.get("N1", 0) == 1
    assert res.hits_by_rule.get("R1", 0) == 0


def test_r4_lt_div_left():
    """Lt(Div(A, c), C) -> Lt(A, IntMul(c, C)) for c > 0.

    Arithmetic is emitted in the Int domain (IntMul + (int)-tagged
    constant) regardless of the source Div op, to avoid bv overflow.
    """
    tac = parse_string(
        _tac("\t\tAssignExpCmd R1 Div(R0 0x4)\n\t\tAssumeExpCmd Lt(R1 R2)"),
        path="<s>",
    )
    res = rewrite_program(tac.program, (R4_DIV_IN_CMP,))
    assert res.hits_by_rule.get("R4", 0) == 1
    for b in res.program.blocks:
        for cmd in b.commands:
            if type(cmd).__name__ == "AssumeExpCmd":
                got = cmd.condition
                assert isinstance(got, ApplyExpr) and got.op == "Lt"
                rhs = got.args[1]
                assert isinstance(rhs, ApplyExpr) and rhs.op == "IntMul"
                # Divisor is retyped to (int).
                from ctac.ast.nodes import ConstExpr as CE
                assert isinstance(rhs.args[0], CE) and rhs.args[0].value == "0x4(int)"


def test_r4_le_right_flips_to_ge():
    """Le(C, Div(A, c)) flips to Ge(Div(A, c), C) then applies Ge rule."""
    tac = parse_string(
        _tac("\t\tAssignExpCmd R1 Div(R0 0x4)\n\t\tAssumeExpCmd Le(R2 R1)"),
        path="<s>",
    )
    res = rewrite_program(tac.program, (R4_DIV_IN_CMP,))
    assert res.hits_by_rule.get("R4", 0) == 1
    for b in res.program.blocks:
        for cmd in b.commands:
            if type(cmd).__name__ == "AssumeExpCmd":
                got = cmd.condition
                # Le(R2, Div(...)) -> Ge(Div(...), R2) -> Ge(R0, Mul(0x4, R2))
                assert isinstance(got, ApplyExpr) and got.op == "Ge"
                assert got.args[0] == SymbolRef("R0")


def test_r4_eq_produces_two_sided_bound():
    """Eq(Div(A, c), C) -> LAnd(Ge(A, c*C), Lt(A, c*(C+1)))."""
    tac = parse_string(
        _tac("\t\tAssignExpCmd R1 Div(R0 0x4)\n\t\tAssumeExpCmd Eq(R1 R2)"),
        path="<s>",
    )
    res = rewrite_program(tac.program, (R4_DIV_IN_CMP,))
    assert res.hits_by_rule.get("R4", 0) == 1
    for b in res.program.blocks:
        for cmd in b.commands:
            if type(cmd).__name__ == "AssumeExpCmd":
                got = cmd.condition
                assert isinstance(got, ApplyExpr) and got.op == "LAnd"
                assert isinstance(got.args[0], ApplyExpr) and got.args[0].op == "Ge"
                assert isinstance(got.args[1], ApplyExpr) and got.args[1].op == "Lt"


def test_r4_skips_non_positive_const_divisor():
    """Non-positive divisor skips R4 (safety: Euclidean div requires B > 0)."""
    tac = parse_string(
        _tac("\t\tAssignExpCmd R1 Div(R0 R3)\n\t\tAssumeExpCmd Lt(R1 R2)",
             syms="R0:bv256\n\tR1:bv256\n\tR2:bv256\n\tR3:bv256"),
        path="<s>",
    )
    res = rewrite_program(tac.program, (R4_DIV_IN_CMP,))
    assert res.hits_by_rule.get("R4", 0) == 0  # R3 isn't a constant


def test_r4_skips_both_sides_div():
    """Both-sides Div: R4 skips to avoid non-obvious rewrite choice."""
    tac = parse_string(
        _tac("""\t\tAssignExpCmd R1 Div(R0 0x4)
\t\tAssignExpCmd R3 Div(R2 0x8)
\t\tAssumeExpCmd Lt(R1 R3)""",
             syms="R0:bv256\n\tR1:bv256\n\tR2:bv256\n\tR3:bv256"),
        path="<s>",
    )
    res = rewrite_program(tac.program, (R4_DIV_IN_CMP,))
    assert res.hits_by_rule.get("R4", 0) == 0


def test_r4_intdiv_uses_intmul():
    """IntDiv selects IntMul / IntAdd for the rewrite."""
    tac = parse_string(
        _tac("\t\tAssignExpCmd R1 IntDiv(R0 0x4)\n\t\tAssumeExpCmd Lt(R1 R2)"),
        path="<s>",
    )
    res = rewrite_program(tac.program, (R4_DIV_IN_CMP,))
    for b in res.program.blocks:
        for cmd in b.commands:
            if type(cmd).__name__ == "AssumeExpCmd":
                got = cmd.condition
                rhs = got.args[1]
                assert isinstance(rhs, ApplyExpr) and rhs.op == "IntMul"


def test_r4_peels_narrow_via_lookthrough():
    """R4 sees through narrow(IntDiv(...)) thanks to transitive lookthrough."""
    tac_src = _tac(
        """\t\tAssignHavocCmd R0
\t\tAssignExpCmd I1 IntMul(R3 R4)
\t\tAssignExpCmd R1 Apply(safe_math_narrow_bv256:bif IntDiv(I1 0x4000))
\t\tAssumeExpCmd Lt(R1 R2)""",
        syms="R0:bv256\n\tI1:bv256\n\tR1:bv256\n\tR2:bv256\n\tR3:bv256\n\tR4:bv256",
    )
    tac = parse_string(tac_src, path="<s>")
    res = rewrite_program(tac.program, (R4_DIV_IN_CMP,))
    assert res.hits_by_rule.get("R4", 0) == 1
    for b in res.program.blocks:
        for cmd in b.commands:
            if type(cmd).__name__ == "AssumeExpCmd":
                got = cmd.condition
                # RHS should be the post-Div numerator I1 (no Div remains).
                assert isinstance(got, ApplyExpr) and got.op == "Lt"
                assert got.args[0] == SymbolRef("I1")


def test_lnot_cmp_flip_le_to_gt():
    """LNot(Le(X, Y)) simplifies to Gt(X, Y) via BoolAbsorb."""
    from ctac.rewrite.rules import BOOL_ABSORB

    tac = parse_string(
        _tac("\t\tAssumeExpCmd LNot(Le(R0 R1))"),
        path="<s>",
    )
    res = rewrite_program(tac.program, (BOOL_ABSORB,))
    for b in res.program.blocks:
        for cmd in b.commands:
            if type(cmd).__name__ == "AssumeExpCmd":
                got = cmd.condition
                assert isinstance(got, ApplyExpr) and got.op == "Gt"


def test_cp_propagates_through_alias():
    tac_src = _tac(
        """\t\tAssignHavocCmd R0
\t\tAssignExpCmd R1 R0
\t\tAssignExpCmd R2 Add(R1 R1)""",
        syms="R0:bv256\n\tR1:bv256\n\tR2:bv256",
    )
    tac = parse_string(tac_src, path="<s>")
    res = rewrite_program(tac.program, (CP_ALIAS,))
    assert res.hits_by_rule.get("CP", 0) >= 2
    rhs = _rhs(res.program, "R2")
    assert isinstance(rhs, ApplyExpr) and rhs.op == "Add"
    assert rhs.args == (SymbolRef("R0"), SymbolRef("R0"))


def test_cp_propagates_constant_to_use_sites():
    """`R1 = 0x300000538` then `R2 = Select(M, R1)` — CP propagates the
    constant to the Select-index, unblocking SELECT_OVER_STORE / range
    folding downstream. (Mirror of the L0_triple post-specialize shape
    documented in the parked CP_CONST entry.)"""
    tac_src = _tac(
        """\t\tAssignHavocCmd M
\t\tAssignExpCmd R1 0x300000538
\t\tAssignExpCmd R2 Select(M R1)""",
        syms="M:bytemap\n\tR1:bv256\n\tR2:bv256",
    )
    tac = parse_string(tac_src, path="<s>")
    res = rewrite_program(tac.program, (CP_ALIAS,))
    assert res.hits_by_rule.get("CP", 0) >= 1
    rhs = _rhs(res.program, "R2")
    assert isinstance(rhs, ApplyExpr) and rhs.op == "Select"
    assert rhs.args == (SymbolRef("M"), ConstExpr("0x300000538"))


def test_cp_propagates_constant_through_compound_expressions():
    """Constants flow through nested expressions too — `IntAdd(0x8, R1)`
    becomes `IntAdd(0x8, 0x300000538)` once CP fires on R1. (RangeFold
    then folds compound forms to a single ConstExpr; that's a separate
    rule outside CP's scope.)"""
    tac_src = _tac(
        """\t\tAssignExpCmd R1 0x300000538
\t\tAssignExpCmd R2 IntAdd(0x8(int) R1)""",
        syms="R1:bv256\n\tR2:int",
    )
    tac = parse_string(tac_src, path="<s>")
    res = rewrite_program(tac.program, (CP_ALIAS,))
    assert res.hits_by_rule.get("CP", 0) >= 1
    rhs = _rhs(res.program, "R2")
    assert isinstance(rhs, ApplyExpr) and rhs.op == "IntAdd"
    assert rhs.args == (ConstExpr("0x8(int)"), ConstExpr("0x300000538"))


def test_assume_range_only_visible_in_dominating_branch():
    """CP should not inline facts across non-dominating branches."""
    tac_src = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tR0:bv256
\tR1:bv256
\tc:bool
}
Program {
\tBlock entry Succ [L, R] {
\t\tAssignHavocCmd c
\t\tJumpiCmd L R c
\t}
\tBlock L Succ [J] {
\t\tAssumeExpCmd Le(R0 0xff)
\t\tJumpCmd J
\t}
\tBlock R Succ [J] {
\t\tJumpCmd J
\t}
\tBlock J Succ [] {
\t\tAssignExpCmd R1 Mul(Mod(Div(R0 0x4000) 0x100000000) 0x4000)
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""
    tac = parse_string(tac_src, path="<s>")
    res = rewrite_program(tac.program, default_pipeline, symbol_sorts=tac.symbol_sorts)
    # The Le(R0, 0xff) assume in L does not dominate use in J -> R1 must not fire.
    assert res.hits_by_rule.get("R1", 0) == 0


def test_ite_depth_cap_blocks_deep_range_inference():
    """``ite_max_depth=0`` disables Ite range unioning entirely."""
    tac_src = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t\tsafe_math_narrow_bv256:JSON{"x":1}
\t}
\tUninterpretedFunctions {
\t}
\tR0:bv256
\tR1:bv256
\tR2:bv256
\tR3:bv256
\tR4:bv256
\tc:bool
}
Program {
\tBlock e Succ [] {
\t\tAssignHavocCmd R0
\t\tAssumeExpCmd Le(R0 0xffffffff)
\t\tAssignHavocCmd c
\t\tAssignExpCmd R1 Ite(c 0x0 R0)
\t\tAssignExpCmd R2 IntMul(0x4000(int) R1)
\t\tAssignExpCmd R3 Apply(safe_math_narrow_bv256:bif R2)
\t\tAssignExpCmd R4 BWAnd(R3 0x3fffffffc000)
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""
    tac = parse_string(tac_src, path="<s>")
    # depth=4 (default): R1 fires. depth=0: bails at the Ite, so R1 doesn't fire.
    deep = rewrite_program(tac.program, default_pipeline, symbol_sorts=tac.symbol_sorts)
    shallow = rewrite_program(tac.program, default_pipeline, ite_max_depth=0)
    assert deep.hits_by_rule.get("R1", 0) == 1
    assert shallow.hits_by_rule.get("R1", 0) == 0
    # N1 still fires regardless (no range reasoning).
    assert shallow.hits_by_rule.get("N1", 0) == 1


def test_r1_fires_through_ite_branches():
    """Range inference unions Ite branch ranges; R1 can then collapse bitfield."""
    tac_src = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t\tsafe_math_narrow_bv256:JSON{"x":1}
\t}
\tUninterpretedFunctions {
\t}
\tR0:bv256
\tR1:bv256
\tR2:bv256
\tR3:bv256
\tR4:bv256
\tc:bool
}
Program {
\tBlock e Succ [] {
\t\tAssignHavocCmd R0
\t\tAssumeExpCmd Le(R0 0xffffffff)
\t\tAssignHavocCmd c
\t\tAssignExpCmd R1 Ite(c 0x0 R0)
\t\tAssignExpCmd R2 IntMul(0x4000(int) R1)
\t\tAssignExpCmd R3 Apply(safe_math_narrow_bv256:bif R2)
\t\tAssignExpCmd R4 BWAnd(R3 0x3fffffffc000)
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""
    tac = parse_string(tac_src, path="<s>")
    res = rewrite_program(tac.program, default_pipeline, symbol_sorts=tac.symbol_sorts)
    assert res.hits_by_rule.get("N1", 0) == 1
    assert res.hits_by_rule.get("R1", 0) == 1, res.hits_by_rule


def test_r1_does_not_fire_without_low_bits_proof():
    """R1's low-bits gate must reject directly-bounded havoc symbols.

    Counterexample if it didn't: ``R0 = 1`` satisfies ``Le(R0 0xff)``
    (R0 in [0, 2^8-1] — fits the 2^(k+n) bound), but
    ``((R0/16)%16)*16 = 0 != R0 = 1``. The rule used to fire here
    before the structural divisibility gate was added.
    """
    tac_src = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tR0:bv256
\tR1:bv256
}
Program {
\tBlock entry Succ [] {
\t\tAssignHavocCmd R0
\t\tAssumeExpCmd Le(R0 0xff)
\t\tAssignExpCmd R1 Mul(Mod(Div(R0 0x10) 0x10) 0x10)
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""
    tac = parse_string(tac_src, path="<s>")
    res = rewrite_program(tac.program, default_pipeline, symbol_sorts=tac.symbol_sorts)
    assert res.hits_by_rule.get("R1", 0) == 0, res.hits_by_rule
