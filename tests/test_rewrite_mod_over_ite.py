"""Unit tests for ``MOD_OVER_ITE``."""

from __future__ import annotations

from ctac.ast.nodes import ApplyExpr, AssumeExpCmd, ConstExpr, SymbolRef
from ctac.parse import parse_string
from ctac.rewrite import rewrite_program
from ctac.rewrite.rules import MOD_OVER_ITE


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


def _assume_cond(prog):
    for b in prog.blocks:
        for cmd in b.commands:
            if isinstance(cmd, AssumeExpCmd):
                return cmd.condition
    raise AssertionError("no assume in program")


def test_const_else_arm_fires():
    """``Mod(Ite(c, X, 2^256-1), 2^64)`` — else arm const-folds; then arm
    becomes identity once the path condition refines R's range."""
    bv256_max = "0x" + "f" * 64
    body = (
        "\t\tAssignHavocCmd R\n"
        "\t\tAssumeExpCmd Le(R 0xffffffffffffffff)\n"
        "\t\tAssignExpCmd TB Ge(R 0x1)\n"
        "\t\tAssignExpCmd Y "
        f"Mod(Ite(TB IntSub(R 0x1) {bv256_max}) 0x10000000000000000)\n"
        "\t\tAssertCmd Le(Y 0xffffffffffffffff)\n"
    )
    tac = parse_string(
        _wrap(body, syms="R:bv256\n\tTB:bool\n\tY:bv256"), path="<s>"
    )
    res = rewrite_program(
        tac.program, (MOD_OVER_ITE,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule.get("ModOverIte", 0) == 1


def test_unfittable_arm_skips():
    """If neither path refinement nor any other simplification applies
    to an arm, the rule must abstain — distributing Mod into both arms
    without shrinking is a regression."""
    body = (
        "\t\tAssignHavocCmd R\n"
        "\t\tAssignHavocCmd S\n"
        "\t\tAssignHavocCmd C\n"
        "\t\tAssignExpCmd Y "
        "Mod(Ite(C R S) 0x10000000000000000)\n"
        "\t\tAssertCmd Le(Y 0xffffffffffffffff)\n"
    )
    tac = parse_string(
        _wrap(body, syms="R:bv256\n\tS:bv256\n\tC:bool\n\tY:bv256"),
        path="<s>",
    )
    res = rewrite_program(
        tac.program, (MOD_OVER_ITE,), symbol_sorts=tac.symbol_sorts
    )
    assert "ModOverIte" not in res.hits_by_rule


def test_both_const_arms_const_fold():
    """``Mod(Ite(c, K1, K2), K3)`` collapses to ``Ite(c, K1%K3, K2%K3)``."""
    body = (
        "\t\tAssignHavocCmd C\n"
        "\t\tAssignExpCmd Y Mod(Ite(C 0x12345 0x67890) 0x100)\n"
        "\t\tAssertCmd Le(Y 0xff)\n"
    )
    tac = parse_string(_wrap(body, syms="C:bool\n\tY:bv256"), path="<s>")
    res = rewrite_program(
        tac.program, (MOD_OVER_ITE,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule.get("ModOverIte", 0) == 1


def test_path_refinement_ge_then_branch():
    """The then-arm's ``IntSub(R, 1)`` fits in u64 only when the
    cond ``Ge(R, 1)`` refines R's lower bound. Verifies the
    refinement path."""
    bv256_max = "0x" + "f" * 64
    body = (
        "\t\tAssignHavocCmd R\n"
        "\t\tAssumeExpCmd Le(R 0xffffffffffffffff)\n"
        "\t\tAssignExpCmd TB Ge(R 0x1)\n"
        "\t\tAssignExpCmd Y "
        f"Mod(Ite(TB IntSub(R 0x1) {bv256_max}) 0x10000000000000000)\n"
        "\t\tAssertCmd Le(Y 0xffffffffffffffff)\n"
    )
    tac = parse_string(
        _wrap(body, syms="R:bv256\n\tTB:bool\n\tY:bv256"), path="<s>"
    )
    res = rewrite_program(
        tac.program, (MOD_OVER_ITE,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule.get("ModOverIte", 0) == 1
    # The Mod is gone from the rewritten Y's RHS.
    y_rhs = None
    for block in res.program.blocks:
        for cmd in block.commands:
            if getattr(cmd, "lhs", None) == "Y":
                y_rhs = cmd.rhs
    assert y_rhs is not None
    assert isinstance(y_rhs, ApplyExpr) and y_rhs.op == "Ite"
    cond, then_arm, else_arm = y_rhs.args
    # Then arm is IntSub(R, 1) directly (no Mod).
    assert isinstance(then_arm, ApplyExpr) and then_arm.op == "IntSub"
    # Else arm is the const-folded 2^64-1.
    assert isinstance(else_arm, ConstExpr)


def test_no_const_divisor_skips():
    """Divisor must be a positive ConstExpr; symbolic K is bailed."""
    body = (
        "\t\tAssignHavocCmd K\n"
        "\t\tAssignHavocCmd C\n"
        "\t\tAssignExpCmd Y Mod(Ite(C 0x10 0x20) K)\n"
        "\t\tAssertCmd Le(Y K)\n"
    )
    tac = parse_string(
        _wrap(body, syms="K:bv256\n\tC:bool\n\tY:bv256"), path="<s>"
    )
    res = rewrite_program(
        tac.program, (MOD_OVER_ITE,), symbol_sorts=tac.symbol_sorts
    )
    assert "ModOverIte" not in res.hits_by_rule


def test_mod_idempotent_arm():
    """``Mod(Ite(c, Mod(X, K), Y_const), K)`` — then arm hits the Mod
    idempotence case."""
    body = (
        "\t\tAssignHavocCmd X\n"
        "\t\tAssignHavocCmd C\n"
        "\t\tAssignExpCmd Y "
        "Mod(Ite(C Mod(X 0x100) 0x10) 0x100)\n"
        "\t\tAssertCmd Le(Y 0xff)\n"
    )
    tac = parse_string(
        _wrap(body, syms="X:bv256\n\tC:bool\n\tY:bv256"), path="<s>"
    )
    res = rewrite_program(
        tac.program, (MOD_OVER_ITE,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule.get("ModOverIte", 0) == 1


# Stub used by the assertions above — keep the imports honest.
_ = (SymbolRef, _assume_cond)
