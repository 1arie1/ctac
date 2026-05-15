"""Tests for ``SIGN_EXTEND_UNWRAP``."""

from __future__ import annotations

from ctac.ast.nodes import ApplyExpr, SymbolRef
from ctac.parse import parse_string
from ctac.rewrite.framework import rewrite_program
from ctac.rewrite.rules import SIGN_EXTEND_UNWRAP, default_pipeline


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
{body}
}}
Axioms {{
}}
Metas {{
  "0": []
}}
"""


def test_rule_fires_with_range_tightening():
    """When ``Mod(X, 2^64)`` pins ``x`` to ``[0, 2^64)``, the emitted
    Ite uses ``x`` directly (no inner Mod)."""
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd R\n"
            "\t\tAssignExpCmd X Mod(R 0x10000000000000000)\n"
            "\t\tAssignExpCmd I Apply(unwrap_twos_complement_256:bif SignExtend(0x7 X))\n"
            "\t\tAssertCmd Le(I 0x100)\n"
            "\t}\n",
            syms="R:bv256\n\tX:bv256\n\tI:int",
        ),
        path="<s>",
    )
    res = rewrite_program(tac.program, (SIGN_EXTEND_UNWRAP,), symbol_sorts=tac.symbol_sorts)
    assert res.hits_by_rule.get("SignExtendUnwrap") == 1

    # Locate the rewritten I-def and check shape.
    i_cmd = next(
        c for b in res.program.blocks for c in b.commands
        if getattr(c, "lhs", None) == "I"
    )
    rhs = i_cmd.rhs
    assert isinstance(rhs, ApplyExpr) and rhs.op == "Ite"
    cond, then_arm, else_arm = rhs.args
    # Cond: Lt(X, 2^63). Range proved 0 <= X < 2^64, so the operand is
    # X directly, not Mod(X, 2^64).
    assert isinstance(cond, ApplyExpr) and cond.op == "Lt"
    assert cond.args[0] == SymbolRef("X")
    # then arm = X; else arm = IntSub(X, 2^64).
    assert then_arm == SymbolRef("X")
    assert isinstance(else_arm, ApplyExpr) and else_arm.op == "IntSub"
    assert else_arm.args[0] == SymbolRef("X")


def test_rule_uses_mod_when_range_unknown():
    """Without a range-pinning def, the rule still fires but wraps
    the operand in ``Mod(_, 2^w)`` for soundness."""
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd R\n"  # range = bv256, not <= 2^64
            "\t\tAssignExpCmd I Apply(unwrap_twos_complement_256:bif SignExtend(0x7 R))\n"
            "\t\tAssertCmd Le(I 0x100)\n"
            "\t}\n",
            syms="R:bv256\n\tI:int",
        ),
        path="<s>",
    )
    res = rewrite_program(tac.program, (SIGN_EXTEND_UNWRAP,), symbol_sorts=tac.symbol_sorts)
    assert res.hits_by_rule.get("SignExtendUnwrap") == 1

    i_cmd = next(
        c for b in res.program.blocks for c in b.commands
        if getattr(c, "lhs", None) == "I"
    )
    rhs = i_cmd.rhs
    assert isinstance(rhs, ApplyExpr) and rhs.op == "Ite"
    cond, then_arm, _else = rhs.args
    # Cond's left operand is Mod(R, 2^64).
    assert isinstance(cond, ApplyExpr) and cond.op == "Lt"
    inner = cond.args[0]
    assert isinstance(inner, ApplyExpr) and inner.op == "Mod"
    assert inner.args[0] == SymbolRef("R")
    # then arm reuses the same Mod.
    assert then_arm == inner


def test_rule_handles_various_byte_indices():
    """``b`` ranges over [0, 31]; each emits a width-correct Ite."""
    for b in (0, 1, 3, 7, 15, 31):
        tac = parse_string(
            _wrap(
                "\tBlock e Succ [] {\n"
                "\t\tAssignHavocCmd X\n"
                f"\t\tAssignExpCmd I Apply(unwrap_twos_complement_256:bif SignExtend(0x{b:x} X))\n"
                "\t\tAssertCmd Le(I 0x100)\n"
                "\t}\n",
                syms="X:bv256\n\tI:int",
            ),
            path="<s>",
        )
        res = rewrite_program(
            tac.program, (SIGN_EXTEND_UNWRAP,), symbol_sorts=tac.symbol_sorts
        )
        assert res.hits_by_rule.get("SignExtendUnwrap") == 1, f"b={b}"


def test_rule_does_not_fire_on_bare_signextend():
    """Without the ``unwrap_twos_complement_256:bif`` wrapper the rule
    declines — the bare ``SignExtend`` use isn't safe to fold to the
    Int form (the result is bv256, not Int)."""
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd X\n"
            "\t\tAssignExpCmd R SignExtend(0x7 X)\n"
            "\t}\n",
            syms="X:bv256\n\tR:bv256",
        ),
        path="<s>",
    )
    res = rewrite_program(tac.program, (SIGN_EXTEND_UNWRAP,), symbol_sorts=tac.symbol_sorts)
    assert res.hits_by_rule.get("SignExtendUnwrap", 0) == 0


def test_rule_in_default_pipeline_eliminates_signextend():
    """End-to-end: running the default pipeline removes every
    ``SignExtend`` use that's wrapped by the canonical unwrap idiom."""
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd R\n"
            "\t\tAssignExpCmd X Mod(R 0x10000000000000000)\n"
            "\t\tAssignExpCmd I IntMul(0x-1(int) Apply(unwrap_twos_complement_256:bif SignExtend(0x7 X)))\n"
            "\t\tAssertCmd Le(I 0x100)\n"
            "\t}\n",
            syms="R:bv256\n\tX:bv256\n\tI:int",
        ),
        path="<s>",
    )
    res = rewrite_program(tac.program, default_pipeline, symbol_sorts=tac.symbol_sorts)

    def _has_op(expr, op):
        if isinstance(expr, ApplyExpr):
            if expr.op == op:
                return True
            return any(_has_op(a, op) for a in expr.args)
        return False

    for b in res.program.blocks:
        for cmd in b.commands:
            rhs = getattr(cmd, "rhs", None) or getattr(cmd, "predicate", None)
            if rhs is not None:
                assert not _has_op(rhs, "SignExtend"), f"SignExtend remains in {cmd!r}"
