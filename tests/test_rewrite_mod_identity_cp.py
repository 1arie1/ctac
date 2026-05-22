"""Unit tests for ``MOD_IDENTITY_CP``."""

from __future__ import annotations

from ctac.ast.nodes import ApplyExpr, AssumeExpCmd, SymbolRef
from ctac.parse import parse_string
from ctac.rewrite import rewrite_program
from ctac.rewrite.rules import MOD_IDENTITY_CP


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


def _last_assume(prog):
    last = None
    for b in prog.blocks:
        for cmd in b.commands:
            if isinstance(cmd, AssumeExpCmd):
                last = cmd
    return last


def test_mod_is_identity_under_range():
    """``R = Mod(X, M)`` with X provably in [0, M-1]: R uses fold to X."""
    body = (
        "\t\tAssignHavocCmd X\n"
        "\t\tAssumeExpCmd Le(X 0xff)\n"  # X <= 255, well under 2^128.
        "\t\tAssignExpCmd R Mod(X 0x100000000000000000000000000000000)\n"
        "\t\tAssumeExpCmd Le(R 0xff)\n"
        "\t\tAssertCmd false\n"
    )
    tac = parse_string(_wrap(body, syms="X:bv256\n\tR:bv256"), path="<s>")
    res = rewrite_program(
        tac.program, (MOD_IDENTITY_CP,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule.get("ModIdentityCP", 0) >= 1
    # The Le(R, ...) assume now references X.
    last = _last_assume(res.program)
    assert last is not None
    cond = last.condition
    assert isinstance(cond, ApplyExpr) and cond.op == "Le"
    assert cond.args[0] == SymbolRef("X")


def test_skips_when_range_doesnt_prove_identity():
    """X's range exceeds M-1: rule abstains (Mod is not identity)."""
    body = (
        "\t\tAssignHavocCmd X\n"
        # No bound on X -> bv256 sort default [0, 2^256-1], exceeds M-1.
        "\t\tAssignExpCmd R Mod(X 0x100000000000000000000000000000000)\n"
        "\t\tAssumeExpCmd Le(R 0xff)\n"
        "\t\tAssertCmd false\n"
    )
    tac = parse_string(_wrap(body, syms="X:bv256\n\tR:bv256"), path="<s>")
    res = rewrite_program(
        tac.program, (MOD_IDENTITY_CP,), symbol_sorts=tac.symbol_sorts
    )
    assert "ModIdentityCP" not in res.hits_by_rule


def test_skips_on_non_mod_def():
    """R's def isn't Mod — rule abstains."""
    body = (
        "\t\tAssignHavocCmd X\n"
        "\t\tAssignExpCmd R IntAdd(X 0x1)\n"
        "\t\tAssumeExpCmd Le(R 0xff)\n"
        "\t\tAssertCmd false\n"
    )
    tac = parse_string(_wrap(body, syms="X:bv256\n\tR:bv256"), path="<s>")
    res = rewrite_program(
        tac.program, (MOD_IDENTITY_CP,), symbol_sorts=tac.symbol_sorts
    )
    assert "ModIdentityCP" not in res.hits_by_rule


def test_handles_symbolic_div_via_range_inference():
    """X = IntDiv(A, B) with A bounded and B's lower bound positive:
    range_infer composes ``floor_div_nonneg`` so X's range is known,
    and the Mod-identity gate can fire."""
    body = (
        "\t\tAssignHavocCmd A\n"
        "\t\tAssumeExpCmd Le(A 0xffffffffffffffff)\n"  # A <= 2^64-1
        "\t\tAssignHavocCmd B\n"
        "\t\tAssumeExpCmd Ge(B 0x100)\n"  # B >= 256
        "\t\tAssumeExpCmd Le(B 0xffffffffffffffff)\n"  # B <= 2^64-1
        "\t\tAssignExpCmd X IntDiv(A B)\n"
        # X <= A/B_lo <= 2^64-1 / 256 < 2^128. So Mod(X, 2^128) = X.
        "\t\tAssignExpCmd R Mod(X 0x100000000000000000000000000000000)\n"
        "\t\tAssumeExpCmd Le(R 0xff)\n"
        "\t\tAssertCmd false\n"
    )
    syms = "A:bv256\n\tB:bv256\n\tX:bv256\n\tR:bv256"
    tac = parse_string(_wrap(body, syms=syms), path="<s>")
    res = rewrite_program(
        tac.program, (MOD_IDENTITY_CP,), symbol_sorts=tac.symbol_sorts
    )
    assert res.hits_by_rule.get("ModIdentityCP", 0) >= 1
