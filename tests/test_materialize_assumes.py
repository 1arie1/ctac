"""Unit tests for ``materialize_assumes``: the post-rewrite pass that
surfaces interval-derived facts as explicit ``assume`` commands
around uses of axiomatized operators (currently ``IntCeilDiv``)."""

from __future__ import annotations

from ctac.analysis import (
    analyze_dsa,
    analyze_use_before_def,
    extract_def_use,
)
from ctac.ast.nodes import (
    ApplyExpr,
    AssignExpCmd,
    AssumeExpCmd,
    SymbolRef,
)
from ctac.parse import parse_string
from ctac.rewrite.materialize_assumes import materialize_assumes


def _tac_with_int_ceil_div_use(
    *,
    den_assume: str = "LAnd(Ge(R_den 0x1) Le(R_den 0xffff))",
    num_assume: str = "LAnd(Ge(R_num 0x0) Le(R_num 0xffffffff))",
) -> str:
    """A tiny program with one IntCeilDiv use site, surrounded by
    interval-shape assumes that ``ctx.range`` matches as inclusive
    bounds."""
    return f"""TACSymbolTable {{
\tUserDefined {{
\t}}
\tBuiltinFunctions {{
\t\tsafe_math_narrow_bv256:JSON{{"x":1}}
\t}}
\tUninterpretedFunctions {{
\t}}
\tR_num:bv256
\tR_den:bv256
\tR_ceil:bv256
}}
Program {{
\tBlock e Succ [] {{
\t\tAssignHavocCmd R_num
\t\tAssumeExpCmd {num_assume}
\t\tAssignHavocCmd R_den
\t\tAssumeExpCmd {den_assume}
\t\tAssignExpCmd R_ceil Apply(safe_math_narrow_bv256:bif IntCeilDiv(R_num R_den))
\t}}
}}
Axioms {{
}}
Metas {{
  "0": []
}}
"""


def _block_cmds(program):
    return list(program.blocks[0].commands)


def _is_assume_with_op(cmd, op: str) -> bool:
    return (
        isinstance(cmd, AssumeExpCmd)
        and isinstance(cmd.condition, ApplyExpr)
        and cmd.condition.op == op
    )


def _check_tac_well_formed(program, *, symbol_sorts=None) -> None:
    """Output validation: DSA shape passes; def-use is consistent
    (no use-before-def). The materializer should never produce TAC
    that fails the standard analyses."""
    du = extract_def_use(program)
    dsa = analyze_dsa(program, def_use=du)
    assert dsa.is_valid, f"DSA shape issues after materialize: {dsa.issues}"
    ubd = analyze_use_before_def(program, def_use=du)
    assert not ubd.issues, (
        f"use-before-def after materialize: {ubd.issues}"
    )


def test_materialize_inserts_den_positive_and_lhs_nonneg() -> None:
    """When interval analysis proves both ``R_den > 0`` and the
    IntCeilDiv result's non-negativity, both hints land: ``assume
    R_den > 0`` before the host and ``assume R_ceil >= 0`` after."""
    tac = parse_string(_tac_with_int_ceil_div_use(), path="<s>")
    res = materialize_assumes(tac.program, symbol_sorts=tac.symbol_sorts)
    cmds = _block_cmds(res.program)

    host_idx = next(
        i
        for i, c in enumerate(cmds)
        if isinstance(c, AssignExpCmd) and c.lhs == "R_ceil"
    )
    assert _is_assume_with_op(cmds[host_idx - 1], "Gt")
    gt_args = cmds[host_idx - 1].condition.args
    assert isinstance(gt_args[0], SymbolRef) and gt_args[0].name == "R_den"

    assert _is_assume_with_op(cmds[host_idx + 1], "Ge")
    ge_args = cmds[host_idx + 1].condition.args
    assert isinstance(ge_args[0], SymbolRef) and ge_args[0].name == "R_ceil"

    assert res.hits == {
        "intceildiv_den_positive": 1,
        "intceildiv_lhs_nonneg": 1,
    }
    _check_tac_well_formed(res.program, symbol_sorts=tac.symbol_sorts)


def test_materialize_skips_when_den_range_unknown() -> None:
    """Without an inclusive range on R_den, ``infer_expr_range(R_den)``
    can't prove ``R_den > 0`` (the only constraint is the bv256 sort,
    which gives ``[0, 2^256-1]`` — not strictly positive). The
    den-positive hint is NOT materialized; the lhs-nonneg hint still
    lands because R_ceil's bv256 sort guarantees non-negativity."""
    tac_str = _tac_with_int_ceil_div_use().replace(
        "AssumeExpCmd LAnd(Ge(R_den 0x1) Le(R_den 0xffff))\n", ""
    )
    tac = parse_string(tac_str, path="<s>")
    res = materialize_assumes(tac.program, symbol_sorts=tac.symbol_sorts)
    assert "intceildiv_den_positive" not in res.hits
    # R_ceil:bv256's sort gives [0, 2^256-1] — non-negative — so the
    # post-host ``assume R_ceil >= 0`` still materializes.
    assert res.hits.get("intceildiv_lhs_nonneg") == 1
    _check_tac_well_formed(res.program, symbol_sorts=tac.symbol_sorts)


def test_materialize_idempotent_on_no_intceildiv() -> None:
    """A program without any IntCeilDiv use is returned unchanged
    (same object), so callers can run the pass on every TAC safely."""
    tac_str = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tR:bv256
}
Program {
\tBlock e Succ [] {
\t\tAssignHavocCmd R
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""
    tac = parse_string(tac_str, path="<s>")
    res = materialize_assumes(tac.program, symbol_sorts=tac.symbol_sorts)
    assert res.program is tac.program
    assert res.hits == {}


def test_materialize_strict_gating_no_invented_facts() -> None:
    """Strict gating: when interval analysis CAN'T prove the
    precondition, no assume is materialized — the pass never invents
    a fact. Use int-typed operands with no range assumes; range
    analysis returns None for both, so neither hint should fire."""
    tac_str = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tA:int
\tB:int
\tY:int
}
Program {
\tBlock e Succ [] {
\t\tAssignHavocCmd A
\t\tAssignHavocCmd B
\t\tAssignExpCmd Y IntCeilDiv(A B)
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""
    tac = parse_string(tac_str, path="<s>")
    res = materialize_assumes(tac.program, symbol_sorts=tac.symbol_sorts)
    # No range info on int-typed havocs; nothing to materialize.
    assert res.hits == {}


def test_materialize_handles_bare_intceildiv_no_narrow_wrapper() -> None:
    """The pass also handles a bare ``IntCeilDiv`` (no
    ``safe_math_narrow_bv256`` wrapper) — useful if a future
    emission chooses an int-typed lhs directly."""
    tac_str = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tA:bv256
\tB:bv256
\tY:bv256
}
Program {
\tBlock e Succ [] {
\t\tAssignHavocCmd A
\t\tAssumeExpCmd LAnd(Ge(A 0x0) Le(A 0xffff))
\t\tAssignHavocCmd B
\t\tAssumeExpCmd LAnd(Ge(B 0x1) Le(B 0xff))
\t\tAssignExpCmd Y IntCeilDiv(A B)
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""
    tac = parse_string(tac_str, path="<s>")
    res = materialize_assumes(tac.program, symbol_sorts=tac.symbol_sorts)
    assert res.hits == {
        "intceildiv_den_positive": 1,
        "intceildiv_lhs_nonneg": 1,
    }
    _check_tac_well_formed(res.program, symbol_sorts=tac.symbol_sorts)
