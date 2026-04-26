"""Unit tests for R6 (ceiling-division chain collapse)."""

from __future__ import annotations

from ctac.ast.nodes import (
    ApplyExpr,
    AssignExpCmd,
    AssignHavocCmd,
    AssumeExpCmd,
    SymbolRef,
)
from ctac.parse import parse_string
from ctac.rewrite import rewrite_program
from ctac.rewrite.rules import (
    N1_SHIFTED_BWAND,
    N2_LOW_MASK,
    N3_HIGH_MASK,
    N4_SHR_CONST,
    R6_CEILDIV,
)


def _tac_with_ceildiv_chain(
    *,
    num_range: tuple[str, str] = ("0x0", "0xffffffff"),
    den_range: tuple[str, str] = ("0x1", "0xffff"),
    final_bwand: str = "0xffffffffffffffff",
    final_shr: str = "0x40",
) -> str:
    """Build a minimal TAC that contains the ceiling-division idiom.

    The chain is in a single block. After N2/N4 normalize the BWAnd/Shr,
    R6 should recognize the full pattern on the R_ceil assignment.
    """
    num_lo, num_hi = num_range
    den_lo, den_hi = den_range
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
\tR_floor:bv256
\tI_prod:bv256
\tR_prod:bv256
\tR_trunc:bv256
\tR_high:bv256
\tX1:bv256
\tX2:bv256
\tR_ceil:bv256
}}
Program {{
\tBlock e Succ [] {{
\t\tAssignHavocCmd R_num
\t\tAssumeExpCmd LAnd(Ge(R_num {num_lo} ) Le(R_num {num_hi} ) )
\t\tAssignHavocCmd R_den
\t\tAssumeExpCmd LAnd(Ge(R_den {den_lo} ) Le(R_den {den_hi} ) )
\t\tAssignExpCmd R_floor Apply(safe_math_narrow_bv256:bif IntDiv(R_num R_den ))
\t\tAssignExpCmd I_prod IntMul(R_floor R_den )
\t\tAssignExpCmd R_prod Apply(safe_math_narrow_bv256:bif I_prod )
\t\tAssignExpCmd R_trunc BWAnd(R_prod {final_bwand} )
\t\tAssignExpCmd R_high Sub(0x0 ShiftRightLogical(R_prod {final_shr} ) )
\t\tAssignExpCmd X1 Sub(R_high Ite(Lt(R_num R_trunc ) 0x1 0x0 ) )
\t\tAssignExpCmd X2 Sub(R_num R_trunc )
\t\tAssignExpCmd R_ceil Apply(safe_math_narrow_bv256:bif IntAdd(R_floor Ite(LAnd(Eq(X2 0x0 ) Eq(X1 0x0 ) ) 0x0 0x1 )))
\t}}
}}
Axioms {{
}}
Metas {{
  "0": []
}}
"""


def _pipeline_with_r6():
    # Run the bit-op normalization rules first, then R6.
    return (N1_SHIFTED_BWAND, N2_LOW_MASK, N3_HIGH_MASK, N4_SHR_CONST, R6_CEILDIV)


def _rhs(res_program, lhs):
    for b in res_program.blocks:
        for cmd in b.commands:
            if isinstance(cmd, AssignExpCmd) and cmd.lhs == lhs:
                return cmd.rhs
    raise AssertionError(f"no assignment for {lhs}")


def test_r6_fires_on_full_chain():
    """The full chain collapses to an unconstrained R_ceil + ceiling-bound assumes.

    R6 reuses the host LHS (R_ceil) as the new havoc name: the original
    chain-final ``AssignExpCmd R_ceil ...`` is dropped, replaced by
    ``AssignHavocCmd R_ceil`` followed by the polynomial bounds.

    Pinned to the legacy emission via ``use_int_ceil_div=False`` so this
    test continues to assert on the havoc form. The new IntCeilDiv
    emission is covered separately below.
    """
    tac = parse_string(_tac_with_ceildiv_chain(), path="<s>")
    res = rewrite_program(
        tac.program, _pipeline_with_r6(), use_int_ceil_div=False
    )
    assert res.hits_by_rule.get("R6", 0) == 1
    # No new symbol is introduced; R_ceil's name is reused.
    assert res.extra_symbols == ()
    # R_ceil is now a havoc, not an AssignExpCmd.
    block = res.program.blocks[0]
    r_ceil_havocs = [c for c in block.commands if isinstance(c, AssignHavocCmd) and c.lhs == "R_ceil"]
    assert len(r_ceil_havocs) == 1
    r_ceil_assigns = [c for c in block.commands if isinstance(c, AssignExpCmd) and c.lhs == "R_ceil"]
    assert not r_ceil_assigns

    # Bound assumes reference the reused R_ceil name.
    def _refers_to_r_ceil(e):
        if isinstance(e, SymbolRef):
            return e.name == "R_ceil"
        if isinstance(e, ApplyExpr):
            return any(_refers_to_r_ceil(a) for a in e.args)
        return False

    new_assumes = [
        c
        for c in block.commands
        if isinstance(c, AssumeExpCmd) and _refers_to_r_ceil(c.condition)
    ]
    assert len(new_assumes) >= 2  # Ge and Lt; maybe a third Ge(R_ceil, 0)


def test_r6_does_not_fire_with_wrong_bwand_mask():
    """If R_trunc's mask isn't 2^64 - 1, the chain shape doesn't match."""
    tac = parse_string(
        _tac_with_ceildiv_chain(final_bwand="0xff"),  # 2^8 - 1 instead
        path="<s>",
    )
    res = rewrite_program(tac.program, _pipeline_with_r6())
    assert res.hits_by_rule.get("R6", 0) == 0


def test_r6_does_not_fire_with_wrong_shift():
    """Wrong shift amount (not 0x40) breaks the high-bits derivation."""
    tac = parse_string(
        _tac_with_ceildiv_chain(final_shr="0x20"),
        path="<s>",
    )
    res = rewrite_program(tac.program, _pipeline_with_r6())
    assert res.hits_by_rule.get("R6", 0) == 0


def test_r6_requires_positive_denominator_range():
    """If R_den's range has lo <= 0, R6 skips (unsound otherwise)."""
    tac = parse_string(
        _tac_with_ceildiv_chain(den_range=("0x0", "0xffff")),  # allows 0
        path="<s>",
    )
    res = rewrite_program(tac.program, _pipeline_with_r6())
    assert res.hits_by_rule.get("R6", 0) == 0


def test_r6_intermediates_become_dead():
    """After simplify_pipeline + iterated DCE, chain intermediates are gone.

    DCE is a single pass over current liveness; a chain of dead-but-still-
    referenced vars needs multiple sweeps to clean up transitively (the
    inner var's def keeps the outer var appearing live on the first pass).
    Iterate until fixed point.
    """
    from ctac.analysis import eliminate_dead_assignments
    from ctac.rewrite.rules import simplify_pipeline

    tac = parse_string(_tac_with_ceildiv_chain(), path="<s>")
    res = rewrite_program(tac.program, simplify_pipeline)
    program = res.program
    while True:
        dce = eliminate_dead_assignments(program)
        if not dce.removed:
            break
        program = dce.program

    remaining_lhs = {
        cmd.lhs
        for b in program.blocks
        for cmd in b.commands
        if isinstance(cmd, (AssignExpCmd, AssignHavocCmd))
    }
    # None of the chain intermediates remain after iterated DCE.
    for stale in ("R_floor", "I_prod", "R_prod", "R_trunc", "R_high", "X1", "X2"):
        assert stale not in remaining_lhs, f"{stale} survived DCE after R6"


def test_r6_dsa_still_valid_after_rewrite():
    """Post-rewrite DSA check reports no shape issues."""
    from ctac.analysis import analyze_dsa
    from ctac.rewrite.rules import simplify_pipeline

    tac = parse_string(_tac_with_ceildiv_chain(), path="<s>")
    res = rewrite_program(tac.program, simplify_pipeline)
    dsa = analyze_dsa(res.program)
    shape_issues = [i for i in dsa.issues if i.kind == "shape"]
    assert not shape_issues, f"DSA shape issues after R6: {shape_issues}"


def test_r6_emits_intceildiv_when_flag_on():
    """With ``use_int_ceil_div=True`` (default), R6 emits a single
    ``AssignExpCmd R_ceil Apply(safe_math_narrow_bv256:bif IntCeilDiv(R_num,
    R_den))`` and no havoc / no polynomial-bound assumes. The 6 chain
    intermediates become dead and DCE removes them."""
    tac = parse_string(_tac_with_ceildiv_chain(), path="<s>")
    res = rewrite_program(tac.program, _pipeline_with_r6(), use_int_ceil_div=True)
    assert res.hits_by_rule.get("R6", 0) == 1

    block = res.program.blocks[0]

    # No havoc on R_ceil (legacy emission shape) and no extra symbols
    # registered for R_ceil (its sort stays bv256).
    r_ceil_havocs = [
        c for c in block.commands if isinstance(c, AssignHavocCmd) and c.lhs == "R_ceil"
    ]
    assert not r_ceil_havocs
    assert res.extra_symbols == ()

    # Exactly one AssignExpCmd assigns R_ceil, with the new RHS shape.
    r_ceil_assigns = [
        c for c in block.commands if isinstance(c, AssignExpCmd) and c.lhs == "R_ceil"
    ]
    assert len(r_ceil_assigns) == 1
    rhs = r_ceil_assigns[0].rhs
    assert isinstance(rhs, ApplyExpr)
    assert rhs.op == "Apply"
    assert len(rhs.args) == 2
    bif_tag, inner = rhs.args
    assert isinstance(bif_tag, SymbolRef)
    assert bif_tag.name == "safe_math_narrow_bv256:bif"
    assert isinstance(inner, ApplyExpr)
    assert inner.op == "IntCeilDiv"
    assert len(inner.args) == 2

    # The legacy bound assumes (Ge(IntMul(R_den, R_ceil), R_num) etc.)
    # are NOT emitted on the new path.
    def _refers_to_r_ceil(e):
        if isinstance(e, SymbolRef):
            return e.name == "R_ceil"
        if isinstance(e, ApplyExpr):
            return any(_refers_to_r_ceil(a) for a in e.args)
        return False

    new_r_ceil_assumes = [
        c
        for c in block.commands
        if isinstance(c, AssumeExpCmd) and _refers_to_r_ceil(c.condition)
    ]
    assert not new_r_ceil_assumes, (
        f"new path should not emit R_ceil assumes; got {new_r_ceil_assumes}"
    )


def test_r6_falls_back_to_havoc_when_flag_off():
    """``use_int_ceil_div=False`` preserves the legacy havoc + bounds
    emission verbatim — performance-validated and serving as the
    benchmark for the new path."""
    tac = parse_string(_tac_with_ceildiv_chain(), path="<s>")
    res = rewrite_program(
        tac.program, _pipeline_with_r6(), use_int_ceil_div=False
    )
    assert res.hits_by_rule.get("R6", 0) == 1

    block = res.program.blocks[0]
    # Legacy: a single havoc on R_ceil and no AssignExpCmd assigning it.
    r_ceil_havocs = [
        c for c in block.commands if isinstance(c, AssignHavocCmd) and c.lhs == "R_ceil"
    ]
    assert len(r_ceil_havocs) == 1
    r_ceil_assigns = [
        c for c in block.commands if isinstance(c, AssignExpCmd) and c.lhs == "R_ceil"
    ]
    assert not r_ceil_assigns

    # No IntCeilDiv ApplyExpr on the legacy path.
    def _has_int_ceil_div(e):
        if isinstance(e, ApplyExpr):
            if e.op == "IntCeilDiv":
                return True
            return any(_has_int_ceil_div(a) for a in e.args)
        return False

    for cmd in block.commands:
        rhs = getattr(cmd, "rhs", None) or getattr(cmd, "condition", None)
        if rhs is not None:
            assert not _has_int_ceil_div(rhs), (
                "legacy path leaked an IntCeilDiv emission"
            )
