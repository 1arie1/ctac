"""Interval domain tests."""

from __future__ import annotations

from ctac.analysis.abs_int import analyze_intervals
from ctac.analysis.abs_int.interval_ops import Interval
from ctac.ast.nodes import (
    ApplyExpr,
    AssignExpCmd,
    AssignHavocCmd,
    AssumeExpCmd,
    ConstExpr,
    JumpCmd,
    JumpiCmd,
    SymbolRef,
    TacCmd,
    TacExpr,
)
from ctac.ir.models import TacBlock, TacProgram
from ctac.parse import parse_string
from ctac.rewrite.context import RewriteCtx
from ctac.rewrite.range_infer import infer_expr_range


def _block(bid: str, succs: list[str], cmds: list[TacCmd]) -> TacBlock:
    return TacBlock(id=bid, successors=succs, commands=cmds)


def _assign(lhs: str, rhs: TacExpr) -> AssignExpCmd:
    return AssignExpCmd(raw=f"{lhs} = ...", lhs=lhs, rhs=rhs)


def _havoc(lhs: str) -> AssignHavocCmd:
    return AssignHavocCmd(raw=f"{lhs} = havoc", lhs=lhs)


def _assume(cond: TacExpr) -> AssumeExpCmd:
    return AssumeExpCmd(raw="AssumeExpCmd ...", condition=cond)


def _sym(name: str) -> SymbolRef:
    return SymbolRef(name=name)


def _const(v: str) -> ConstExpr:
    return ConstExpr(value=v)


def _apply(op: str, *args: TacExpr) -> ApplyExpr:
    return ApplyExpr(op=op, args=tuple(args))


def _jumpi(then_blk: str, else_blk: str, cond: str) -> JumpiCmd:
    return JumpiCmd(
        raw=f"JumpiCmd {then_blk} {else_blk} {cond}",
        then_target=then_blk,
        else_target=else_blk,
        condition=cond,
    )


def _jump(target: str) -> JumpCmd:
    return JumpCmd(raw=f"JumpCmd {target}", target=target)


# ----------------------------------------------------------------
# Constants and bv-sort defaults


def test_havoc_with_bv64_sort_yields_full_range() -> None:
    program = TacProgram(blocks=[_block("e", [], [_havoc("X")])])
    result = analyze_intervals(program, symbol_sorts={"X": "bv64"})
    assert result.static["X"] == Interval(0, (1 << 64) - 1)


def test_havoc_without_sort_yields_top() -> None:
    program = TacProgram(blocks=[_block("e", [], [_havoc("X")])])
    result = analyze_intervals(program)
    assert result.static["X"] == Interval(None, None)


# ----------------------------------------------------------------
# Entry-block assumes


def test_le_assume_at_entry_promotes_to_static() -> None:
    """Entry-block refinements on DSA-static vars promote to ``static``
    (universal value), not ``local`` — entry dominates everything, so
    the fact is universally true. The assume narrows X to [0, 100]."""
    program = TacProgram(
        blocks=[
            _block(
                "e",
                [],
                [
                    _havoc("X"),
                    _assume(_apply("Le", _sym("X"), _const("0x64"))),
                ],
            ),
        ]
    )
    result = analyze_intervals(program, symbol_sorts={"X": "bv256"})
    assert result.static["X"] == Interval(0, 100)
    assert "X" not in result.per_block_local.get("e", {})


def test_ge_assume_narrows_static_lower_bound() -> None:
    program = TacProgram(
        blocks=[
            _block(
                "e",
                [],
                [
                    _havoc("X"),
                    _assume(_apply("Ge", _sym("X"), _const("0xa"))),
                ],
            ),
        ]
    )
    result = analyze_intervals(program, symbol_sorts={"X": "bv256"})
    assert result.static["X"] == Interval(10, (1 << 256) - 1)


def test_eq_const_assume_pins_static_to_point() -> None:
    program = TacProgram(
        blocks=[
            _block(
                "e",
                [],
                [
                    _havoc("X"),
                    _assume(_apply("Eq", _sym("X"), _const("0x2a"))),
                ],
            ),
        ]
    )
    result = analyze_intervals(program, symbol_sorts={"X": "bv256"})
    assert result.static["X"] == Interval(42, 42)


def test_eq_symbols_intersects_intervals_into_static() -> None:
    # X in [0, 100], Y in [50, 200], assume X == Y => both in [50, 100],
    # universally (entry block).
    program = TacProgram(
        blocks=[
            _block(
                "e",
                [],
                [
                    _havoc("X"),
                    _havoc("Y"),
                    _assume(_apply("Le", _sym("X"), _const("0x64"))),
                    _assume(_apply("Ge", _sym("Y"), _const("0x32"))),
                    _assume(_apply("Le", _sym("Y"), _const("0xc8"))),
                    _assume(_apply("Eq", _sym("X"), _sym("Y"))),
                ],
            ),
        ]
    )
    result = analyze_intervals(
        program, symbol_sorts={"X": "bv256", "Y": "bv256"}
    )
    assert result.static["X"] == Interval(50, 100)
    assert result.static["Y"] == Interval(50, 100)


def test_land_at_entry_refines_both_conjuncts_into_static() -> None:
    program = TacProgram(
        blocks=[
            _block(
                "e",
                [],
                [
                    _havoc("X"),
                    _assume(
                        _apply(
                            "LAnd",
                            _apply("Ge", _sym("X"), _const("0xa")),
                            _apply("Le", _sym("X"), _const("0x14")),
                        )
                    ),
                ],
            ),
        ]
    )
    result = analyze_intervals(program, symbol_sorts={"X": "bv256"})
    assert result.static["X"] == Interval(10, 20)


def test_non_entry_assume_stays_in_local_not_static() -> None:
    """A refinement in a non-entry block isn't universal — it lives in
    ``local[B]`` and ``static[X]`` keeps its universal value."""
    program = TacProgram(
        blocks=[
            _block("e", ["B1"], [_havoc("X"), _jump("B1")]),
            _block(
                "B1",
                [],
                [_assume(_apply("Le", _sym("X"), _const("0x64")))],
            ),
        ]
    )
    result = analyze_intervals(program, symbol_sorts={"X": "bv256"})
    assert result.static["X"] == Interval(0, (1 << 256) - 1)
    assert result.per_block_local["B1"]["X"] == Interval(0, 100)


# ----------------------------------------------------------------
# Arithmetic


def test_intmul_propagates_intervals() -> None:
    # X in [0, 2^32-1]; 0x4000 * X in [0, 2^14 * (2^32-1)].
    program = TacProgram(
        blocks=[
            _block(
                "e",
                [],
                [
                    _havoc("X"),
                    _assume(_apply("Le", _sym("X"), _const("0xffffffff"))),
                    _assign(
                        "Y",
                        _apply("IntMul", _const("0x4000"), _sym("X")),
                    ),
                ],
            ),
        ]
    )
    result = analyze_intervals(program, symbol_sorts={"X": "bv256", "Y": "int"})
    # Y is DSA-static (single def via AssignExpCmd) so its value lives
    # in the static map regardless of which block it was defined in.
    assert result.static["Y"] == Interval(0, (1 << 14) * ((1 << 32) - 1))


def test_intdiv_by_pos_const_scales_bounds() -> None:
    # X in [0, 2^256-1]; floor(X / 0x4000) in [0, 2^242 - 1].
    program = TacProgram(
        blocks=[
            _block(
                "e",
                [],
                [
                    _havoc("X"),
                    _assign("Y", _apply("IntDiv", _sym("X"), _const("0x4000"))),
                ],
            ),
        ]
    )
    result = analyze_intervals(program, symbol_sorts={"X": "bv256", "Y": "int"})
    assert result.static["Y"] == Interval(0, (1 << 242) - 1)


def test_intmod_by_pos_const_bounds_to_divisor_minus_one() -> None:
    program = TacProgram(
        blocks=[
            _block(
                "e",
                [],
                [
                    _havoc("X"),
                    _assign(
                        "Y", _apply("IntMod", _sym("X"), _const("0x100000000"))
                    ),
                ],
            ),
        ]
    )
    result = analyze_intervals(program, symbol_sorts={"X": "bv256", "Y": "int"})
    assert result.static["Y"] == Interval(0, (1 << 32) - 1)


def test_raw_bv_ops_precise_when_un_wrapped_fits() -> None:
    """Raw bv ops (``Add``/``Sub``/``Mul``/``Div``/``Mod``) are
    bvN-modular but the domain treats them as modular intervals: when
    the un-wrapped result fits in ``[0, 2^N-1]``, the bv op didn't
    wrap and the precise interval is sound."""
    program = TacProgram(
        blocks=[
            _block(
                "e",
                [],
                [
                    _havoc("X"),
                    _assume(_apply("Le", _sym("X"), _const("0x10"))),
                    _assign("RA", _apply("Add", _sym("X"), _sym("X"))),
                    _assign("RM", _apply("Mul", _sym("X"), _sym("X"))),
                    _assign("RS", _apply("Sub", _sym("X"), _sym("X"))),
                    _assign("RD", _apply("Div", _sym("X"), _const("0x2"))),
                    _assign(
                        "RMOD", _apply("Mod", _sym("X"), _const("0x8"))
                    ),
                ],
            ),
        ]
    )
    result = analyze_intervals(
        program,
        symbol_sorts={
            "X": "bv256",
            "RA": "bv256",
            "RM": "bv256",
            "RS": "bv256",
            "RD": "bv256",
            "RMOD": "bv256",
        },
    )
    # X in [0, 16]; Add(X, X) un-wrapped in [0, 32], fits → precise.
    assert result.static["RA"] == Interval(0, 32)
    # Mul(X, X) un-wrapped in [0, 256], fits → precise.
    assert result.static["RM"] == Interval(0, 256)
    # Sub(X, X) un-wrapped in [-16, 16]; lo < 0 means wraparound is
    # possible → fall back to the bv range.
    assert result.static["RS"] == Interval(0, (1 << 256) - 1)
    # Div(X, 2) in [0, 8] — never grows; precise.
    assert result.static["RD"] == Interval(0, 8)
    # Mod(X, 8) in [0, 7] — bounded by divisor; precise.
    assert result.static["RMOD"] == Interval(0, 7)


def test_raw_bv_op_falls_back_to_bv_range_on_overflow() -> None:
    """If the un-wrapped result overflows the bv width, the domain
    returns the full bv range (sound overapproximation across the
    wraparound). Verified with X near 2^256."""
    program = TacProgram(
        blocks=[
            _block(
                "e",
                [],
                [
                    _havoc("X"),
                    # X in [0, 2^255]; Add(X, X) un-wrapped up to 2^256
                    # which doesn't fit in bv256 → wrap-possible.
                    _assume(
                        _apply(
                            "Le", _sym("X"), _const(f"{1 << 255:#x}")
                        )
                    ),
                    _assign("R", _apply("Add", _sym("X"), _sym("X"))),
                ],
            ),
        ]
    )
    result = analyze_intervals(
        program, symbol_sorts={"X": "bv256", "R": "bv256"}
    )
    assert result.static["R"] == Interval(0, (1 << 256) - 1)


def test_raw_bv_op_no_width_context_returns_top() -> None:
    """If the assignment's lhs has no bv sort, we have no width to
    drive the modular-interval clamp — fall back to TOP rather than
    pretending the op is unbounded."""
    program = TacProgram(
        blocks=[
            _block(
                "e",
                [],
                [
                    _havoc("X"),
                    _assume(_apply("Le", _sym("X"), _const("0x10"))),
                    _assign("R", _apply("Add", _sym("X"), _sym("X"))),
                ],
            ),
        ]
    )
    # Note: no sort for R → no width context for the bv Add.
    result = analyze_intervals(program, symbol_sorts={"X": "bv256"})
    assert result.static["R"] == Interval(None, None)


def test_safe_math_narrow_around_intadd_keeps_precision() -> None:
    """The wrap-checked form recovers precision: an IntAdd of bounded
    operands wrapped in safe_math_narrow_bv256 is identity when the
    sum fits in bv256."""
    program = TacProgram(
        blocks=[
            _block(
                "e",
                [],
                [
                    _havoc("X"),
                    _assume(_apply("Le", _sym("X"), _const("0x64"))),
                    _havoc("Y"),
                    _assume(_apply("Le", _sym("Y"), _const("0xc8"))),
                    _assign(
                        "S",
                        _apply(
                            "Apply",
                            _sym("safe_math_narrow_bv256:bif"),
                            _apply("IntAdd", _sym("X"), _sym("Y")),
                        ),
                    ),
                ],
            ),
        ]
    )
    result = analyze_intervals(
        program, symbol_sorts={"X": "bv256", "Y": "bv256", "S": "bv256"}
    )
    # X ∈ [0, 100], Y ∈ [0, 200] → IntAdd ∈ [0, 300] → narrow_bv256
    # identity since 300 < 2^256.
    assert result.static["S"] == Interval(0, 300)


# ----------------------------------------------------------------
# Branches: refinement on edge condition


def test_then_edge_refines_via_jumpi_condition() -> None:
    # B0: havoc X (bv256); JumpiCmd to BT/BF on c.
    # In BT, the edge condition `c` is unhelpful as a refinement of X
    # unless we set up a c that compares X. Use Le(X, K) as the cond.
    # The encoding: an AssignExpCmd produces `c`; JumpiCmd uses `c`
    # as a SymbolRef in edge_condition. To exercise refinement on the
    # cmp expr directly, we'd need def-following inside refine_assume,
    # which v1 doesn't do. Instead we verify the bool itself becomes
    # an Interval(0, 1) at the def, and that the SymbolRef edge_cond
    # doesn't narrow X. (Path-sensitivity beyond direct rel-on-symbol
    # is deferred — we just confirm soundness, not precision, here.)
    program = TacProgram(
        blocks=[
            _block(
                "B0",
                ["BT", "BF"],
                [
                    _havoc("X"),
                    _assign("c", _apply("Le", _sym("X"), _const("0x64"))),
                    _jumpi("BT", "BF", "c"),
                ],
            ),
            _block("BT", [], []),
            _block("BF", [], []),
        ]
    )
    result = analyze_intervals(program, symbol_sorts={"X": "bv256", "c": "bool"})
    # `c` is a boolean — must be in [0, 1].
    assert result.static["c"] == Interval(0, 1)
    # X reaches BT and BF unchanged (no direct refinement on X via the
    # SymbolRef edge_cond — sound, less precise).
    assert result.per_block_local["BT"].get("X", result.static["X"]) == Interval(
        0, (1 << 256) - 1
    )


def test_join_lubs_per_block_refinements() -> None:
    # Diamond: B0 havocs X and assumes X <= 100, then splits to BT
    # (assume X <= 10) and BF (assume X >= 50). Join at BJ should
    # produce X in [0, 100] (lub of [0, 10] and [50, 100]).
    program = TacProgram(
        blocks=[
            _block(
                "B0",
                ["BT", "BF"],
                [
                    _havoc("X"),
                    _assume(_apply("Le", _sym("X"), _const("0x64"))),
                    _jumpi("BT", "BF", "c"),
                ],
            ),
            _block(
                "BT",
                ["BJ"],
                [
                    _assume(_apply("Le", _sym("X"), _const("0xa"))),
                    _jump("BJ"),
                ],
            ),
            _block(
                "BF",
                ["BJ"],
                [
                    _assume(_apply("Ge", _sym("X"), _const("0x32"))),
                    _jump("BJ"),
                ],
            ),
            _block("BJ", [], []),
        ]
    )
    result = analyze_intervals(program, symbol_sorts={"X": "bv256"})
    assert result.per_block_local["BT"]["X"] == Interval(0, 10)
    assert result.per_block_local["BF"]["X"] == Interval(50, 100)
    # Join produces convex hull [0, 100].
    assert result.per_block_local["BJ"]["X"] == Interval(0, 100)


# ----------------------------------------------------------------
# DSA-static var defined in a non-entry block stays in static


def test_static_var_def_in_non_entry_block_lands_in_static() -> None:
    # X is havoc'd in B1 (the only def of X), so DSA flags it static.
    program = TacProgram(
        blocks=[
            _block("B0", ["B1"], [_jump("B1")]),
            _block("B1", [], [_havoc("X")]),
        ]
    )
    result = analyze_intervals(program, symbol_sorts={"X": "bv256"})
    # Even though X is defined in B1 (not the entry), DSA classifies
    # it static — so the universal value lives in `static`.
    assert result.static["X"] == Interval(0, (1 << 256) - 1)


# ----------------------------------------------------------------
# Cross-check property against range_infer for DSA-static vars


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


def test_cross_check_with_range_infer_for_dsa_static_vars() -> None:
    """For every DSA-static var, the interval domain's value must
    match `range_infer.infer_expr_range`'s result. They share
    `interval_ops.py` so any disagreement is in the lookup adapter."""
    body = (
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd R0\n"
        "\t\tAssumeExpCmd Le(R0 0xffffffff)\n"
        "\t\tAssignExpCmd R1 IntMul(0x4000(int) R0)\n"
        "\t\tAssignExpCmd R2 Apply(safe_math_narrow_bv256:bif R1)\n"
        "\t}"
    )
    tac = parse_string(
        _wrap(body, syms="R0:bv256\n\tR1:bv256\n\tR2:bv256"), path="<s>"
    )
    ctx = RewriteCtx(tac.program, symbol_sorts=tac.symbol_sorts)
    ctx.set_position("e", 4)
    result = analyze_intervals(tac.program, symbol_sorts=tac.symbol_sorts)

    for var in ("R0", "R1", "R2"):
        ri = infer_expr_range(SymbolRef(var), ctx)
        # Pull the var's value via the read-path: local → static.
        state_local = result.per_block_local.get("e", {})
        if var in state_local:
            iv = state_local[var]
        else:
            iv = result.static.get(var, Interval(None, None))
        # DSA-static var with full bounds == range_infer's tuple.
        assert iv.lo is not None and iv.hi is not None
        assert ri == (iv.lo, iv.hi), f"{var}: range_infer={ri}, domain={iv}"
