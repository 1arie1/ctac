"""Polynomial-degree domain tests."""

from __future__ import annotations

from ctac.analysis.abs_int import analyze_polynomial_degree
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


def _run_single(cmds: list[TacCmd]):
    program = TacProgram(blocks=[_block("B0", [], cmds)])
    return analyze_polynomial_degree(program)


def test_constant_assignment_has_degree_zero() -> None:
    res = _run_single([_assign("R", _const("5"))])
    assert res.final_state["R"] == 0
    assert res.program_max_degree == 0


def test_linear_via_havoc_plus_const() -> None:
    res = _run_single([_havoc("R"), _assign("S", _apply("Add", _sym("R"), _const("1")))])
    assert res.final_state["R"] == 1
    assert res.final_state["S"] == 1


def test_quadratic_self_multiply() -> None:
    res = _run_single([_havoc("R"), _assign("S", _apply("Mul", _sym("R"), _sym("R")))])
    assert res.final_state["S"] == 2


def test_cubic_chain() -> None:
    res = _run_single(
        [
            _havoc("X"),
            _havoc("Y"),
            _havoc("Z"),
            _assign("R1", _apply("Mul", _sym("X"), _sym("Y"))),
            _assign("R2", _apply("Mul", _sym("R1"), _sym("Z"))),
        ]
    )
    assert res.final_state["R1"] == 2
    assert res.final_state["R2"] == 3


def test_division_bumps_degree() -> None:
    res = _run_single(
        [
            _havoc("X"),
            _havoc("Y"),
            _assign("S", _apply("Div", _sym("X"), _sym("Y"))),
        ]
    )
    # max(deg(X), deg(Y)) + 1 = 1 + 1 = 2
    assert res.final_state["S"] == 2


def test_havoc_yields_degree_one() -> None:
    res = _run_single([_havoc("R")])
    assert res.final_state["R"] == 1


def test_ite_takes_max_of_branches() -> None:
    res = _run_single(
        [
            _havoc("c"),
            _havoc("X"),
            _havoc("Y"),
            _assign(
                "R",
                _apply("Ite", _sym("c"), _sym("X"), _apply("Mul", _sym("X"), _sym("Y"))),
            ),
        ]
    )
    assert res.final_state["R"] == 2


def test_unrecognized_apply_yields_top() -> None:
    res = _run_single([_assign("R", _apply("MysteryOp", _const("0")))])
    assert res.saw_top is True
    assert res.final_state["R"] == "TOP"
    assert "R" in res.top_symbols


def test_top_is_absorbing_through_arithmetic() -> None:
    res = _run_single(
        [
            _assign("R", _apply("MysteryOp", _const("0"))),
            _assign("S", _apply("Add", _sym("R"), _const("1"))),
        ]
    )
    assert res.final_state["S"] == "TOP"
    assert res.saw_top is True


def test_safe_math_narrow_is_identity_for_degree() -> None:
    res = _run_single(
        [
            _havoc("X"),
            _havoc("Y"),
            _assign(
                "R",
                _apply(
                    "safe_math_narrow_bv256:bif",
                    _apply("Mul", _sym("X"), _sym("Y")),
                ),
            ),
        ]
    )
    assert res.final_state["R"] == 2


def test_select_treated_as_fresh_symbol() -> None:
    res = _run_single(
        [
            _assign("R", _apply("Select", _sym("M"), _sym("idx"))),
        ]
    )
    assert res.final_state["R"] == 1


def test_bitwise_and_with_const_mask_is_linear() -> None:
    res = _run_single(
        [
            _havoc("X"),
            _assign("R", _apply("BWAnd", _sym("X"), _const("0xff"))),
        ]
    )
    # Mask op with a constant: linear in X.
    assert res.final_state["R"] == 1


def test_bitwise_and_two_symbolic_bumps_degree() -> None:
    res = _run_single(
        [
            _havoc("X"),
            _havoc("Y"),
            _assign("R", _apply("BWAnd", _sym("X"), _sym("Y"))),
        ]
    )
    # Both symbolic: genuinely nonlinear.
    assert res.final_state["R"] == 2


def test_div_by_const_is_linear() -> None:
    res = _run_single(
        [
            _havoc("X"),
            _assign("R", _apply("Div", _sym("X"), _const("8"))),
        ]
    )
    # x / c is linear scaling (multiplication by 1/c).
    assert res.final_state["R"] == 1


def test_div_of_const_by_var_bumps_degree() -> None:
    res = _run_single(
        [
            _havoc("X"),
            _assign("R", _apply("Div", _const("8"), _sym("X"))),
        ]
    )
    # c / x introduces 1/x — genuinely nonlinear.
    assert res.final_state["R"] == 2


def test_mod_by_const_is_linear() -> None:
    res = _run_single(
        [
            _havoc("X"),
            _assign("R", _apply("Mod", _sym("X"), _const("8"))),
        ]
    )
    assert res.final_state["R"] == 1


def test_shift_by_const_is_linear() -> None:
    res = _run_single(
        [
            _havoc("X"),
            _assign("R", _apply("ShiftLeft", _sym("X"), _const("4"))),
        ]
    )
    # x << k = x * 2^k for constant k — linear.
    assert res.final_state["R"] == 1


def test_shift_by_var_bumps_degree() -> None:
    res = _run_single(
        [
            _havoc("X"),
            _havoc("K"),
            _assign("R", _apply("ShiftLeft", _sym("X"), _sym("K"))),
        ]
    )
    # Variable shift count is genuinely nonlinear.
    assert res.final_state["R"] == 2


def test_bwnot_is_linear() -> None:
    res = _run_single(
        [
            _havoc("X"),
            _assign("R", _apply("BWNot", _sym("X"))),
        ]
    )
    # Bit-complement is linear (~x = -x - 1).
    assert res.final_state["R"] == 1


def test_div_then_mul_by_same_const_stays_linear() -> None:
    # The kvault chain `(R / [2^14]) *int [2^14]` should not inflate
    # degree when both operations are by constants.
    res = _run_single(
        [
            _havoc("X"),
            _assign(
                "R",
                _apply(
                    "Mul",
                    _apply("Div", _sym("X"), _const("0x4000")),
                    _const("0x4000"),
                ),
            ),
        ]
    )
    assert res.final_state["R"] == 1


def test_two_block_straight_line() -> None:
    program = TacProgram(
        blocks=[
            _block("B0", ["B1"], [_havoc("R"), _jump("B1")]),
            _block(
                "B1", [], [_assign("S", _apply("Add", _sym("R"), _sym("R")))]
            ),
        ]
    )
    res = analyze_polynomial_degree(program)
    assert res.final_state["R"] == 1
    assert res.final_state["S"] == 1


def test_branch_merge_takes_max_via_join() -> None:
    # B0 (havoc X) -> B1 / B2, B1: R = X, B2: R = X*X, B3: T = R + 1
    program = TacProgram(
        blocks=[
            _block(
                "B0",
                ["B1", "B2"],
                [_havoc("X"), _havoc("c"), _jumpi("B1", "B2", "c")],
            ),
            _block("B1", ["B3"], [_assign("R", _sym("X")), _jump("B3")]),
            _block(
                "B2",
                ["B3"],
                [
                    _assign("R", _apply("Mul", _sym("X"), _sym("X"))),
                    _jump("B3"),
                ],
            ),
            _block(
                "B3", [], [_assign("T", _apply("Add", _sym("R"), _const("1")))]
            ),
        ]
    )
    res = analyze_polynomial_degree(program)
    # R is dynamic — join over the two defs gives degree 2.
    assert res.final_state["R"] == 2
    # T = R + 1 → degree 2.
    assert res.final_state["T"] == 2


def test_multiple_havoc_sites_keep_degree_one() -> None:
    program = TacProgram(
        blocks=[
            _block("B0", ["B1", "B2"], [_havoc("c"), _jumpi("B1", "B2", "c")]),
            _block("B1", ["B3"], [_havoc("R"), _jump("B3")]),
            _block("B2", ["B3"], [_havoc("R"), _jump("B3")]),
            _block("B3", [], [_assign("S", _sym("R"))]),
        ]
    )
    res = analyze_polynomial_degree(program)
    assert res.final_state["R"] == 1
    assert res.final_state["S"] == 1


def test_assume_assert_jump_are_no_ops_for_degree() -> None:
    # An assume on R doesn't change R's degree; v1 doesn't refine.
    res = _run_single(
        [
            _havoc("R"),
            _assume(_apply("Gt", _sym("R"), _const("0"))),
            _assign("S", _sym("R")),
        ]
    )
    assert res.final_state["R"] == 1
    assert res.final_state["S"] == 1


def test_program_max_degree_picks_largest() -> None:
    res = _run_single(
        [
            _assign("A", _const("5")),
            _havoc("B"),
            _assign("C", _apply("Mul", _sym("B"), _sym("B"))),
        ]
    )
    assert res.program_max_degree == 2


def test_program_max_degree_ignores_top() -> None:
    res = _run_single(
        [
            _havoc("X"),
            _assign("M", _apply("MysteryOp", _const("0"))),
            _assign("Q", _apply("Mul", _sym("X"), _sym("X"))),
        ]
    )
    assert res.program_max_degree == 2
    assert res.saw_top is True
    assert res.final_state["M"] == "TOP"
