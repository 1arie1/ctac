from __future__ import annotations

import pytest

from ctac.parse import parse_string
from ctac.smt.vc import (
    TacLoweringOptions,
    VCLoweringError,
    VCBuilder,
    VCConfig,
    lower_tac_file,
    lower_tac_program,
    render_vc_script,
)


def _wrap(program: str, symbols: str) -> str:
    return f"""TACSymbolTable {{
{symbols}
}}
Program {{
{program}
}}
Axioms {{
}}
Metas {{}}
"""


def test_tac_lowering_executes_scalar_commands_into_vc_events() -> None:
    tac = parse_string(
        _wrap(
            """
\tBlock entry Succ [] {
\t\tAssignExpCmd R Add(X 1)
\t\tAssumeExpCmd Le(R 10)
\t\tAssertCmd Ge(R 0)
\t}
""",
            "\tX:bv256\n\tR:bv256",
        )
    )

    vc, controls = lower_tac_file(tac, vc=VCBuilder(VCConfig(check_sat=False)))
    text = render_vc_script(vc.script())

    assert controls[0].block == "entry"
    assert "(assert (=> BLK_entry (= R (int.bv256_add X 1))))" in text
    assert "(assert (=> BLK_entry (<= R 10)))" in text
    assert "(assert (=> BLK_entry (>= R 0)))" in text


def test_tac_lowering_collapses_havoc_followed_by_range_assume() -> None:
    tac = parse_string(
        _wrap(
            """
\tBlock entry Succ [] {
\t\tAssignHavocCmd X
\t\tAssumeExpCmd LAnd(Le(0 X) Le(X 255))
\t}
""",
            "\tX:bv256",
        )
    )

    vc, _controls = lower_tac_file(tac, vc=VCBuilder(VCConfig(check_sat=False)))
    text = render_vc_script(vc.script())

    assert "(assert (=> BLK_entry (<= 0 X 255)))" in text
    assert "(assert (=> BLK_entry (and (<= 0 X) (<= X 255))))" not in text


def test_tac_lowering_havoc_emits_bv256_range() -> None:
    tac = parse_string(
        _wrap(
            """
\tBlock entry Succ [] {
\t\tAssignHavocCmd X
\t}
""",
            "\tX:bv256",
        )
    )

    vc, _controls = lower_tac_file(tac, vc=VCBuilder(VCConfig(check_sat=False)))
    text = render_vc_script(vc.script())

    assert "(assert (=> BLK_entry (int.in_bv256 X)))" in text


def test_tac_lowering_havoc_range_refines_one_sided_assume() -> None:
    tac = parse_string(
        _wrap(
            """
\tBlock entry Succ [] {
\t\tAssignHavocCmd X
\t\tAssumeExpCmd Le(X 0xffffffffffffffff)
\t}
""",
            "\tX:bv256",
        )
    )

    vc, _controls = lower_tac_file(tac, vc=VCBuilder(VCConfig(check_sat=False)))
    text = render_vc_script(vc.script())

    assert "(assert (=> BLK_entry (int.in_bv64 X)))" in text
    assert "(assert (=> BLK_entry (<= X BV64_MAX)))" not in text


def test_tac_lowering_rejects_int_where_bool_is_required() -> None:
    tac = parse_string(
        _wrap(
            """
\tBlock entry Succ [] {
\t\tAssumeExpCmd X
\t}
""",
            "\tX:bv256",
        )
    )

    with pytest.raises(VCLoweringError, match="expected Bool expression"):
        lower_tac_file(tac, vc=VCBuilder(VCConfig(check_sat=False)))


def test_tac_lowering_rejects_int_ite_condition() -> None:
    tac = parse_string(
        _wrap(
            """
\tBlock entry Succ [] {
\t\tAssignExpCmd R Ite(X 1 2)
\t}
""",
            "\tX:bv256\n\tR:bv256",
        )
    )

    with pytest.raises(VCLoweringError, match="expected Bool expression"):
        lower_tac_file(tac, vc=VCBuilder(VCConfig(check_sat=False)))


def test_tac_lowering_accepts_bool_ite_in_bool_assignment() -> None:
    tac = parse_string(
        _wrap(
            """
\tBlock entry Succ [] {
\t\tAssignExpCmd b Ite(C true false)
\t\tAssertCmd b
\t}
""",
            "\tC:bool\n\tb:bool",
        )
    )

    vc, _controls = lower_tac_file(tac, vc=VCBuilder(VCConfig(check_sat=False)))
    text = render_vc_script(vc.script())

    # ``ite(C, true, false)`` folds to ``C`` via the on-the-fly
    # simplifier; the assignment lowers to ``(= b C)`` instead of
    # baking the no-op ite into the emitted VC.
    assert "(assert (=> BLK_entry (= b C)))" in text
    assert "(assert (=> BLK_entry b))" in text


def test_tac_lowering_folds_inverted_bool_ite_to_not() -> None:
    """The dual case: ``Ite(C, false, true)`` folds to ``(not C)``."""
    tac = parse_string(
        _wrap(
            """
\tBlock entry Succ [] {
\t\tAssignExpCmd b Ite(C false true)
\t\tAssertCmd b
\t}
""",
            "\tC:bool\n\tb:bool",
        )
    )

    vc, _controls = lower_tac_file(tac, vc=VCBuilder(VCConfig(check_sat=False)))
    text = render_vc_script(vc.script())
    assert "(assert (=> BLK_entry (= b (not C))))" in text


def test_tac_lowering_folds_equal_arms_ite() -> None:
    """``Ite(_, x, x) -> x``: the condition becomes irrelevant."""
    tac = parse_string(
        _wrap(
            """
\tBlock entry Succ [] {
\t\tAssignExpCmd b Ite(C true true)
\t\tAssertCmd b
\t}
""",
            "\tC:bool\n\tb:bool",
        )
    )
    vc, _controls = lower_tac_file(tac, vc=VCBuilder(VCConfig(check_sat=False)))
    text = render_vc_script(vc.script())
    assert "(assert (=> BLK_entry (= b true)))" in text


def test_tac_lowering_rejects_bool_ite_in_int_assignment() -> None:
    tac = parse_string(
        _wrap(
            """
\tBlock entry Succ [] {
\t\tAssignExpCmd R Ite(C true false)
\t}
""",
            "\tC:bool\n\tR:bv256",
        )
    )

    with pytest.raises(VCLoweringError, match="assignment sort mismatch"):
        lower_tac_file(tac, vc=VCBuilder(VCConfig(check_sat=False)))


def test_tac_lowering_rejects_int_ite_in_bool_assignment() -> None:
    tac = parse_string(
        _wrap(
            """
\tBlock entry Succ [] {
\t\tAssignExpCmd b Ite(C 1 0)
\t}
""",
            "\tC:bool\n\tb:bool",
        )
    )

    with pytest.raises(VCLoweringError, match="assignment sort mismatch"):
        lower_tac_file(tac, vc=VCBuilder(VCConfig(check_sat=False)))


def test_tac_lowering_rejects_mixed_sort_equality() -> None:
    tac = parse_string(
        _wrap(
            """
\tBlock entry Succ [] {
\t\tAssignExpCmd b Eq(R true)
\t}
""",
            "\tR:bv256\n\tb:bool",
        )
    )

    with pytest.raises(VCLoweringError, match="sort mismatch"):
        lower_tac_file(tac, vc=VCBuilder(VCConfig(check_sat=False)))


def test_tac_lowering_rejects_bool_operand_to_int_operator() -> None:
    tac = parse_string(
        _wrap(
            """
\tBlock entry Succ [] {
\t\tAssignExpCmd R Add(b 1)
\t}
""",
            "\tb:bool\n\tR:bv256",
        )
    )

    with pytest.raises(VCLoweringError, match="expected Int expression"):
        lower_tac_file(tac, vc=VCBuilder(VCConfig(check_sat=False)))


def test_tac_lowering_strips_tac_symbol_annotations() -> None:
    tac = parse_string(
        _wrap(
            """
\tBlock entry Succ [] {
\t\tAssignExpCmd R:2 Add(X:1 1)
\t\tAssumeExpCmd Le(R:2 10)
\t\tAssertCmd Ge(R:2 0)
\t}
""",
            "\tX:bv256:1\n\tR:bv256:2",
        )
    )

    vc, _controls = lower_tac_file(tac, vc=VCBuilder(VCConfig(check_sat=False)))
    text = render_vc_script(vc.script())

    assert "(declare-const X Int)" in text
    assert "(declare-const R Int)" in text
    assert "(assert (=> BLK_entry (= R (int.bv256_add X 1))))" in text
    assert "(declare-const X:1" not in text
    assert "(declare-const R:2" not in text
    assert "(assert (=> BLK_entry (= R:2" not in text


def test_tac_lowering_supports_twos_complement_builtins() -> None:
    tac = parse_string(
        _wrap(
            """
\tBlock entry Succ [] {
\t\tAssignExpCmd I Apply(unwrap_twos_complement_256:bif R)
\t\tAssignExpCmd R2 Apply(wrap_twos_complement_256:bif I)
\t\tAssertCmd Eq(R2 R)
\t}
""",
            "\tR:bv256\n\tI:int\n\tR2:bv256",
        )
    )

    vc, _controls = lower_tac_file(tac, vc=VCBuilder(VCConfig(check_sat=False)))
    text = render_vc_script(vc.script())

    assert "(define-fun to_s256 ((s Int)) Int (ite (>= s 0) s (+ s BV256_MOD)))" in text
    assert "(define-fun BV256_HALF () Int (div BV256_MOD 2))" in text
    assert "(define-fun from_s256 ((b Int)) Int (ite (< b BV256_HALF) b (- b BV256_MOD)))" in text
    assert "(assert (=> BLK_entry (= I (from_s256 R))))" in text
    assert "(assert (=> BLK_entry (= R2 (to_s256 I))))" in text


def test_tac_lowering_supports_signed_comparisons() -> None:
    """``Slt`` / ``Sle`` / ``Sgt`` route through bv256.slt / bv256.sle
    in the encoded VC. ``Sgt(a, b)`` reuses ``bv256.slt`` with swapped
    args. ``Sge`` does the same for ``sle``. The three define-funs
    (``bv256.is_neg``, ``bv256.slt``, ``bv256.sle``) emit only when
    actually used."""
    tac = parse_string(
        _wrap(
            """
\tBlock entry Succ [] {
\t\tAssignHavocCmd A
\t\tAssignHavocCmd B
\t\tAssignExpCmd B1 Slt(A B)
\t\tAssignExpCmd B2 Sle(A B)
\t\tAssignExpCmd B3 Sgt(A B)
\t\tAssertCmd LAnd(LAnd(B1 B2) B3)
\t}
""",
            "\tA:bv256\n\tB:bv256\n\tB1:bool\n\tB2:bool\n\tB3:bool",
        )
    )

    vc, _controls = lower_tac_file(tac, vc=VCBuilder(VCConfig(check_sat=False)))
    text = render_vc_script(vc.script())

    # Define-funs are emitted exactly once each, with the user-spec'd
    # shape (case-split via is_neg; same-sign falls back to raw <).
    assert (
        "(define-fun bv256.is_neg ((x Int)) Bool (>= x BV256_HALF))"
        in text
    )
    assert (
        "(define-fun bv256.slt ((x Int) (y Int)) Bool "
        "(or (and (bv256.is_neg x) (not (bv256.is_neg y))) "
        "(and (= (bv256.is_neg x) (bv256.is_neg y)) (< x y))))"
    ) in text
    assert (
        "(define-fun bv256.sle ((x Int) (y Int)) Bool "
        "(or (and (bv256.is_neg x) (not (bv256.is_neg y))) "
        "(and (= (bv256.is_neg x) (bv256.is_neg y)) (<= x y))))"
    ) in text
    # Slt(A, B) call site.
    assert "(bv256.slt A B)" in text
    # Sgt(A, B) routes through bv256.slt with swapped args.
    assert "(bv256.slt B A)" in text
    # Sle(A, B) call site.
    assert "(bv256.sle A B)" in text


def test_tac_lowering_omits_signed_define_funs_when_unused() -> None:
    """A program with no signed comparisons doesn't emit the three
    bv256.slt/sle/is_neg define-funs."""
    tac = parse_string(
        _wrap(
            """
\tBlock entry Succ [] {
\t\tAssignHavocCmd X
\t\tAssertCmd Le(X 0x10)
\t}
""",
            "\tX:bv256",
        )
    )
    vc, _controls = lower_tac_file(tac, vc=VCBuilder(VCConfig(check_sat=False)))
    text = render_vc_script(vc.script())
    assert "bv256.is_neg" not in text
    assert "bv256.slt" not in text
    assert "bv256.sle" not in text


def test_tac_lowering_strips_bytemap_symbol_annotations() -> None:
    tac = parse_string(
        _wrap(
            """
\tBlock entry Succ [] {
\t\tAssignHavocCmd M0:1
\t\tAssignExpCmd M1:2 Store(M0:1 I:3 V:4)
\t\tAssignExpCmd R:5 Select(M1:2 I:3)
\t}
""",
            "\tM0:bytemap:1\n\tM1:bytemap:2\n\tI:bv256:3\n\tV:bv256:4\n\tR:bv256:5",
        )
    )

    vc, _controls = lower_tac_file(tac, vc=VCBuilder(VCConfig(check_sat=False)))
    text = render_vc_script(vc.script())

    assert "(declare-fun M0 (Int) Int)" in text
    assert "(define-fun M1 ((idx Int)) Int" in text
    assert "(assert (=> BLK_entry (= R (M1 I))))" in text
    assert "(declare-fun M0:1" not in text
    assert "(define-fun M1:2" not in text
    assert "(assert (=> BLK_entry (= R:5" not in text


def test_tac_lowering_executes_bytemap_store_and_select() -> None:
    tac = parse_string(
        _wrap(
            """
\tBlock entry Succ [] {
\t\tAssignHavocCmd M0
\t\tAssignExpCmd M1 Store(M0 I V)
\t\tAssignExpCmd R Select(M1 I)
\t}
""",
            "\tM0:bytemap\n\tM1:bytemap\n\tI:bv256\n\tV:bv256\n\tR:bv256",
        )
    )

    vc, _controls = lower_tac_file(tac, vc=VCBuilder(VCConfig(check_sat=False)))
    text = render_vc_script(vc.script())

    assert "(declare-fun M0 (Int) Int)" in text
    assert "(define-fun M1 ((idx Int)) Int (ite (= idx I) V (M0 idx)))" in text
    assert "(assert (=> BLK_entry (= R (M1 I))))" in text
    assert "(assert (int.in_bv256 R))" in text


def test_tac_lowering_executes_bytemap_ite_definition() -> None:
    tac = parse_string(
        _wrap(
            """
\tBlock entry Succ [] {
\t\tAssignHavocCmd M0
\t\tAssignHavocCmd M1
\t\tAssignHavocCmd C
\t\tAssignExpCmd M2 Ite(C M0 M1)
\t\tAssignExpCmd R Select(M2 I)
\t}
""",
            "\tM0:bytemap\n\tM1:bytemap\n\tM2:bytemap\n\tC:bool\n\tI:bv256\n\tR:bv256",
        )
    )

    vc, _controls = lower_tac_file(tac, vc=VCBuilder(VCConfig(check_sat=False)))
    text = render_vc_script(vc.script())

    assert "(define-fun M2 ((idx Int)) Int (ite C (M0 idx) (M1 idx)))" in text
    assert "(assert (=> BLK_entry (= R (M2 I))))" in text


def test_tac_lowering_reports_jumpi_edge_conditions_without_assuming_them() -> None:
    tac = parse_string(
        _wrap(
            """
\tBlock entry Succ [then, else] {
\t\tJumpiCmd then else C
\t}
\tBlock then Succ [] {
\t}
\tBlock else Succ [] {
\t}
""",
            "\tC:bool",
        )
    )

    vc, controls = lower_tac_file(tac, vc=VCBuilder(VCConfig(check_sat=False)))
    text = render_vc_script(vc.script())

    assert controls[0].edge_conditions[0][0] == "then"
    assert controls[0].edge_conditions[0][1].text == "C"
    assert controls[0].edge_conditions[1][0] == "else"
    assert controls[0].edge_conditions[1][1].text == "(not C)"
    assert "(assert (=> BLK_entry C))" not in text


def test_tac_lowering_can_skip_assignment_points() -> None:
    tac = parse_string(
        _wrap(
            """
\tBlock entry Succ [] {
\t\tAssignExpCmd X 1
\t\tAssignExpCmd Y 2
\t}
""",
            "\tX:bv256\n\tY:bv256",
        )
    )

    vc, _controls = lower_tac_file(
        tac,
        vc=VCBuilder(VCConfig(check_sat=False)),
        options=TacLoweringOptions(skip_command_points=frozenset({("entry", 0)})),
    )
    text = render_vc_script(vc.script())

    assert "(= X 1)" not in text
    assert "(assert (=> BLK_entry (= Y 2)))" in text


def test_tac_lowering_can_visit_blocks_in_topological_order() -> None:
    tac = parse_string(
        _wrap(
            """
\tBlock b Succ [] {
\t\tAssignExpCmd Y 2
\t}
\tBlock a Succ [b] {
\t\tAssignExpCmd X 1
\t}
""",
            "\tX:bv256\n\tY:bv256",
        )
    )

    vc, controls = lower_tac_program(
        tac.program,
        tac.symbol_sorts,
        vc=VCBuilder(VCConfig(check_sat=False)),
        options=TacLoweringOptions(block_order="topological"),
    )
    text = render_vc_script(vc.script())

    assert tuple(c.block for c in controls) == ("a", "b")
    assert text.index("(= X 1)") < text.index("(= Y 2)")
