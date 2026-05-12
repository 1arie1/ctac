from __future__ import annotations

from ctac.parse import parse_string
from ctac.smt.vc import VCBuilder, VCConfig, lower_tac_file, render_vc_script


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
    assert "(define-fun M1 ((idx Int)) Int\n  (ite (= idx I) V (M0 idx))\n)" in text
    assert "(assert (=> BLK_entry (= R (M1 I))))" in text
    assert "(assert (int.in_bv256 R))" in text


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
