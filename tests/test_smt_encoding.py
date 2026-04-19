from __future__ import annotations

import pytest

from ctac.parse import parse_string
from ctac.smt import build_vc, render_smt_script
from ctac.smt.encoding.base import SmtEncodingError

TAC_ASSERT_FAIL_VC = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tb:bool
}
Program {
\tBlock entry Succ [ok, bad] {
\t\tAssignExpCmd b true
\t\tJumpiCmd ok bad b
\t}
\tBlock ok Succ [] {
\t\tAssertCmd b "assertion"
\t}
\tBlock bad Succ [] {
\t\tAssumeExpCmd false
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""

TAC_SMOKE_OPS = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tx:bv256
\ty:bv256
\tb:bool
}
Program {
\tBlock entry Succ [fail] {
\t\tAssignExpCmd x 0x1
\t\tAssignExpCmd y Add(x 0x2)
\t\tAssignExpCmd b Ge(y 0x3)
\t\tJumpCmd fail
\t}
\tBlock fail Succ [] {
\t\tAssertCmd b "y >= 3"
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""

TAC_INT_NARROW = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tI1:int
\tR1:bv256
\tb:bool
}
Program {
\tBlock entry Succ [] {
\t\tAssignExpCmd R1 Apply(safe_math_narrow_bv256:bif I1)
\t\tAssignExpCmd b true
\t\tAssertCmd b "shape"
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""


def test_vc_assertion_is_reachability_and_negated_predicate() -> None:
    tac = parse_string(TAC_ASSERT_FAIL_VC, path="<string>")
    script = build_vc(tac)
    rendered = render_smt_script(script)
    assert "(assert (and reach__ok (not" in rendered
    assert "(check-sat)" in rendered


def test_vc_rendering_is_deterministic() -> None:
    tac = parse_string(TAC_ASSERT_FAIL_VC, path="<string>")
    first = render_smt_script(build_vc(tac))
    second = render_smt_script(build_vc(tac))
    assert first == second


def test_vc_smoke_contains_expected_op_lowering() -> None:
    tac = parse_string(TAC_SMOKE_OPS, path="<string>")
    rendered = render_smt_script(build_vc(tac))
    assert "bvadd" in rendered
    assert "bvuge" in rendered


def test_vc_rejects_int_to_bv_narrow_in_qf_bv_encoder() -> None:
    tac = parse_string(TAC_INT_NARROW, path="<string>")
    with pytest.raises(SmtEncodingError, match="QF_BV encoding does not support Int-typed TAC symbols"):
        build_vc(tac)


def test_render_unsat_core_preamble_and_get_unsat_core() -> None:
    tac = parse_string(TAC_ASSERT_FAIL_VC, path="<string>")
    rendered = render_smt_script(build_vc(tac, unsat_core=True))
    assert rendered.startswith(
        "(set-option :produce-unsat-cores true)\n(set-option :smt.core.minimize true)\n"
    )
    assert rendered.rstrip().endswith("(check-sat)\n(get-unsat-core)")


def test_sea_vc_unsat_core_names_tac_asserts_not_cfg() -> None:
    tac = parse_string(TAC_ASSERT_FAIL_VC, path="<string>")
    rendered = render_smt_script(build_vc(tac, encoding="sea_vc", unsat_core=True))
    assert ":named TAC_1" in rendered
    i_cfg = rendered.find("CFG Reachability")
    i_exit = rendered.find("Exit and Assert-Failure Objective")
    assert i_cfg != -1 and i_exit != -1
    assert ":named" not in rendered[i_cfg:i_exit]


def test_vc_path_predicates_unsat_core_objective_not_named() -> None:
    tac = parse_string(TAC_ASSERT_FAIL_VC, path="<string>")
    rendered = render_smt_script(build_vc(tac, encoding="vc-path-predicates", unsat_core=True))
    assert ":named TAC_1" in rendered
    assert "(assert (and reach__ok (not" in rendered
    assert "(assert (! (and reach__ok (not" not in rendered
