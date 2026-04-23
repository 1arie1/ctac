from __future__ import annotations


from ctac.parse import parse_string
from ctac.smt import build_vc, render_smt_script

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
    # sea_vc models "failing assert is reachable" as BLK_EXIT →
    # (not <pred>) ∧ <assert-block guard>, plus a standalone
    # `(assert BLK_EXIT)` kickoff. Verify both pieces.
    assert "BLK_EXIT" in rendered
    assert "(not " in rendered
    assert "(check-sat)" in rendered


def test_vc_rendering_is_deterministic() -> None:
    tac = parse_string(TAC_ASSERT_FAIL_VC, path="<string>")
    first = render_smt_script(build_vc(tac))
    second = render_smt_script(build_vc(tac))
    assert first == second


def test_vc_smoke_contains_expected_op_lowering() -> None:
    tac = parse_string(TAC_SMOKE_OPS, path="<string>")
    rendered = render_smt_script(build_vc(tac))
    # sea_vc lowers arithmetic into the Int theory, modding back into
    # the bv256 domain: Add(X, Y) → `(mod (+ X Y) BV256_MOD)`.
    # Comparisons are plain Int operators: Ge → `(>= X Y)`.
    assert "(+ " in rendered
    assert "BV256_MOD" in rendered
    assert "(>= " in rendered


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


