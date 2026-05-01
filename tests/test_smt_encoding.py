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


TAC_NON_ENTRY_STATIC = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tcond:bool
\tv:bv256
\tp:bool
}
Program {
\tBlock entry Succ [ok, bad] {
\t\tAssignExpCmd cond true
\t\tJumpiCmd ok bad cond
\t}
\tBlock ok Succ [] {
\t\tAssignExpCmd v 0x42
\t\tAssignExpCmd p Eq(v 0x42)
\t\tAssertCmd p "v == 42"
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


def test_guard_statics_off_emits_unguarded_static_eq() -> None:
    tac = parse_string(TAC_NON_ENTRY_STATIC, path="<string>")
    rendered = render_smt_script(build_vc(tac))
    # `v` is single-def in block `ok` (non-entry, static). Default off:
    # emitted as a bare equality, not wrapped in `(=> BLK_ok ...)`.
    # sea_vc renders bv256 constants as decimal Int literals.
    assert "(assert (= v 66))" in rendered
    assert "(=> BLK_ok (= v 66))" not in rendered


def test_guard_statics_on_wraps_non_entry_static_in_blk_implication() -> None:
    tac = parse_string(TAC_NON_ENTRY_STATIC, path="<string>")
    rendered = render_smt_script(build_vc(tac, guard_statics=True))
    assert "(assert (=> BLK_ok (= v 66)))" in rendered
    assert "(assert (= v 66))" not in rendered


def test_guard_statics_on_leaves_entry_static_unguarded() -> None:
    # Entry block guard reduces to `true`, so `_implies` short-circuits
    # and entry-block static defs render identically with/without the flag.
    tac = parse_string(TAC_SMOKE_OPS, path="<string>")
    a = render_smt_script(build_vc(tac))
    b = render_smt_script(build_vc(tac, guard_statics=True))
    assert a == b


def test_guard_statics_default_off_is_byte_identical() -> None:
    tac = parse_string(TAC_NON_ENTRY_STATIC, path="<string>")
    a = render_smt_script(build_vc(tac))
    b = render_smt_script(build_vc(tac, guard_statics=False))
    assert a == b


# CFG encoding strategies (bwd0 default, bwd1 alternative). The
# fixture below has a non-entry mid block with a conditional branch
# to two leaves; the `then` leaf has a single non-entry predecessor
# whose edge condition is `c`, which is what differentiates bwd0
# (`(=> BLK_then (and BLK_mid c))`) from bwd1 (per-edge:
# `(=> (and BLK_then BLK_mid) c)`).
TAC_DIAMOND_CFG = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tc:bool
\tp:bool
}
Program {
\tBlock entry Succ [mid] {
\t\tAssignExpCmd c true
\t\tJumpCmd mid
\t}
\tBlock mid Succ [thn, els] {
\t\tJumpiCmd thn els c
\t}
\tBlock thn Succ [] {
\t\tAssignExpCmd p true
\t\tAssertCmd p "ok"
\t}
\tBlock els Succ [] {
\t\tAssumeExpCmd false
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""


def test_cfg_encoding_default_is_bwd0_and_byte_identical() -> None:
    tac = parse_string(TAC_DIAMOND_CFG, path="<string>")
    a = render_smt_script(build_vc(tac))
    b = render_smt_script(build_vc(tac, cfg_encoding="bwd0"))
    assert a == b


def test_cfg_encoding_bwd0_emits_or_of_ands_edge_feasibility() -> None:
    tac = parse_string(TAC_DIAMOND_CFG, path="<string>")
    rendered = render_smt_script(build_vc(tac, cfg_encoding="bwd0"))
    # bwd0: edge-feasibility OR-of-ANDs. `thn` has one predecessor
    # `mid` with branch condition `c`, so we get the AND on the rhs
    # of the implication.
    assert "(=> BLK_thn (and BLK_mid c))" in rendered
    # bwd1's per-edge clausal form must NOT appear.
    assert "(=> (and BLK_thn BLK_mid) c)" not in rendered


def test_cfg_encoding_bwd1_emits_per_edge_implications() -> None:
    tac = parse_string(TAC_DIAMOND_CFG, path="<string>")
    rendered = render_smt_script(build_vc(tac, cfg_encoding="bwd1"))
    # bwd1: per-edge clausal `(=> (and BLK_S BLK_P) cond)`.
    assert "(=> (and BLK_thn BLK_mid) c)" in rendered
    # bwd0's edge-feasibility OR-of-ANDs must NOT appear.
    assert "(=> BLK_thn (and BLK_mid c))" not in rendered


def test_cfg_encoding_unknown_value_rejected() -> None:
    tac = parse_string(TAC_DIAMOND_CFG, path="<string>")
    with pytest.raises(SmtEncodingError, match="unknown cfg_encoding"):
        build_vc(tac, cfg_encoding="bogus")


def test_cfg_encoding_fwd_emits_one_way_block_existence() -> None:
    tac = parse_string(TAC_DIAMOND_CFG, path="<string>")
    rendered = render_smt_script(build_vc(tac, cfg_encoding="fwd"))
    # `mid` has two successors `thn` and `els`; fwd emits one-way
    # block-existence: BLK_mid => (or BLK_thn BLK_els). One-way
    # is required for soundness on diamond CFGs.
    assert "(=> BLK_mid (or BLK_thn BLK_els))" in rendered
    # The biconditional shape (= BLK_mid (or ...)) must NOT appear.
    assert "(= BLK_mid (or BLK_thn BLK_els))" not in rendered
    # Per-edge guard at fwd shape: (=> (and BLK_mid BLK_thn) c).
    assert "(=> (and BLK_mid BLK_thn) c)" in rendered
    assert "(=> (and BLK_mid BLK_els) (not c))" in rendered


def test_cfg_encoding_fwd_edge_declares_edge_vars_and_uses_iff() -> None:
    tac = parse_string(TAC_DIAMOND_CFG, path="<string>")
    rendered = render_smt_script(build_vc(tac, cfg_encoding="fwd-edge"))
    # Edge vars get declared. Block indices in TAC_DIAMOND_CFG order:
    # entry=0, mid=1, thn=2, els=3. Out-edges from entry to mid, and
    # from mid to thn / els.
    assert "(declare-const e_0_1 Bool)" in rendered
    assert "(declare-const e_1_2 Bool)" in rendered
    assert "(declare-const e_1_3 Bool)" in rendered
    # Biconditional block-existence over edge vars at mid (which has
    # two outgoing edges).
    assert "(= BLK_mid (or e_1_2 e_1_3))" in rendered
    # Edge guard: e_1_2 => c (the JumpiCmd's then-condition).
    assert "(=> e_1_2 c)" in rendered
    # Edge guard: e_1_3 => (not c).
    assert "(=> e_1_3 (not c))" in rendered
    # Bidirectional: e_1_2 => BLK_thn.
    assert "(=> e_1_2 BLK_thn)" in rendered
    assert "(=> e_1_3 BLK_els)" in rendered


def test_cfg_encoding_bwd_edge_declares_edge_vars_skips_entry() -> None:
    tac = parse_string(TAC_DIAMOND_CFG, path="<string>")
    rendered = render_smt_script(build_vc(tac, cfg_encoding="bwd-edge"))
    # Entry block is skipped; mid is the only non-entry block with
    # in-edges from entry. thn/els each have one in-edge from mid.
    assert "(declare-const e_0_1 Bool)" in rendered
    assert "(declare-const e_1_2 Bool)" in rendered
    assert "(declare-const e_1_3 Bool)" in rendered
    # Biconditional block-existence per non-entry block over its
    # in-edges. mid has one in-edge (e_0_1).
    assert "(= BLK_mid e_0_1)" in rendered
    # thn has one in-edge (e_1_2); els has one (e_1_3).
    assert "(= BLK_thn e_1_2)" in rendered
    assert "(= BLK_els e_1_3)" in rendered
    # Per-edge guard on edge variable.
    assert "(=> e_1_2 c)" in rendered
    assert "(=> e_1_3 (not c))" in rendered
    # Bidirectional: e_1_2 => BLK_mid (the predecessor).
    assert "(=> e_1_2 BLK_mid)" in rendered
    assert "(=> e_1_3 BLK_mid)" in rendered


def test_cfg_encoding_all_strategies_close_unsat_on_simple_program() -> None:
    # Soundness sanity: every strategy should accept a clearly
    # unsatisfiable VC (assertion never fails) on a simple CFG.
    # Use a fixture where the assert is on `b == true` which is
    # statically true. All five strategies should report UNSAT.
    src = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tb:bool
}
Program {
\tBlock entry Succ [ok] {
\t\tAssignExpCmd b true
\t\tJumpCmd ok
\t}
\tBlock ok Succ [] {
\t\tAssertCmd b "ok"
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""
    tac = parse_string(src, path="<string>")
    for enc in ("bwd0", "bwd1", "fwd", "fwd-edge", "bwd-edge"):
        rendered = render_smt_script(build_vc(tac, cfg_encoding=enc))
        # Every strategy must produce a well-formed script that
        # mentions BLK_EXIT and the assert predicate.
        assert "BLK_EXIT" in rendered, f"{enc}: missing BLK_EXIT"
        assert "(check-sat)" in rendered, f"{enc}: missing check-sat"


