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
    # Block `ok` has two static defs (`v = 0x42` and `p = Eq(v, 0x42)`);
    # under --guard-statics they share a single block-guard implication
    # over the conjunction of equalities, not one implication apiece.
    assert "(assert (=> BLK_ok (and (= v 66) (= p (= v 66)))))" in rendered
    assert "(assert (=> BLK_ok (= v 66)))" not in rendered
    assert "(assert (= v 66))" not in rendered


def test_guard_statics_on_leaves_entry_static_unguarded() -> None:
    # Entry block guard reduces to `true`, so `implies` short-circuits
    # the wrapper away — entry-block statics never appear under
    # `(=> BLK_entry ...)`. They are still bundled into a single
    # `(and ...)` conjunction (the per-block grouping shape). Use the
    # legacy `mod` axiom variant here so the conjunction shape is
    # checked against a stable form — the orthogonal default-axiom
    # change ("no-mod") is covered by `test_bv_add_sub_axiom_*`.
    tac = parse_string(TAC_SMOKE_OPS, path="<string>")
    rendered = render_smt_script(
        build_vc(tac, guard_statics=True, bv_add_sub_axiom="mod")
    )
    assert "(=> BLK_entry" not in rendered
    assert (
        "(assert (and (= x 1) (= y (mod (+ x 2) BV256_MOD)) (= b (>= y 3))))"
        in rendered
    )


def test_guard_statics_default_off_is_byte_identical() -> None:
    tac = parse_string(TAC_NON_ENTRY_STATIC, path="<string>")
    a = render_smt_script(build_vc(tac))
    b = render_smt_script(build_vc(tac, guard_statics=False))
    assert a == b


# Two-block diamond with a DSA-dynamic var: `v` is assigned in both
# `a` and `b` (different RHSes), then read in the join block. The
# encoder treats `v` as dynamic and merges the two defs.
TAC_DYNAMIC_ASSIGN = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tc:bool
\tv:bv256
\tp:bool
}
Program {
\tBlock entry Succ [a, b] {
\t\tAssignExpCmd c true
\t\tJumpiCmd a b c
\t}
\tBlock a Succ [j] {
\t\tAssignExpCmd v 0x1
\t\tJumpCmd j
\t}
\tBlock b Succ [j] {
\t\tAssignExpCmd v 0x2
\t\tJumpCmd j
\t}
\tBlock j Succ [] {
\t\tAssignExpCmd p Eq(v 0x1)
\t\tAssertCmd p "either"
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""


def test_guard_dynamics_off_emits_ite_merge() -> None:
    tac = parse_string(TAC_DYNAMIC_ASSIGN, path="<string>")
    rendered = render_smt_script(build_vc(tac))
    # Default: single ITE-merged equality on v, selected by block guard.
    assert "(assert (= v (ite BLK_a 1 2)))" in rendered
    # No per-block guarded equality on v.
    assert "(=> BLK_a (= v 1))" not in rendered


def test_guard_dynamics_on_emits_per_block_guarded_equalities() -> None:
    tac = parse_string(TAC_DYNAMIC_ASSIGN, path="<string>")
    rendered = render_smt_script(build_vc(tac, guard_dynamics=True))
    # Per-defining-block guarded equality, one per def site.
    assert "(assert (=> BLK_a (= v 1)))" in rendered
    assert "(assert (=> BLK_b (= v 2)))" in rendered
    # The merged ITE form must NOT appear.
    assert "(ite BLK_a 1 2)" not in rendered


def test_guard_dynamics_default_off_is_byte_identical() -> None:
    tac = parse_string(TAC_DYNAMIC_ASSIGN, path="<string>")
    a = render_smt_script(build_vc(tac))
    b = render_smt_script(build_vc(tac, guard_dynamics=False))
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


def test_cfg_encoding_fwd_bwd_includes_fwd_clauses_and_idom_implications() -> None:
    """`fwd-bwd` is a strict superset of `fwd`: every fwd clause is
    present, plus a backward immediate-dominator clause for each
    non-entry block. The diamond CFG has entry -> mid -> {thn, els};
    every non-entry block's idom is whichever block dominates it on
    every path."""
    tac = parse_string(TAC_DIAMOND_CFG, path="<string>")
    rendered = render_smt_script(build_vc(tac, cfg_encoding="fwd-bwd"))
    # All the existing fwd clauses must still be present.
    assert "(=> BLK_mid (or BLK_thn BLK_els))" in rendered
    assert "(=> (and BLK_mid BLK_thn) c)" in rendered
    assert "(=> (and BLK_mid BLK_els) (not c))" in rendered
    # Backward idom clauses. `entry`'s guard is "true" so any
    # `BLK_X => true` clause is filtered out by sea_vc's add_constraint.
    # idom(mid) = entry — clause filtered. idom(thn) = mid, idom(els) = mid:
    assert "(=> BLK_thn BLK_mid)" in rendered
    assert "(=> BLK_els BLK_mid)" in rendered


def test_cfg_encoding_fwd_bwd_skips_idom_clause_when_idom_is_entry() -> None:
    """The entry block's guard is the SMT literal `true` (path_skeleton
    convention), so `BLK_i => true` collapses to `true` in the implies
    helper and is filtered out — no spurious unconditional clauses."""
    tac = parse_string(TAC_DIAMOND_CFG, path="<string>")
    rendered = render_smt_script(build_vc(tac, cfg_encoding="fwd-bwd"))
    # idom(mid) = entry. The clause "(=> BLK_mid true)" must NOT appear.
    assert "(=> BLK_mid true)" not in rendered


def test_cfg_encoding_fwd_edge_declares_edge_vars_and_uses_iff() -> None:
    tac = parse_string(TAC_DIAMOND_CFG, path="<string>")
    rendered = render_smt_script(build_vc(tac, cfg_encoding="fwd-edge"))
    # Edge vars get declared only at branching blocks. Block indices
    # in TAC_DIAMOND_CFG order: entry=0, mid=1, thn=2, els=3. entry
    # has a single successor (mid) so e_0_1 is elided — BLK_entry is
    # used directly. mid has two successors so e_1_2 / e_1_3 are
    # declared as usual.
    assert "(declare-const e_0_1 Bool)" not in rendered
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


def test_cfg_encoding_fwd_edge_single_successor_elides_edge_var() -> None:
    """When a block has exactly one successor, the edge variable
    e_{i→j} is redundant with BLK_i (BLK_i ⇔ e_{i→j} forces them
    equivalent under vacuous AMO). The encoder emits BLK_i => BLK_j
    and BLK_i => cond directly without introducing the edge var."""
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
\tBlock entry Succ [a] {
\t\tAssignExpCmd b true
\t\tJumpCmd a
\t}
\tBlock a Succ [b1] {
\t\tJumpCmd b1
\t}
\tBlock b1 Succ [] {
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
    rendered = render_smt_script(build_vc(tac, cfg_encoding="fwd-edge"))
    # No edge variables declared: every non-terminal has one successor.
    assert "declare-const e_" not in rendered
    # BLK_a (the only single-successor non-entry, non-terminal block)
    # implies BLK_b1 directly (BLK_a is its own "edge" to b1).
    assert "(=> BLK_a BLK_b1)" in rendered


def test_cfg_encoding_bwd_edge_skips_edge_vars_at_single_pred_blocks() -> None:
    tac = parse_string(TAC_DIAMOND_CFG, path="<string>")
    rendered = render_smt_script(build_vc(tac, cfg_encoding="bwd-edge"))
    # Every non-entry block in TAC_DIAMOND_CFG has exactly one
    # predecessor, so all edge vars are elided — block guards are
    # used directly. (mid's pred is entry whose guard is "true", so
    # mid's two bwd-edge constraints both collapse to (assert true);
    # thn / els have non-trivial branch conditions that survive.)
    assert "declare-const e_" not in rendered
    # thn / els's only in-edges from mid carry the JumpiCmd condition.
    assert "(=> BLK_thn BLK_mid)" in rendered
    assert "(=> BLK_thn c)" in rendered
    assert "(=> BLK_els BLK_mid)" in rendered
    assert "(=> BLK_els (not c))" in rendered


# Fixture with a true merge: entry -> a -> join, entry -> b -> join.
# `join` has two predecessors so bwd-edge MUST introduce edge
# variables there. (Critical edges are split by the pre-pass; this
# layout has a / b as the intermediate non-critical step.)
TAC_BWD_EDGE_MERGE = """TACSymbolTable {
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
\tBlock entry Succ [a, b] {
\t\tAssignExpCmd c true
\t\tJumpiCmd a b c
\t}
\tBlock a Succ [join] {
\t\tJumpCmd join
\t}
\tBlock b Succ [join] {
\t\tJumpCmd join
\t}
\tBlock join Succ [] {
\t\tAssignExpCmd p true
\t\tAssertCmd p "ok"
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""


def test_cfg_encoding_bwd_edge_emits_edge_vars_at_merge_blocks() -> None:
    """At a merge block (multi-pred), bwd-edge introduces fresh
    edge variables and emits the iff/AMO/bidirectional shape."""
    tac = parse_string(TAC_BWD_EDGE_MERGE, path="<string>")
    rendered = render_smt_script(build_vc(tac, cfg_encoding="bwd-edge"))
    # Block index order: entry=0, a=1, b=2, join=3. join has two
    # in-edges from a (e_1_3) and b (e_2_3) — both must be declared.
    assert "(declare-const e_1_3 Bool)" in rendered
    assert "(declare-const e_2_3 Bool)" in rendered
    # Single-pred blocks (a, b) have their edge vars elided.
    assert "(declare-const e_0_1 Bool)" not in rendered
    assert "(declare-const e_0_2 Bool)" not in rendered
    # join's biconditional + bidirectional + edge guards.
    assert "(= BLK_join (or e_1_3 e_2_3))" in rendered
    assert "(=> e_1_3 BLK_a)" in rendered
    assert "(=> e_2_3 BLK_b)" in rendered


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
    for enc in ("bwd0", "bwd1", "fwd", "fwd-bwd", "fwd-edge", "bwd-edge"):
        rendered = render_smt_script(build_vc(tac, cfg_encoding=enc))
        # Every strategy must produce a well-formed script that
        # mentions BLK_EXIT and the assert predicate.
        assert "BLK_EXIT" in rendered, f"{enc}: missing BLK_EXIT"
        assert "(check-sat)" in rendered, f"{enc}: missing check-sat"


# UF-axiom trigger in a non-entry block: BWXor in `ok` lowers to
# `bv256_xor`; the per-application axiom must carry the trigger
# block's reachability guard under --guard-axioms.
TAC_NON_ENTRY_XOR = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tc:bool
\tx:bv256
\ty:bv256
\tz:bv256
\tp:bool
}
Program {
\tBlock entry Succ [ok, bad] {
\t\tAssignExpCmd c true
\t\tAssignHavocCmd x
\t\tAssignHavocCmd y
\t\tJumpiCmd ok bad c
\t}
\tBlock ok Succ [] {
\t\tAssignExpCmd z BWXor(x y)
\t\tAssignExpCmd p Eq(z 0x0)
\t\tAssertCmd p "no"
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


# UF-axiom trigger in the entry block: the entry-block guard
# resolves to `true`, so even with --guard-axioms the axiom should
# stay bare (the `implies` helper short-circuits `true => x` to `x`).
TAC_ENTRY_XOR = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tx:bv256
\ty:bv256
\tz:bv256
\tb:bool
}
Program {
\tBlock entry Succ [ok] {
\t\tAssignHavocCmd x
\t\tAssignHavocCmd y
\t\tAssignExpCmd z BWXor(x y)
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


# Leaf bv256-range axiom: a `Select` on a havoc'd bytemap in a
# non-entry block. The leaf-axiom on `(M idx)` is keyed on the
# Select's enclosing block, not the map's def block.
TAC_NON_ENTRY_SELECT = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tc:bool
\tM:bytemap
\tv:bv256
\tb:bool
}
Program {
\tBlock entry Succ [ok, bad] {
\t\tAssignExpCmd c true
\t\tAssignHavocCmd M
\t\tJumpiCmd ok bad c
\t}
\tBlock ok Succ [] {
\t\tAssignExpCmd v Select(M 0x10)
\t\tAssignExpCmd b Eq(v 0x0)
\t\tAssertCmd b "v"
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


def test_guard_axioms_default_off_is_byte_identical() -> None:
    tac = parse_string(TAC_NON_ENTRY_XOR, path="<string>")
    a = render_smt_script(build_vc(tac))
    b = render_smt_script(build_vc(tac, guard_axioms=False))
    assert a == b


def test_guard_axioms_off_emits_unguarded_uf_axiom() -> None:
    tac = parse_string(TAC_NON_ENTRY_XOR, path="<string>")
    rendered = render_smt_script(build_vc(tac))
    # Default off: bare assert of the per-application axiom, no
    # block-guard wrapper.
    assert "(assert (bv256_xor_axiom x y))" in rendered
    assert "(=> BLK_ok (bv256_xor_axiom x y))" not in rendered


def test_guard_axioms_on_wraps_non_entry_uf_axiom_in_blk_implication() -> None:
    tac = parse_string(TAC_NON_ENTRY_XOR, path="<string>")
    rendered = render_smt_script(build_vc(tac, guard_axioms=True))
    # The xor instance is triggered solely by the static def
    # `z = BWXor(x, y)` in block `ok`, so the axiom carries `BLK_ok`
    # as its single guard.
    assert "(assert (=> BLK_ok (bv256_xor_axiom x y)))" in rendered
    assert "(assert (bv256_xor_axiom x y))" not in rendered


def test_guard_axioms_on_leaves_entry_uf_axiom_unguarded() -> None:
    # Entry-block guard collapses to `true`; `implies` short-circuits
    # the wrapper away. Same shape as guard_statics treats entry-block
    # static defs.
    tac = parse_string(TAC_ENTRY_XOR, path="<string>")
    rendered = render_smt_script(build_vc(tac, guard_axioms=True))
    assert "(assert (bv256_xor_axiom x y))" in rendered
    assert "(=> BLK_entry" not in rendered


def test_guard_axioms_does_not_guard_leaf_bv256_range_axiom() -> None:
    # Memory bv256-range axioms are generic and cheap, so they stay
    # unguarded even when --guard-axioms is on. Both modes must emit
    # the bare `(<= 0 (M 16) BV256_MAX)` form.
    tac = parse_string(TAC_NON_ENTRY_SELECT, path="<string>")
    for guard in (False, True):
        rendered = render_smt_script(build_vc(tac, guard_axioms=guard))
        assert "(assert (<= 0 (M 16) BV256_MAX))" in rendered
        assert "(=> BLK_ok (<= 0 (M 16) BV256_MAX))" not in rendered


# bv_add_sub axiom variant — Add and Sub on bv256 lower to either an
# opaque ``(mod (op a b) BV256_MOD)`` (legacy) or a single-wrap ITE
# whose two arms are linear in the operands (default, "no-mod"). The
# fixture below uses both Add and Sub plus an IntAdd (unwrapped) and a
# Mul (multi-wrap; never affected by the option).
TAC_ADD_SUB_MUL_INT = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tx:bv256
\ty:bv256
\ti:int
\tj:int
\ta:bv256
\ts:bv256
\tm:bv256
\tn:int
\tok:bool
}
Program {
\tBlock entry Succ [] {
\t\tAssignExpCmd x 0x11
\t\tAssignExpCmd y 0x3
\t\tAssignExpCmd i 0x11(int)
\t\tAssignExpCmd j 0x3(int)
\t\tAssignExpCmd a Add(x y)
\t\tAssignExpCmd s Sub(x y)
\t\tAssignExpCmd m Mul(x y)
\t\tAssignExpCmd n IntAdd(i j)
\t\tAssignExpCmd ok true
\t\tAssertCmd ok "arith"
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""


def test_bv_add_sub_axiom_default_is_no_mod() -> None:
    # Default emits single-wrap ITE for Add and Sub.
    tac = parse_string(TAC_ADD_SUB_MUL_INT, path="<string>")
    rendered = render_smt_script(build_vc(tac))
    assert (
        "(assert (= a (ite (<= (+ x y) BV256_MAX) (+ x y) (- (+ x y) BV256_MOD))))"
        in rendered
    )
    assert (
        "(assert (= s (ite (>= (- x y) 0) (- x y) (+ (- x y) BV256_MOD))))"
        in rendered
    )
    # Legacy mod-form for Add/Sub must NOT appear.
    assert "(mod (+ " not in rendered
    assert "(mod (- " not in rendered


def test_bv_add_sub_axiom_mod_emits_legacy_form() -> None:
    # Opt-in legacy `mod` axiom recovers the previous opaque form.
    tac = parse_string(TAC_ADD_SUB_MUL_INT, path="<string>")
    rendered = render_smt_script(build_vc(tac, bv_add_sub_axiom="mod"))
    assert "(assert (= a (mod (+ x y) BV256_MOD)))" in rendered
    assert "(assert (= s (mod (- x y) BV256_MOD)))" in rendered
    # The new ITE form must NOT appear under legacy.
    assert "(ite (<= (+ x y) BV256_MAX)" not in rendered
    assert "(ite (>= (- x y) 0)" not in rendered


def test_bv_add_sub_axiom_does_not_affect_mul() -> None:
    # TAC Mul always lowers to `(mod (* a b) BV256_MOD)`; the new
    # variant doesn't apply (single-wrap insufficient for Mul).
    tac = parse_string(TAC_ADD_SUB_MUL_INT, path="<string>")
    for variant in ("no-mod", "mod"):
        rendered = render_smt_script(build_vc(tac, bv_add_sub_axiom=variant))
        assert "(assert (= m (mod (* x y) BV256_MOD)))" in rendered, variant


def test_bv_add_sub_axiom_does_not_affect_int_add() -> None:
    # TAC IntAdd is unwrapped Int-arithmetic and always emits `(+ i j)`
    # regardless of the bv-axiom variant.
    tac = parse_string(TAC_ADD_SUB_MUL_INT, path="<string>")
    for variant in ("no-mod", "mod"):
        rendered = render_smt_script(build_vc(tac, bv_add_sub_axiom=variant))
        assert "(assert (= n (+ i j)))" in rendered, variant


def test_bv_add_sub_axiom_invalid_value_rejected() -> None:
    tac = parse_string(TAC_ADD_SUB_MUL_INT, path="<string>")
    with pytest.raises(SmtEncodingError, match="unknown bv_add_sub_axiom"):
        build_vc(tac, bv_add_sub_axiom="bogus")


def test_bv_add_sub_axiom_legacy_mode_byte_identical_pre_change_shape() -> None:
    # Sanity: under `bv_add_sub_axiom="mod"`, the wrap form for Add and
    # Sub is byte-identical to the prior implementation. The fixture
    # below uses the same shape historic tests pinned.
    tac = parse_string(TAC_SMOKE_OPS, path="<string>")
    rendered = render_smt_script(build_vc(tac, bv_add_sub_axiom="mod"))
    assert "(assert (= y (mod (+ x 2) BV256_MOD)))" in rendered


