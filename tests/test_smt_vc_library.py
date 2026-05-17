from __future__ import annotations

from ctac.smt.vc import (
    AssertionPolicy,
    BytemapConfig,
    FactKind,
    FactPlacement,
    Int,
    IntRange,
    LeinoEdge,
    LeinoLowerer,
    OpConfig,
    OpMode,
    VCBuilder,
    VCConfig,
    add,
    eq,
    ge,
    render_vc_script,
    term,
    true,
)
from ctac.smt import render_any_smt_script
from ctac.smt.model import SmtScript


def test_vc_builder_emits_scoped_defs_ranges_and_unnamed_assertions_by_default() -> None:
    vc = VCBuilder(VCConfig(check_sat=False))
    x = vc.const("X", Int)
    y = vc.const("Y", Int)

    with vc.block("BB7") as b:
        with vc.stmt(17, "Y = X + 1"):
            b.def_(y, add(x, vc.int_lit(1)))
            b.range(y, IntRange.u64())

    text = render_vc_script(vc.script())

    assert "(declare-const BLK_BB7 Bool)" in text
    assert "(assert (=> BLK_BB7 (= Y (+ X 1))))" in text
    assert "(define-fun int.in_bv64 ((x Int)) Bool (and (<= 0 x) (<= x BV64_MAX)))" in text
    assert "(define-fun BV64_MAX () Int (- BV64_MOD 1))" in text
    assert "; block BB7" in text
    assert "; command 17" not in text
    assert "(assert (=> BLK_BB7 (int.in_bv64 Y)))" in text
    assert "; Y = X + 1" not in text
    assert ":named" not in text


def test_vc_builder_can_annotate_assertions_with_raw_commands() -> None:
    vc = VCBuilder(VCConfig(check_sat=False, annotate_with_cmds=True))
    x = vc.const("X", Int)

    with vc.block("BB7") as b:
        with vc.stmt(17, "AssumeExpCmd Le(X 10)"):
            b.assume(ge(x, vc.int_lit(0)))

    text = render_vc_script(vc.script())

    assert "; AssumeExpCmd Le(X 10)" in text
    assert "(assert (=> BLK_BB7 (>= X 0)))" in text


def test_assertion_policy_groups_selected_facts_by_block_scope() -> None:
    vc = VCBuilder(
        VCConfig(
            check_sat=False,
            assertion_policy=AssertionPolicy(
                grouped_kinds=frozenset({FactKind.DEF, FactKind.ASSUME})
            ),
        )
    )
    x = vc.const("X", Int)
    y = vc.const("Y", Int)
    ok = vc.const("OK", Int)

    with vc.block("BB7") as b:
        b.def_(x, vc.int_lit(1))
        b.assume(ge(x, vc.int_lit(0)))
        b.def_(y, vc.ops.bv256.add(x, vc.int_lit(2)))
        b.assert_(ge(ok, vc.int_lit(0)))

    text = render_vc_script(vc.script())

    assert "(assert (=> BLK_BB7 (and (= X 1) (>= X 0) (= Y (int.bv256_add X 2)))))" in text
    assert "(assert (=> BLK_BB7 (>= OK 0)))" in text
    assert "(assert (=> BLK_BB7 (= X 1)))" not in text
    assert "(assert (=> BLK_BB7 (>= X 0)))" not in text
    assert "(assert (=> BLK_BB7 (= Y (int.bv256_add X 2))))" not in text


def test_def_can_emit_inline_define_fun_instead_of_assertion() -> None:
    vc = VCBuilder(VCConfig(check_sat=False))
    x = vc.const("X", Int)
    y = vc.const("Y", Int)

    with vc.block("BB7") as b:
        b.def_(y, add(x, vc.int_lit(1)), inline=True)
        b.assume(ge(y, vc.int_lit(0)))

    text = render_vc_script(vc.script())

    assert "(declare-const X Int)" in text
    assert "(declare-const Y Int)" not in text
    assert "(define-fun Y () Int (+ X 1))" in text
    assert "(assert (=> BLK_BB7 (= Y (+ X 1))))" not in text
    assert "(assert (=> BLK_BB7 (>= Y 0)))" in text


def test_global_fact_placement_elides_scope() -> None:
    vc = VCBuilder(VCConfig(check_sat=False))
    x = vc.const("X", Int)

    with vc.block("BB7"):
        vc.fact(
            FactKind.DEF,
            eq(x, vc.int_lit(1)),
            placement=FactPlacement.GLOBAL,
            origin="static-def",
        )

    text = render_vc_script(vc.script())

    assert "(assert (= X 1))" in text
    assert "(assert (=> BLK_BB7 (= X 1)))" not in text


def test_eligible_global_fact_placement_is_configured_at_lowering_time() -> None:
    scoped = VCBuilder(VCConfig(check_sat=False, globalize_eligible_facts=False))
    scoped_x = scoped.const("X", Int)
    with scoped.block("BB7") as block:
        block.def_(scoped_x, scoped.int_lit(1), placement=FactPlacement.ELIGIBLE_GLOBAL)
    scoped_text = render_vc_script(scoped.script())
    assert "(assert (=> BLK_BB7 (= X 1)))" in scoped_text

    globalized = VCBuilder(VCConfig(check_sat=False, globalize_eligible_facts=True))
    global_x = globalized.const("X", Int)
    with globalized.block("BB7") as block:
        block.def_(global_x, globalized.int_lit(1), placement=FactPlacement.ELIGIBLE_GLOBAL)
    global_text = render_vc_script(globalized.script())
    assert "(assert (= X 1))" in global_text
    assert "(assert (=> BLK_BB7 (= X 1)))" not in global_text


def test_common_bv_max_literals_use_mnemonic_names() -> None:
    vc = VCBuilder(VCConfig(check_sat=False))
    x = vc.const("X", Int)

    vc.fact(FactKind.ASSUME, eq(x, vc.int_lit((1 << 64) - 1)))

    text = render_vc_script(vc.script())

    assert "(define-fun BV64_MOD () Int 18446744073709551616)" in text
    assert "(define-fun BV64_MAX () Int (- BV64_MOD 1))" in text
    assert "(define-fun C_18446744073709551615" not in text
    assert "(assert (= X BV64_MAX))" in text


def test_near_pow2_literals_use_mnemonic_names() -> None:
    vc = VCBuilder(VCConfig(check_sat=False))
    x = vc.const("X", Int)
    y = vc.const("Y", Int)

    vc.fact(FactKind.ASSUME, eq(x, vc.int_lit((1 << 47) - (1 << 15))))
    vc.fact(FactKind.ASSUME, eq(y, vc.int_lit((1 << 33) - 3)))

    text = render_vc_script(vc.script())

    assert "(define-fun POW2_47_MINUS_POW2_15 () Int (- POW2_47 POW2_15))" in text
    assert "(define-fun POW2_33_MINUS_3 () Int (- POW2_33 3))" in text
    assert "(define-fun C_140737488322560" not in text
    assert "(define-fun C_8589934589" not in text
    assert "(assert (= X POW2_47_MINUS_POW2_15))" in text
    assert "(assert (= Y POW2_33_MINUS_3))" in text


def test_near_pow2_small_delta_stays_inline() -> None:
    vc = VCBuilder(VCConfig(check_sat=False))
    x = vc.const("X", Int)

    vc.fact(FactKind.ASSUME, eq(x, vc.int_lit((1 << 33) - 1)))

    text = render_vc_script(vc.script())

    assert "(define-fun POW2_0" not in text
    assert "(define-fun POW2_33_MINUS_1 () Int (- POW2_33 1))" in text
    assert "(assert (= X POW2_33_MINUS_1))" in text


def test_unrecognized_large_literals_are_emitted_inline() -> None:
    vc = VCBuilder(VCConfig(check_sat=False))
    x = vc.const("X", Int)

    vc.fact(FactKind.ASSUME, eq(x, vc.int_lit(12345678901234567890)))

    text = render_vc_script(vc.script())

    assert "(define-fun C_12345678901234567890" not in text
    assert "(assert (= X 12345678901234567890))" in text


def test_raw_cfg_fact_is_emitted_globally() -> None:
    vc = VCBuilder(VCConfig(check_sat=False))
    vc.raw_fact("(=> BLK_a BLK_b)", origin="cfg")

    text = render_vc_script(vc.script())

    assert "(assert (=> BLK_a BLK_b))" in text


def test_dynamic_def_ite_omits_last_guard() -> None:
    vc = VCBuilder(VCConfig(check_sat=False))
    x = vc.const("X", Int)
    g1 = vc.const("G1", true().sort)
    g2 = vc.const("G2", true().sort)

    vc.dynamic_def(
        x,
        (
            (g1, vc.int_lit(10)),
            (g2, vc.int_lit(20)),
            (true(), vc.int_lit(30)),
        ),
    )

    text = render_vc_script(vc.script())

    assert "(assert (= X (ite G1 10 (ite G2 20 30))))" in text


def test_dynamic_def_guarded_emits_per_case_implications() -> None:
    vc = VCBuilder(VCConfig(check_sat=False))
    x = vc.const("X", Int)
    g1 = vc.const("G1", true().sort)
    g2 = vc.const("G2", true().sort)

    vc.dynamic_def(x, ((g1, vc.int_lit(10)), (g2, vc.int_lit(20))), guarded=True)

    text = render_vc_script(vc.script())

    assert "(assert (=> G1 (= X 10)))" in text
    assert "(assert (=> G2 (= X 20)))" in text


def test_assert_failure_objective() -> None:
    vc = VCBuilder(VCConfig(check_sat=False))
    blk = vc.const("BLK_bad", true().sort)
    pred = vc.const("P", true().sort)
    exit_var = vc.const("BLK_EXIT", true().sort)

    vc.assert_failure_objective(exit_var, blk, pred)

    text = render_vc_script(vc.script())

    assert "(assert (=> BLK_EXIT (and BLK_bad (not P))))" in text
    assert "(assert BLK_EXIT)" in text


def test_render_any_smt_script_accepts_legacy_and_vc_scripts() -> None:
    legacy = SmtScript(logic="QF_UF", assertions=("(assert true)",), check_sat=False)
    assert "(assert true)" in render_any_smt_script(legacy)

    vc = VCBuilder(VCConfig(check_sat=False))
    vc.raw_fact("true")
    assert "(assert true)" not in render_any_smt_script(vc.script())


def test_vc_builder_drops_true_facts() -> None:
    vc = VCBuilder(VCConfig(check_sat=False))
    vc.fact(FactKind.ASSUME, true())
    vc.raw_fact("true")

    text = render_vc_script(vc.script())

    assert "(assert true)" not in text


def test_leino_lowerer_emits_ok_equations_from_external_cfg() -> None:
    vc = VCBuilder(
        VCConfig(
            check_sat=False,
            fact_lowerer=LeinoLowerer(
                entry_block="entry",
                edges=(LeinoEdge("entry", "exit", true()),),
            ),
        )
    )
    x = vc.const("X", Int)

    with vc.block("entry") as b:
        b.def_(x, vc.int_lit(1))
        b.assume(ge(x, vc.int_lit(0)))
    with vc.block("exit") as b:
        b.assert_(ge(x, vc.int_lit(1)))

    text = render_vc_script(vc.script())

    assert "(declare-const OK_entry Bool)" in text
    assert "(declare-const OK_exit Bool)" in text
    assert "(assert (= OK_entry (=> (and (= X 1) (>= X 0)) OK_exit)))" in text
    assert "(assert (= OK_exit (>= X 1)))" in text
    assert "(assert (not OK_entry))" in text
    assert "(assert (=> BLK_entry (= X 1)))" not in text


def test_leino_lowerer_puts_edge_premises_on_transition() -> None:
    vc = VCBuilder(
        VCConfig(
            check_sat=False,
            fact_lowerer=LeinoLowerer(
                entry_block="entry",
                edges=(
                    LeinoEdge(
                        "entry",
                        "exit",
                        true(),
                        premises=(eq(term("DYN", Int), term("7", Int)),),
                    ),
                ),
            ),
        )
    )
    x = vc.const("X", Int)

    with vc.block("entry") as b:
        b.assume(ge(x, vc.int_lit(0)))
    with vc.block("exit") as b:
        b.assert_(ge(x, vc.int_lit(1)))

    text = render_vc_script(vc.script())

    assert "(assert (= OK_entry (=> (>= X 0) (=> (= DYN 7) OK_exit))))" in text
    assert "(assert (= OK_exit (>= X 1)))" in text


def test_leino_lowerer_treats_scoped_lemmas_as_block_premises() -> None:
    vc = VCBuilder(
        VCConfig(
            check_sat=False,
            fact_lowerer=LeinoLowerer(
                entry_block="entry",
                edges=(LeinoEdge("entry", "exit", true()),),
            ),
        )
    )
    x = vc.const("X", Int)

    with vc.block("entry"):
        vc.fact(FactKind.LEMMA, ge(x, vc.int_lit(0)))
    with vc.block("exit") as b:
        b.assert_(ge(x, vc.int_lit(1)))

    text = render_vc_script(vc.script())

    assert "(assert (= OK_entry (=> (>= X 0) OK_exit)))" in text
    assert "(assert (=> BLK_entry (>= X 0)))" not in text


def test_leino_lowerer_sanitizes_ok_names() -> None:
    vc = VCBuilder(
        VCConfig(
            check_sat=False,
            fact_lowerer=LeinoLowerer(
                entry_block="0:entry",
                edges=(LeinoEdge("0:entry", "1:exit", true()),),
            ),
        )
    )

    text = render_vc_script(vc.script())

    assert "(declare-const OK__0_entry Bool)" in text
    assert "(declare-const OK__1_exit Bool)" in text
    assert "(assert (= OK__0_entry OK__1_exit))" in text
    assert "(assert (not OK__0_entry))" in text


def test_unsat_core_mode_layers_names_on_assertions() -> None:
    vc = VCBuilder(VCConfig(produce_unsat_cores=True, check_sat=False))
    ok = vc.const("OK", Int)

    with vc.block("entry") as b:
        b.assert_(ge(ok, vc.int_lit(0)))

    text = render_vc_script(vc.script())

    assert "(set-option :produce-unsat-cores true)" in text
    assert "(assert (! (=> BLK_entry (>= OK 0)) :named entry_assert))" in text


def test_uf_operation_records_callsite_binds_direct_result_and_instantiates_lemma() -> None:
    vc = VCBuilder(VCConfig(check_sat=False))
    a = vc.const("A", Int)
    b_term = vc.const("B", Int)
    c = vc.const("C", Int)
    r = vc.const("R", Int)

    with vc.block("math") as block:
        with vc.stmt("3", "R = int.muldiv(A, B, C)"):
            rhs = vc.ops.int_mul_div(a, b_term, c)
            block.def_(r, rhs)

    text = render_vc_script(vc.script())

    assert "(declare-fun int.muldiv (Int Int Int) Int)" in text
    assert "(define-fun lemma_int_mul_div_bounds ((a Int) (b Int) (c Int) (r Int)) Bool" in text
    assert "(assert (=> BLK_math (= R (int.muldiv A B C))))" in text
    assert "(assert (lemma_int_mul_div_bounds A B C R))" in text
    assert len(vc.call_sites) == 1
    assert vc.call_sites[0].bound_result == r


def test_nested_uf_calls_are_tracked_without_incorrect_result_binding() -> None:
    vc = VCBuilder(VCConfig(check_sat=False))
    a = vc.const("A", Int)
    b = vc.const("B", Int)
    c = vc.const("C", Int)
    d = vc.const("D", Int)
    e = vc.const("E", Int)
    r = vc.const("R", Int)

    with vc.block("math") as block:
        left = vc.ops.int_mul_div(a, b, c)
        right = vc.ops.int_ceil_div(d, e)
        block.def_(r, add(left, right))

    text = render_vc_script(vc.script())

    assert len(vc.call_sites) == 2
    assert vc.call_sites[0].bound_result is None
    assert vc.call_sites[1].bound_result is None
    assert "(assert (lemma_int_mul_div_bounds A B C (int.muldiv A B C)))" in text
    assert "(assert (lemma_int_ceil_div_bounds D E (int_ceil_div D E)))" in text


def test_operation_models_can_be_swapped_to_inline_or_define_fun() -> None:
    inline_vc = VCBuilder(
        VCConfig(
            check_sat=False,
            op_models={
                "int.muldiv": OpConfig(
                    mode=OpMode.INLINE,
                    instantiate_lemmas=False,
                )
            },
        )
    )
    a = inline_vc.const("A", Int)
    b = inline_vc.const("B", Int)
    c = inline_vc.const("C", Int)
    r = inline_vc.const("R", Int)
    with inline_vc.block("math") as block:
        block.def_(r, inline_vc.ops.int_mul_div(a, b, c))
    inline_text = render_vc_script(inline_vc.script())
    assert "(= R (div (* A B) C))" in inline_text
    assert "int.muldiv" not in inline_text

    define_vc = VCBuilder(
        VCConfig(
            check_sat=False,
            op_models={
                "int.muldiv": OpConfig(
                    mode=OpMode.DEFINE_FUN,
                    instantiate_lemmas=False,
                )
            },
        )
    )
    a = define_vc.const("A", Int)
    b = define_vc.const("B", Int)
    c = define_vc.const("C", Int)
    r = define_vc.const("R", Int)
    with define_vc.block("math") as block:
        block.def_(r, define_vc.ops.int_mul_div(a, b, c))
    define_text = render_vc_script(define_vc.script())
    assert "(define-fun int.muldiv ((a Int) (b Int) (c Int)) Int" in define_text
    assert "(assert (=> BLK_math (= R (int.muldiv A B C))))" in define_text


def test_common_bv_ranges_use_readable_predicate_define_funs() -> None:
    vc = VCBuilder(VCConfig(check_sat=False))
    a = vc.const("A", Int)
    b_val = vc.const("B", Int)
    c = vc.const("C", Int)
    d = vc.const("D", Int)
    with vc.block("entry") as block:
        block.range(a, IntRange.bv32())
        block.range(b_val, IntRange.bv64())
        block.range(c, IntRange.bv128())
        block.assume(vc.ops.bv256.range(d))

    text = render_vc_script(vc.script())

    assert "(define-fun int.in_bv32 ((x Int)) Bool (and (<= 0 x) (<= x BV32_MAX)))" in text
    assert "(define-fun int.in_bv64 ((x Int)) Bool (and (<= 0 x) (<= x BV64_MAX)))" in text
    assert "(define-fun int.in_bv128 ((x Int)) Bool (and (<= 0 x) (<= x BV128_MAX)))" in text
    assert "(define-fun int.in_bv256 ((x Int)) Bool (and (<= 0 x) (<= x BV256_MAX)))" in text
    assert "(define-fun BV64_MAX () Int (- BV64_MOD 1))" in text
    assert "(define-fun BV256_MAX () Int (- BV256_MOD 1))" in text
    assert "(assert (=> BLK_entry (int.in_bv32 A)))" in text
    assert "(assert (=> BLK_entry (int.in_bv64 B)))" in text
    assert "(assert (=> BLK_entry (int.in_bv128 C)))" in text
    assert "(assert (=> BLK_entry (int.in_bv256 D)))" in text


def test_narrow_ops_are_identity_define_funs_with_range_lemmas() -> None:
    vc = VCBuilder(VCConfig(check_sat=False))
    x32 = vc.const("X32", Int)
    x64 = vc.const("X64", Int)
    x128 = vc.const("X128", Int)
    x256 = vc.const("X256", Int)
    r32 = vc.const("R32", Int)
    r64 = vc.const("R64", Int)
    r128 = vc.const("R128", Int)
    r256 = vc.const("R256", Int)

    with vc.block("entry") as b:
        b.def_(r32, vc.ops.narrow.bv32(x32))
        b.def_(r64, vc.ops.narrow.bv64(x64))
        b.def_(r128, vc.ops.narrow.bv128(x128))
        b.def_(r256, vc.ops.narrow.bv256(x256))

    text = render_vc_script(vc.script())

    for width in (32, 64, 128, 256):
        assert f"(define-fun narrow.bv{width} ((x Int)) Int x)" in text
        assert f"(define-fun lemma_narrow_bv{width}_range ((r Int)) Bool" in text
        assert f"(define-fun int.in_bv{width} ((x Int)) Bool" in text
    assert "(assert (=> BLK_entry (= R32 (narrow.bv32 X32))))" in text
    assert "(assert (=> BLK_entry (= R64 (narrow.bv64 X64))))" in text
    assert "(assert (=> BLK_entry (= R128 (narrow.bv128 X128))))" in text
    assert "(assert (=> BLK_entry (= R256 (narrow.bv256 X256))))" in text
    assert "(assert (lemma_narrow_bv32_range R32))" in text
    assert "(assert (lemma_narrow_bv64_range R64))" in text
    assert "(assert (lemma_narrow_bv128_range R128))" in text
    assert "(assert (lemma_narrow_bv256_range R256))" in text
    assert "lemma_narrow_bv32_range X32" not in text


def test_bv256_add_uses_define_fun_with_ite_body() -> None:
    vc = VCBuilder(VCConfig(check_sat=False))
    x = vc.const("X", Int)
    y = vc.const("Y", Int)
    r = vc.const("R", Int)

    with vc.block("entry") as b:
        b.def_(r, vc.ops.bv256.add(x, y))

    text = render_vc_script(vc.script())

    assert "(define-fun int.bv256_add ((x Int) (y Int)) Int" in text
    assert "(ite (<= (+ x y) BV256_MAX) (+ x y) (- (+ x y) BV256_MOD))" in text
    assert "(assert (=> BLK_entry (= R (int.bv256_add X Y))))" in text


def test_bv256_arithmetic_uses_named_define_funs() -> None:
    vc = VCBuilder(VCConfig(check_sat=False))
    x = vc.const("X", Int)
    y = vc.const("Y", Int)
    s = vc.const("S", Int)
    m = vc.const("M", Int)
    d = vc.const("D", Int)
    rem = vc.const("REM", Int)

    with vc.block("entry") as b:
        b.def_(s, vc.ops.bv256.sub(x, y))
        b.def_(m, vc.ops.bv256.mul(x, y))
        b.def_(d, vc.ops.bv256.div(x, y))
        b.def_(rem, vc.ops.bv256.mod(x, y))

    text = render_vc_script(vc.script())

    assert "(define-fun int.bv256_sub ((x Int) (y Int)) Int" in text
    assert "(ite (>= (- x y) 0) (- x y) (+ (- x y) BV256_MOD))" in text
    assert "(define-fun int.bv256_mul ((x Int) (y Int)) Int (mod (* x y) BV256_MOD))" in text
    assert "(define-fun int.bv256_div ((x Int) (y Int)) Int (div x y))" in text
    assert "(define-fun int.bv256_mod ((x Int) (y Int)) Int (mod x y))" in text
    assert "(assert (=> BLK_entry (= S (int.bv256_sub X Y))))" in text
    assert "(assert (=> BLK_entry (= M (int.bv256_mul X Y))))" in text
    assert "(assert (=> BLK_entry (= D (int.bv256_div X Y))))" in text
    assert "(assert (=> BLK_entry (= REM (int.bv256_mod X Y))))" in text


def test_bytemap_havoc_store_select_uses_binder_range_axiom() -> None:
    vc = VCBuilder(VCConfig(check_sat=False))
    idx = vc.const("I", Int)
    val = vc.const("V", Int)
    result = vc.const("R", Int)
    m0 = vc.bytemap.havoc("M0")
    m1 = vc.bytemap.store("M1", m0, idx, val)

    with vc.block("entry") as block:
        block.def_(result, vc.bytemap.select(m1, idx))

    text = render_vc_script(vc.script())

    assert "(declare-fun M0 (Int) Int)" in text
    assert "(define-fun M1 ((idx Int)) Int (ite (= idx I) V (M0 idx)))" in text
    assert "(assert (=> BLK_entry (= R (M1 I))))" in text
    assert "(assert (int.in_bv256 R))" in text
    assert "(int.in_bv256 (M1 I))" not in text
    assert "(int.in_bv256 (ite" not in text


def test_bytemap_select_range_axiom_can_be_disabled() -> None:
    vc = VCBuilder(
        VCConfig(
            check_sat=False,
            bytemap=BytemapConfig(select_range="none"),
        )
    )
    idx = vc.const("I", Int)
    result = vc.const("R", Int)
    m0 = vc.bytemap.havoc("M0")

    with vc.block("entry") as block:
        block.def_(result, vc.bytemap.select(m0, idx))

    text = render_vc_script(vc.script())

    assert "(assert (=> BLK_entry (= R (M0 I))))" in text
    assert "int.in_bv256 R" not in text


def test_bv256_opaque_ops_use_uf_declarations() -> None:
    vc = VCBuilder(VCConfig(check_sat=False))
    x = vc.const("X", Int)
    y = vc.const("Y", Int)
    left = vc.const("L", Int)
    r = vc.const("R", Int)
    a = vc.const("A", Int)
    xo = vc.const("XO", Int)
    o = vc.const("O", Int)

    with vc.block("entry") as b:
        b.def_(left, vc.ops.bv256.shl(x, y))
        b.def_(r, vc.ops.bv256.lshr(x, y))
        b.def_(a, vc.ops.bv256.and_(x, y))
        b.def_(xo, vc.ops.bv256.xor(x, y))
        b.def_(o, vc.ops.bv256.or_(x, y))

    text = render_vc_script(vc.script())

    for name in (
        "int.bv256_shl",
        "int.bv256_lshr",
        "int.bv256_and",
        "int.bv256_xor",
        "int.bv256_or",
    ):
        assert f"(declare-fun {name} (Int Int) Int)" in text
        assert f"({name} X Y)" in text

    assert "(define-fun lemma_bv256_and_bool ((x Int) (y Int)) Bool" in text
    assert "(define-fun lemma_bv256_xor_bool ((x Int) (y Int)) Bool" in text
    assert "(define-fun lemma_bv256_or_bool ((x Int) (y Int)) Bool" in text
    assert "(ite (and (= x 1) (= y 1)) 1 0)" in text
    assert "(ite (and (= x 0) (= y 0)) 0 1)" in text
    assert "(assert (lemma_bv256_and_bool X Y))" in text
    assert "(assert (lemma_bv256_xor_bool X Y))" in text
    assert "(assert (lemma_bv256_or_bool X Y))" in text


def test_guard_axioms_scopes_all_partial_axioms() -> None:
    """Under --guard-axioms every partial-operator axiom is scoped
    to the originating block. Per the 2026-05-17 soundness fix:
    narrow-range and bytemap select_range are partial axioms; both
    must be guardable or they propagate constraints onto shared
    upstream variables when the originating block is bypassed.
    Total axioms (the boolean-domain lemmas) are also scoped under
    --guard-axioms — that's the flag's contract."""
    vc = VCBuilder(VCConfig(check_sat=False, guard_axioms=True))
    x = vc.const("X", Int)
    y = vc.const("Y", Int)
    a = vc.const("A", Int)
    n = vc.const("N", Int)
    r = vc.const("R", Int)
    m0 = vc.bytemap.havoc("M0")

    with vc.block("mid") as b:
        b.def_(a, vc.ops.bv256.and_(x, y))
        b.def_(n, vc.ops.narrow.bv256(x))
        b.def_(r, vc.bytemap.select(m0, x))

    text = render_vc_script(vc.script())

    # Total bool-domain lemma: scoped under --guard-axioms.
    assert "(assert (=> BLK_mid (lemma_bv256_and_bool X Y)))" in text
    assert "(assert (lemma_bv256_and_bool X Y))" not in text
    # Partial narrow-range axiom: scoped under --guard-axioms.
    assert "(assert (=> BLK_mid (lemma_narrow_bv256_range N)))" in text
    assert "(assert (lemma_narrow_bv256_range N))" not in text
    # Partial bytemap select_range axiom: scoped under --guard-axioms.
    assert "(assert (=> BLK_mid (int.in_bv256 R)))" in text
    assert "(assert (int.in_bv256 R))" not in text


def test_bv256_constant_shift_and_mask_ops_use_readable_define_funs() -> None:
    vc = VCBuilder(VCConfig(check_sat=False))
    x = vc.const("X", Int)
    shl = vc.const("SHL", Int)
    lshr = vc.const("LSHR", Int)
    low = vc.const("LOW", Int)
    high = vc.const("HIGH", Int)
    slc = vc.const("SLC", Int)

    with vc.block("entry") as b:
        b.def_(shl, vc.ops.bv256.shl(x, vc.int_lit(8)))
        b.def_(lshr, vc.ops.bv256.lshr(x, vc.int_lit(8)))
        b.def_(low, vc.ops.bv256.and_(x, vc.int_lit(0xFF)))
        b.def_(high, vc.ops.bv256.and_clear_low(x, 8))
        b.def_(slc, vc.ops.bv256.and_mask(x, 0xFF00))

    text = render_vc_script(vc.script())

    assert "(define-fun POW2_8 () Int 256)" in text
    assert "(define-fun bv256.shl_8 ((x Int)) Int (* x POW2_8))" in text
    assert "(define-fun bv256.lshr_8 ((x Int)) Int (div x POW2_8))" in text
    assert "(define-fun bv256.and_FF ((x Int)) Int (mod x POW2_8))" in text
    assert "(define-fun bv256.and_clear_low_8 ((x Int)) Int (* (div x POW2_8) POW2_8))" in text
    assert "(define-fun bv256.and_slice_8_8 ((x Int)) Int (* (mod (div x POW2_8) POW2_8) POW2_8))" in text
    assert "(assert (=> BLK_entry (= SHL (bv256.shl_8 X))))" in text
    assert "(assert (=> BLK_entry (= LSHR (bv256.lshr_8 X))))" in text
    assert "(assert (=> BLK_entry (= LOW (bv256.and_FF X))))" in text
    assert "(assert (=> BLK_entry (= HIGH (bv256.and_clear_low_8 X))))" in text
    assert "(assert (=> BLK_entry (= SLC (bv256.and_slice_8_8 X))))" in text
