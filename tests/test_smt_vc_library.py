from __future__ import annotations

from ctac.smt.vc import (
    AssertionPolicy,
    FactKind,
    Int,
    IntRange,
    LeinoEdge,
    LeinoLowerer,
    OpConfig,
    OpMode,
    VCBuilder,
    VCConfig,
    add,
    ge,
    render_vc_script,
    true,
)


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
    assert "(define-fun int.in_bv64 ((x Int)) Bool\n  (and (<= 0 x) (<= x BV64_MAX))\n)" in text
    assert "(define-fun BV64_MAX () Int\n  (- BV64_MOD 1)\n)" in text
    assert "(assert (=> BLK_BB7 (int.in_bv64 Y)))" in text
    assert ":named" not in text


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
    assert "(define-fun Y () Int\n  (+ X 1)\n)" in text
    assert "(assert (=> BLK_BB7 (= Y (+ X 1))))" not in text
    assert "(assert (=> BLK_BB7 (>= Y 0)))" in text


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
        with vc.stmt("3", "R = int.mul_div(A, B, C)"):
            rhs = vc.ops.int_mul_div(a, b_term, c)
            block.def_(r, rhs)

    text = render_vc_script(vc.script())

    assert "(declare-fun int_mul_div (Int Int Int) Int)" in text
    assert "(define-fun lemma_int_mul_div_bounds ((a Int) (b Int) (c Int) (r Int)) Bool" in text
    assert "(assert (=> BLK_math (= R (int_mul_div A B C))))" in text
    assert "(assert (=> BLK_math (lemma_int_mul_div_bounds A B C R)))" in text
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
    assert "(assert (=> BLK_math (lemma_int_mul_div_bounds A B C (int_mul_div A B C))))" in text
    assert "(assert (=> BLK_math (lemma_int_ceil_div_bounds D E (int_ceil_div D E))))" in text


def test_operation_models_can_be_swapped_to_inline_or_define_fun() -> None:
    inline_vc = VCBuilder(
        VCConfig(
            check_sat=False,
            op_models={
                "int.mul_div": OpConfig(
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
    assert "int_mul_div" not in inline_text

    define_vc = VCBuilder(
        VCConfig(
            check_sat=False,
            op_models={
                "int.mul_div": OpConfig(
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
    assert "(define-fun int_mul_div ((a Int) (b Int) (c Int)) Int" in define_text
    assert "(assert (=> BLK_math (= R (int_mul_div A B C))))" in define_text


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

    assert "(define-fun int.in_bv32 ((x Int)) Bool\n  (and (<= 0 x) (<= x BV32_MAX))\n)" in text
    assert "(define-fun int.in_bv64 ((x Int)) Bool\n  (and (<= 0 x) (<= x BV64_MAX))\n)" in text
    assert "(define-fun int.in_bv128 ((x Int)) Bool\n  (and (<= 0 x) (<= x BV128_MAX))\n)" in text
    assert "(define-fun int.in_bv256 ((x Int)) Bool\n  (and (<= 0 x) (<= x BV256_MAX))\n)" in text
    assert "(define-fun BV64_MAX () Int\n  (- BV64_MOD 1)\n)" in text
    assert "(define-fun BV256_MAX () Int\n  (- BV256_MOD 1)\n)" in text
    assert "(assert (=> BLK_entry (int.in_bv32 A)))" in text
    assert "(assert (=> BLK_entry (int.in_bv64 B)))" in text
    assert "(assert (=> BLK_entry (int.in_bv128 C)))" in text
    assert "(assert (=> BLK_entry (int.in_bv256 D)))" in text


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
    assert "(define-fun int.bv256_mul ((x Int) (y Int)) Int\n  (mod (* x y) BV256_MOD)\n)" in text
    assert "(define-fun int.bv256_div ((x Int) (y Int)) Int\n  (div x y)\n)" in text
    assert "(define-fun int.bv256_mod ((x Int) (y Int)) Int\n  (mod x y)\n)" in text
    assert "(assert (=> BLK_entry (= S (int.bv256_sub X Y))))" in text
    assert "(assert (=> BLK_entry (= M (int.bv256_mul X Y))))" in text
    assert "(assert (=> BLK_entry (= D (int.bv256_div X Y))))" in text
    assert "(assert (=> BLK_entry (= REM (int.bv256_mod X Y))))" in text


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
