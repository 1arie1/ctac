from __future__ import annotations

from ctac.smt.vc import (
    Int,
    IntRange,
    OpConfig,
    OpMode,
    VCBuilder,
    VCConfig,
    add,
    ge,
    render_vc_script,
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
    assert "(assert (=> BLK_BB7 (and (<= 0 Y) (<= Y C_18446744073709551615))))" in text
    assert "(define-fun C_18446744073709551615 () Int\n  18446744073709551615\n)" in text
    assert ":named" not in text


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


def test_bv256_range_uses_readable_named_constants() -> None:
    vc = VCBuilder(VCConfig(check_sat=False))
    x = vc.const("X", Int)
    with vc.block("entry") as b:
        b.assume(vc.ops.bv256.range(x))

    text = render_vc_script(vc.script())

    assert "(define-fun BV256_MOD () Int" in text
    assert "(define-fun BV256_MAX () Int\n  (- BV256_MOD 1)\n)" in text
    assert "(assert (=> BLK_entry (and (<= 0 X) (<= X BV256_MAX))))" in text
