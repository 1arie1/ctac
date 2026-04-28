"""Tests for sea_vc's bytemap-ro encoding.

Each memory symbol `M<N>` becomes an uninterpreted function
`Int -> Int`, and each `Select(M, idx)` becomes a UF application
`(M idx)`.
"""

from __future__ import annotations

from ctac.parse import parse_string
from ctac.smt import build_vc, render_smt_script


def _wrap(body: str, syms: str) -> str:
    return f"""TACSymbolTable {{
\tUserDefined {{
\t}}
\tBuiltinFunctions {{
\t}}
\tUninterpretedFunctions {{
\t}}
\t{syms}
}}
Program {{
{body}
}}
Axioms {{
}}
Metas {{
  "0": []
}}
"""


def _render(tac_src: str) -> str:
    tac = parse_string(tac_src, path="<s>")
    script = build_vc(tac, encoding="sea_vc")
    return render_smt_script(script)


def test_bytemap_symbol_declared_as_uf():
    src = _wrap(
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd M16\n"
        "\t\tAssignExpCmd R0 Select(M16 0x10)\n"
        "\t\tAssertCmd false \"boom\"\n"
        "\t}",
        "R0:bv256\n\tM16:bytemap",
    )
    out = _render(src)
    assert "(declare-fun M16 (Int) Int)" in out
    # The UF replaces the const declaration — make sure no stray
    # `(declare-const M16 ...)` leaks through.
    assert "(declare-const M16 " not in out


def test_select_becomes_uf_application():
    src = _wrap(
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd M16\n"
        "\t\tAssignExpCmd R0 Select(M16 0x10)\n"
        "\t\tAssertCmd false \"boom\"\n"
        "\t}",
        "R0:bv256\n\tM16:bytemap",
    )
    out = _render(src)
    # 0x10 = 16 — sea_vc uses decimal literals for small constants.
    assert "(M16 16)" in out


def test_logic_is_qf_ufnia_when_memory_present():
    src = _wrap(
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd M16\n"
        "\t\tAssignExpCmd R0 Select(M16 0x10)\n"
        "\t\tAssertCmd false \"boom\"\n"
        "\t}",
        "R0:bv256\n\tM16:bytemap",
    )
    out = _render(src)
    assert "(set-logic QF_UFNIA)" in out


def test_select_with_symbolref_index():
    src = _wrap(
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd M16\n"
        "\t\tAssignHavocCmd R5\n"
        "\t\tAssignExpCmd R0 Select(M16 R5)\n"
        "\t\tAssertCmd false \"boom\"\n"
        "\t}",
        "R0:bv256\n\tR5:bv256\n\tM16:bytemap",
    )
    out = _render(src)
    assert "(declare-fun M16 (Int) Int)" in out
    assert "(M16 R5)" in out


def test_single_store_emits_define_fun_with_ite_body():
    """``M1 = Store(M0, K, V)`` becomes a single ``define-fun`` with
    the canonical ``(ite (= idx K) V (M0 idx))`` body."""
    src = _wrap(
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd M0\n"
        "\t\tAssignHavocCmd K\n"
        "\t\tAssignHavocCmd V\n"
        "\t\tAssignExpCmd M1 Store(M0 K V)\n"
        "\t\tAssertCmd false \"boom\"\n"
        "\t}",
        "K:bv256\n\tV:bv256\n\tM0:bytemap\n\tM1:bytemap",
    )
    out = _render(src)
    assert "(declare-fun M0 (Int) Int)" in out  # M0 has no Store-def
    assert "(define-fun M1 ((idx Int)) Int (ite (= idx K) V (M0 idx)))" in out
    assert "Bytemap Definitions (lambda form)" in out


def test_chained_stores_emit_one_define_fun_per_step():
    """A chain ``M3 = Store(Store(Store(M0, K1, V1), K2, V2), K3, V3)``
    written as separate AssignExpCmds emits one ``define-fun`` per
    Store, each referencing the previous map by name."""
    src = _wrap(
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd M0\n"
        "\t\tAssignHavocCmd K1\n"
        "\t\tAssignHavocCmd K2\n"
        "\t\tAssignHavocCmd V1\n"
        "\t\tAssignHavocCmd V2\n"
        "\t\tAssignExpCmd M1 Store(M0 K1 V1)\n"
        "\t\tAssignExpCmd M2 Store(M1 K2 V2)\n"
        "\t\tAssertCmd false \"boom\"\n"
        "\t}",
        "K1:bv256\n\tK2:bv256\n\tV1:bv256\n\tV2:bv256\n\tM0:bytemap\n\tM1:bytemap\n\tM2:bytemap",
    )
    out = _render(src)
    # Each step defines its own function referencing the prior one.
    assert "(define-fun M1 ((idx Int)) Int (ite (= idx K1) V1 (M0 idx)))" in out
    assert "(define-fun M2 ((idx Int)) Int (ite (= idx K2) V2 (M1 idx)))" in out


def test_nested_store_in_one_rhs_emits_nested_ite():
    """A single AssignExpCmd whose rhs is a nested Store emits one
    ``define-fun`` with nested ITE in the body."""
    src = _wrap(
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd M0\n"
        "\t\tAssignHavocCmd K1\n"
        "\t\tAssignHavocCmd V1\n"
        "\t\tAssignHavocCmd K2\n"
        "\t\tAssignHavocCmd V2\n"
        "\t\tAssignExpCmd M2 Store(Store(M0 K1 V1) K2 V2)\n"
        "\t\tAssertCmd false \"boom\"\n"
        "\t}",
        "K1:bv256\n\tK2:bv256\n\tV1:bv256\n\tV2:bv256\n\tM0:bytemap\n\tM2:bytemap",
    )
    out = _render(src)
    # Outer Store wraps inner Store body: nested ITE in M2's body.
    assert (
        "(define-fun M2 ((idx Int)) Int "
        "(ite (= idx K2) V2 (ite (= idx K1) V1 (M0 idx))))"
    ) in out
    # M1 is not introduced as an intermediate name.
    assert "(define-fun M1 (" not in out


def test_select_after_store_emits_function_application():
    """``Select`` on a Store-defined map is unchanged shape: ``(M k)``
    function application. The map is now a ``define-fun`` (not a
    ``declare-fun``), but Select doesn't care."""
    src = _wrap(
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd M0\n"
        "\t\tAssignHavocCmd K\n"
        "\t\tAssignHavocCmd V\n"
        "\t\tAssignHavocCmd I\n"
        "\t\tAssignExpCmd M1 Store(M0 K V)\n"
        "\t\tAssignExpCmd R Select(M1 I)\n"
        "\t\tAssertCmd false \"boom\"\n"
        "\t}",
        "K:bv256\n\tV:bv256\n\tI:bv256\n\tR:bv256\n\tM0:bytemap\n\tM1:bytemap",
    )
    out = _render(src)
    assert "(M1 I)" in out


def test_to_s256_and_from_s256_in_preamble():
    """The two twos-complement bif functions are emitted as
    ``define-fun`` in the preamble; ``Apply(wrap_..., e)`` and
    ``Apply(unwrap_..., e)`` lower to ``(to_s256 e)`` /
    ``(from_s256 e)`` respectively."""
    src = _wrap(
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd R0\n"
        "\t\tAssumeExpCmd Le(R0 0xff)\n"
        "\t\tAssignExpCmd I0 Apply(unwrap_twos_complement_256:bif R0)\n"
        "\t\tAssignExpCmd R1 Apply(wrap_twos_complement_256:bif I0)\n"
        "\t\tAssertCmd false \"boom\"\n"
        "\t}",
        "R0:bv256\n\tI0:int\n\tR1:bv256",
    )
    out = _render(src)
    # Preamble contains the two define-funs.
    assert "(define-fun to_s256 ((s Int)) Int (mod s BV256_MOD))" in out
    assert "(define-fun from_s256" in out
    # The bif Applies lower to function applications.
    assert "(from_s256 R0)" in out
    assert "(to_s256 I0)" in out


def test_multi_havoc_bytemap_encodes_as_dynamic_map():
    """Multi-havoc bytemap was previously rejected. Now it's encoded
    as a DSA-dynamic map: per-block havoc-defs become per-block
    declare-funs, then a merged ``define-fun`` selects on block
    guards."""
    src = _wrap(
        "\tBlock e Succ [b1] {\n"
        "\t\tAssignHavocCmd M16\n"
        "\t\tJumpCmd b1\n"
        "\t}\n"
        "\tBlock b1 Succ [] {\n"
        "\t\tAssignHavocCmd M16\n"
        "\t\tAssignExpCmd R0 Select(M16 0x10)\n"
        "\t\tAssertCmd false \"boom\"\n"
        "\t}",
        "R0:bv256\n\tM16:bytemap",
    )
    tac = parse_string(src, path="<s>")
    # Should encode without error (no rejection precondition).
    script = build_vc(tac, encoding="sea_vc")
    rendered = render_smt_script(script)
    assert "(check-sat)" in rendered
    # Multi-havoc map → DSA-dynamic merged define-fun shape.
    assert "Bytemap Definitions (lambda form)" in rendered


def test_ssa_ite_on_maps_lowers_to_application_level_define_fun():
    """TAC SSA can produce ``M = Ite(c, M_t, M_f)`` where the Ite
    branches are bytemap symbols (an SSA-merge of maps). The encoder
    must lift this into a function-application body — otherwise z3
    sees a function-valued equality and silently rewrites the goal
    into array theory, which is incomplete on QF_UFNIA."""
    src = _wrap(
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd M0\n"
        "\t\tAssignHavocCmd M1\n"
        "\t\tAssignHavocCmd C\n"
        "\t\tAssignExpCmd M2 Ite(C M0 M1)\n"
        "\t\tAssignExpCmd R0 Select(M2 0x10)\n"
        "\t\tAssertCmd false \"boom\"\n"
        "\t}",
        "C:bool\n\tR0:bv256\n\tM0:bytemap\n\tM1:bytemap\n\tM2:bytemap",
    )
    out = _render(src)
    # Application-level form: branches reference (M0 idx) / (M1 idx),
    # not raw map symbols (which would be function equality).
    assert "(define-fun M2 ((idx Int)) Int (ite C (M0 idx) (M1 idx)))" in out
    # No bare ``(= M2 ...)`` function equality leaked through.
    assert "(assert (= M2 " not in out


def test_select_emits_bv256_range_axiom_per_application():
    """Bytemap cells are bv256-valued; without a per-application range
    axiom, z3 can pick negative or >BV256_MAX values that satisfy the
    Int-level VC but break model replay through ``ctac run``."""
    src = _wrap(
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd M16\n"
        "\t\tAssignExpCmd R0 Select(M16 0x10)\n"
        "\t\tAssignExpCmd R1 Select(M16 0x20)\n"
        "\t\tAssertCmd false \"boom\"\n"
        "\t}",
        "R0:bv256\n\tR1:bv256\n\tM16:bytemap",
    )
    out = _render(src)
    # One range axiom per unique application.
    assert "(assert (<= 0 (M16 16) BV256_MAX))" in out
    assert "(assert (<= 0 (M16 32) BV256_MAX))" in out


def test_two_separate_bytemaps_each_declared():
    src = _wrap(
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd M1\n"
        "\t\tAssignHavocCmd M2\n"
        "\t\tAssignExpCmd R0 Select(M1 0x10)\n"
        "\t\tAssignExpCmd R1 Select(M2 0x20)\n"
        "\t\tAssertCmd false \"boom\"\n"
        "\t}",
        "R0:bv256\n\tR1:bv256\n\tM1:bytemap\n\tM2:bytemap",
    )
    out = _render(src)
    assert "(declare-fun M1 (Int) Int)" in out
    assert "(declare-fun M2 (Int) Int)" in out
    assert "(M1 16)" in out
    assert "(M2 32)" in out
