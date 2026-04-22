"""Tests for sea_vc's bytemap-ro encoding.

Each memory symbol `M<N>` becomes an uninterpreted function
`Int -> Int`, and each `Select(M, idx)` becomes a UF application
`(M idx)`.
"""

from __future__ import annotations

import pytest

from ctac.parse import parse_string
from ctac.smt import build_vc, render_smt_script
from ctac.smt.encoding.base import SmtEncodingError


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


def test_multi_havoc_bytemap_is_rejected():
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
    with pytest.raises(SmtEncodingError, match="multiple definitions"):
        build_vc(tac, encoding="sea_vc")


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
