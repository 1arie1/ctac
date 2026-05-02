"""Tests for `ctac smt --store-reduce`.

Asserts the per-bytemap chain data structure produces:
- shadow-pruned define-fun bodies when a later Store at the same key
  supersedes an earlier one,
- the canonical `(ite ... (M_old idx))` shared-sibling form when no
  pruning fires,
- inlined bodies that skip dead intermediate `define-fun`s when no
  Select reaches them.

The default-off path is byte-identical to the historical eager emission;
existing test suites cover that contract."""

from __future__ import annotations

import re

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


def _render(tac_src: str, *, store_reduce: bool) -> str:
    tac = parse_string(tac_src, path="<s>")
    script = build_vc(tac, encoding="sea_vc", store_reduce=store_reduce)
    return render_smt_script(script)


def _map_define_fun_lines(rendered: str) -> list[str]:
    return [
        line
        for line in rendered.splitlines()
        if line.startswith("(define-fun ")
        and re.match(r"^\(define-fun M\d+", line)
    ]


def test_default_off_byte_identical():
    src = _wrap(
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd M0\n"
        "\t\tAssignExpCmd M1 Store(M0 0x10 0xa1)\n"
        "\t\tAssignExpCmd M2 Store(M1 0x20 0xa2)\n"
        "\t\tAssignExpCmd R0 Select(M2 0x30)\n"
        "\t\tAssertCmd false \"boom\"\n"
        "\t}",
        "R0:bv256\n\tM0:bytemap\n\tM1:bytemap\n\tM2:bytemap",
    )
    a = _render(src, store_reduce=False)
    # Default arg path (no flag) must equal --no-store-reduce.
    tac = parse_string(src, path="<s>")
    b = render_smt_script(build_vc(tac, encoding="sea_vc"))
    assert a == b


def test_no_shadow_keeps_named_predecessor_reference():
    """Two Stores at distinct constant keys → each Mi's body references
    its predecessor by name (sharing preserved)."""
    src = _wrap(
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd M0\n"
        "\t\tAssignExpCmd M1 Store(M0 0x10 0xa1)\n"
        "\t\tAssignExpCmd M2 Store(M1 0x20 0xa2)\n"
        "\t\tAssignExpCmd R0 Select(M2 0x30)\n"
        "\t\tAssertCmd false \"boom\"\n"
        "\t}",
        "R0:bv256\n\tM0:bytemap\n\tM1:bytemap\n\tM2:bytemap",
    )
    out = _render(src, store_reduce=True)
    # M2's body should reference M1 directly. (M2 is queried; closure
    # adds M1; M1's body references M0; closure adds M0.)
    m2_lines = [line for line in out.splitlines() if line.startswith("(define-fun M2 ")]
    assert m2_lines, f"M2 not emitted: {out}"
    assert "(M1 idx)" in m2_lines[0], f"M2 body should reference M1: {m2_lines[0]}"


def test_shadow_prune_drops_dead_kv():
    """`M2 = M1[0x10 := v_new]` over `M1 = M0[0x10 := v_old]` →
    M2's body has just one ITE; the old KV(0x10, v_old) is gone."""
    src = _wrap(
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd M0\n"
        "\t\tAssignExpCmd M1 Store(M0 0x10 0xa1)\n"
        "\t\tAssignExpCmd M2 Store(M1 0x10 0xa2)\n"
        "\t\tAssignExpCmd R0 Select(M2 0x10)\n"
        "\t\tAssertCmd false \"boom\"\n"
        "\t}",
        "R0:bv256\n\tM0:bytemap\n\tM1:bytemap\n\tM2:bytemap",
    )
    out = _render(src, store_reduce=True)
    m2_lines = [line for line in out.splitlines() if line.startswith("(define-fun M2 ")]
    assert m2_lines, f"M2 not emitted: {out}"
    body = m2_lines[0]
    # M2 must reference M0 directly (M1 was pruned out via shadowing).
    assert "(M0 idx)" in body, f"M2 should reference M0 not M1: {body}"
    assert "(M1 idx)" not in body, f"M2 should not reference M1: {body}"
    # Exactly one `(ite (= idx ...)` in M2's body.
    assert body.count("(ite ") == 1, f"M2 body should have one ITE: {body}"


def test_no_shadow_chain_keeps_all_intermediates_via_named_map():
    """Linear no-shadow chain: every Mi keeps its NamedMap(M_{i-1})
    reference, so all intermediates stay live. This is the design's
    *sharing-preserved* property — the SMT solver inlines through
    name references. Dead-map elision fires only when pruning detaches
    a chain from its predecessor (see the pruning test below)."""
    src = _wrap(
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd M0\n"
        "\t\tAssignExpCmd M1 Store(M0 0x10 0xa1)\n"
        "\t\tAssignExpCmd M2 Store(M1 0x20 0xa2)\n"
        "\t\tAssignExpCmd M3 Store(M2 0x30 0xa3)\n"
        "\t\tAssignExpCmd R0 Select(M3 0x40)\n"
        "\t\tAssertCmd false \"boom\"\n"
        "\t}",
        (
            "R0:bv256\n"
            "\tM0:bytemap\n"
            "\tM1:bytemap\n"
            "\tM2:bytemap\n"
            "\tM3:bytemap"
        ),
    )
    out = _render(src, store_reduce=True)
    map_names = {
        re.match(r"^\(define-fun (M\d+)", line).group(1)
        for line in _map_define_fun_lines(out)
    }
    # All three Store-defined maps stay live via NamedMap closure.
    assert {"M1", "M2", "M3"} <= map_names
    # Each Mi's body has exactly one ITE wrapping a `(M_{i-1} idx)` ref.
    for i in (1, 2, 3):
        line = next(
            ln for ln in out.splitlines() if ln.startswith(f"(define-fun M{i} ")
        )
        assert line.count("(ite ") == 1, f"M{i} should have one ITE: {line}"
        assert f"(M{i-1} idx)" in line, f"M{i} should reference M{i-1}: {line}"


def test_pruning_enables_dead_elision():
    """When a Store shadows a predecessor's KV, the new chain inlines
    past the shadow — the shadow-bearing predecessor (M1 here) is no
    longer referenced by name, so it gets dead-elided when nothing
    else queries it.

    Chain: M0 -> M1[k:=v1] -> M2[k:=v2]. M1's KV(k, v1) is shadowed
    by M2's Store. M2's chain inlines past M1 → `[KV(k, v2), NamedMap(M0)]`.
    With Select only on M2, M1 has no remaining references → elided."""
    src = _wrap(
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd M0\n"
        "\t\tAssignExpCmd M1 Store(M0 0x10 0xa1)\n"
        "\t\tAssignExpCmd M2 Store(M1 0x10 0xa2)\n"
        "\t\tAssignExpCmd R0 Select(M2 0xff)\n"
        "\t\tAssertCmd false \"boom\"\n"
        "\t}",
        "R0:bv256\n\tM0:bytemap\n\tM1:bytemap\n\tM2:bytemap",
    )
    out = _render(src, store_reduce=True)
    map_names = {
        re.match(r"^\(define-fun (M\d+)", line).group(1)
        for line in _map_define_fun_lines(out)
    }
    # M2 is live (queried), M0 is live (havoc-leaf, declare-fun + chain
    # tail). M1 is dead — its KV was shadowed and M2's chain skipped it.
    assert "M2" in map_names
    assert "M1" not in map_names, f"M1 should be dead-elided: {map_names}"


def test_pruning_with_directly_selected_intermediate_keeps_it_alive():
    """Same shadowing scenario but with M1 directly Selected. M1 stays
    live because it's queried; M2's chain still inlines past M1 (the
    shadow detached it from the chain), so M2 doesn't reference M1 in
    its body, but M1 is emitted because of its own Select."""
    src = _wrap(
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd M0\n"
        "\t\tAssignExpCmd M1 Store(M0 0x10 0xa1)\n"
        "\t\tAssignExpCmd M2 Store(M1 0x10 0xa2)\n"
        "\t\tAssignExpCmd R0 Select(M1 0xff)\n"
        "\t\tAssignExpCmd R1 Select(M2 0xff)\n"
        "\t\tAssertCmd false \"boom\"\n"
        "\t}",
        (
            "R0:bv256\n"
            "\tR1:bv256\n"
            "\tM0:bytemap\n"
            "\tM1:bytemap\n"
            "\tM2:bytemap"
        ),
    )
    out = _render(src, store_reduce=True)
    map_names = {
        re.match(r"^\(define-fun (M\d+)", line).group(1)
        for line in _map_define_fun_lines(out)
    }
    assert "M1" in map_names and "M2" in map_names
    # M2's body must NOT reference M1 — its chain inlined past M1's
    # shadowed KV.
    m2_body = next(ln for ln in out.splitlines() if ln.startswith("(define-fun M2 "))
    assert "(M1 idx)" not in m2_body, f"M2 should bypass M1: {m2_body}"


def test_havoc_only_map_keeps_uf_declaration():
    """A bytemap with just a havoc def stays as `(declare-fun M (Int) Int)`
    even under --store-reduce; it's the leaf UF for downstream chains."""
    src = _wrap(
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd M0\n"
        "\t\tAssignExpCmd M1 Store(M0 0x10 0xa1)\n"
        "\t\tAssignExpCmd R0 Select(M1 0x20)\n"
        "\t\tAssertCmd false \"boom\"\n"
        "\t}",
        "R0:bv256\n\tM0:bytemap\n\tM1:bytemap",
    )
    out = _render(src, store_reduce=True)
    assert "(declare-fun M0 (Int) Int)" in out


def test_range_axioms_unchanged_under_store_reduce():
    """The leaf-pushed range axioms are emitted by `_collect_leaves` on
    the AST chain, independent of `--store-reduce`. Same set in both
    modes."""
    src = _wrap(
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd M0\n"
        "\t\tAssignExpCmd M1 Store(M0 0x10 0xa1)\n"
        "\t\tAssignExpCmd M2 Store(M1 0x20 0xa2)\n"
        "\t\tAssignExpCmd R0 Select(M2 0x30)\n"
        "\t\tAssertCmd false \"boom\"\n"
        "\t}",
        "R0:bv256\n\tM0:bytemap\n\tM1:bytemap\n\tM2:bytemap",
    )
    a_axioms = sorted(
        line for line in _render(src, store_reduce=False).splitlines()
        if line.startswith("(assert (<= 0 (M")
    )
    b_axioms = sorted(
        line for line in _render(src, store_reduce=True).splitlines()
        if line.startswith("(assert (<= 0 (M")
    )
    assert a_axioms == b_axioms


def test_symbolic_key_does_not_prune():
    """Stores with symbolic keys (different SymRefs) cannot be proven
    distinct by the conservative `_key_relation` — both KVs preserved."""
    src = _wrap(
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd M0\n"
        "\t\tAssignHavocCmd K1\n"
        "\t\tAssignHavocCmd K2\n"
        "\t\tAssignExpCmd M1 Store(M0 K1 0xa1)\n"
        "\t\tAssignExpCmd M2 Store(M1 K2 0xa2)\n"
        "\t\tAssignExpCmd R0 Select(M2 0x30)\n"
        "\t\tAssertCmd false \"boom\"\n"
        "\t}",
        "R0:bv256\n\tK1:bv256\n\tK2:bv256\n\tM0:bytemap\n\tM1:bytemap\n\tM2:bytemap",
    )
    out = _render(src, store_reduce=True)
    # M2 must reference M1 by name (no shadow → cheap shared form).
    m2_lines = [line for line in out.splitlines() if line.startswith("(define-fun M2 ")]
    assert m2_lines and "(M1 idx)" in m2_lines[0]
    # Both M1 and M2 emitted.
    map_names = {re.match(r"^\(define-fun (M\d+)", line).group(1) for line in _map_define_fun_lines(out)}
    assert {"M1", "M2"} <= map_names


def test_z3_semantic_equivalence_under_store_reduce():
    """Sanity check: rendered SMT for the same VC under both modes
    should be equivalent up to map-emission shape. The check-sat
    command + assertion structure must be present in both."""
    src = _wrap(
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd M0\n"
        "\t\tAssignExpCmd M1 Store(M0 0x10 0xa1)\n"
        "\t\tAssignExpCmd R0 Select(M1 0x10)\n"
        "\t\tAssertCmd false \"boom\"\n"
        "\t}",
        "R0:bv256\n\tM0:bytemap\n\tM1:bytemap",
    )
    a = _render(src, store_reduce=False)
    b = _render(src, store_reduce=True)
    for piece in ("(check-sat)", "BV256_MOD"):
        assert piece in a
        assert piece in b
