"""Unit tests for the chunk-pair coalescing pass."""

from __future__ import annotations

from ctac.ast.nodes import ApplyExpr, AssignExpCmd, ConstExpr, SymbolRef
from ctac.parse import parse_string
from ctac.rewrite.coalesce_chunk_pairs import coalesce_chunk_pairs

_TWO64 = "0x10000000000000000"
_U64MAX = "0xffffffffffffffff"
_U128MAX = "0xffffffffffffffffffffffffffffffff"


def _wrap(body: str, *, syms: str) -> str:
    return f"""TACSymbolTable {{
\tUserDefined {{
\t}}
\tBuiltinFunctions {{
\t\tsafe_math_narrow_bv256:JSON{{"#class":"vc.data.TACBuiltInFunction.SafeMathNarrow","returnSort":{{"#class":"tac.Tag.Bit256"}}}}
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


def _def_of(program, lhs):
    for block in program.blocks:
        for cmd in block.commands:
            if isinstance(cmd, AssignExpCmd) and cmd.lhs == lhs:
                return cmd.rhs
    raise AssertionError(f"no def of {lhs!r}")


_PAIR_PRELUDE = (
    "\t\tAssignHavocCmd V\n"
    f"\t\tAssumeExpCmd Le(V {_U128MAX})\n"
    "\t\tAssignHavocCmd W\n"
    f"\t\tAssumeExpCmd Le(W {_U128MAX})\n"
    "\t\tAssignHavocCmd B\n"
    "\t\tAssignHavocCmd C\n"
    f"\t\tAssumeExpCmd Le(C {_U64MAX})\n"
    f"\t\tAssignExpCmd VL Mod(V {_TWO64})\n"
    f"\t\tAssignExpCmd VH Div(V {_TWO64})\n"
    f"\t\tAssignExpCmd WL Mod(W {_TWO64})\n"
    f"\t\tAssignExpCmd WH Div(W {_TWO64})\n"
)

_PAIR_SYMS = (
    "V:bv256\n\tW:bv256\n\tB:bool\n\tC:bv256\n\tVL:bv256\n\tVH:bv256"
    "\n\tWL:bv256\n\tWH:bv256\n\tSL:bv256\n\tSH:bv256\n\tT2:bool"
)


def test_coalesce_parallel_select_extraction_feeds():
    """Two extraction pairs selected in parallel: the pair re-anchors
    as chunks of H = Ite(B, V, W)."""
    body = (
        "\tBlock e Succ [] {\n"
        + _PAIR_PRELUDE
        + "\t\tAssignExpCmd SL Ite(B VL WL)\n"
        + "\t\tAssignExpCmd SH Ite(B VH WH)\n"
        + "\t\tAssignExpCmd T2 LAnd(Eq(SH 0x0) Lt(SL C))\n"
        + "\t\tAssumeExpCmd T2\n"
        + "\t\tAssertCmd false\n"
        + "\t}"
    )
    tac = parse_string(_wrap(body, syms=_PAIR_SYMS), path="<s>")
    res = coalesce_chunk_pairs(tac.program, symbol_sorts=tac.symbol_sorts)
    assert res.hits == 1
    assert ("H0", "bv256") in res.fresh_symbols
    assert _def_of(res.program, "H0") == ApplyExpr(
        "Ite", (SymbolRef("B"), SymbolRef("V"), SymbolRef("W"))
    )
    assert _def_of(res.program, "SL") == ApplyExpr(
        "Mod", (SymbolRef("H0"), ConstExpr(_TWO64))
    )
    assert _def_of(res.program, "SH") == ApplyExpr(
        "Div", (SymbolRef("H0"), ConstExpr(_TWO64))
    )


def test_coalesce_cascaded_min_with_widen_feed():
    """The lopu min idiom: a second select pair feeding off the first
    pair and a (C, 0) widen feed. Cascades across fixpoint rounds."""
    body = (
        "\tBlock e Succ [] {\n"
        + _PAIR_PRELUDE
        + "\t\tAssignHavocCmd B2\n"
        + "\t\tAssignExpCmd SL Ite(B VL WL)\n"
        + "\t\tAssignExpCmd SH Ite(B VH WH)\n"
        + "\t\tAssignExpCmd ML Ite(B2 SL C)\n"
        + "\t\tAssignExpCmd MH Ite(B2 SH 0x0)\n"
        + "\t\tAssumeExpCmd Lt(ML MH)\n"
        + "\t\tAssertCmd false\n"
        + "\t}"
    )
    tac = parse_string(
        _wrap(body, syms=_PAIR_SYMS + "\n\tB2:bool\n\tML:bv256\n\tMH:bv256"),
        path="<s>",
    )
    res = coalesce_chunk_pairs(tac.program, symbol_sorts=tac.symbol_sorts)
    assert res.hits == 2
    assert _def_of(res.program, "ML") == ApplyExpr(
        "Mod", (SymbolRef("H1"), ConstExpr(_TWO64))
    )
    assert _def_of(res.program, "H1") == ApplyExpr(
        "Ite", (SymbolRef("B2"), SymbolRef("H0"), SymbolRef("C"))
    )


def test_coalesce_const_pair_feed():
    """A (c_lo, c_hi) const feed becomes the combined wide literal."""
    body = (
        "\tBlock e Succ [] {\n"
        + _PAIR_PRELUDE
        + "\t\tAssignExpCmd SL Ite(B VL 0x5)\n"
        + "\t\tAssignExpCmd SH Ite(B VH 0x2)\n"
        + "\t\tAssumeExpCmd Lt(SL SH)\n"
        + "\t\tAssertCmd false\n"
        + "\t}"
    )
    tac = parse_string(_wrap(body, syms=_PAIR_SYMS), path="<s>")
    res = coalesce_chunk_pairs(tac.program, symbol_sorts=tac.symbol_sorts)
    assert res.hits == 1
    assert _def_of(res.program, "H0") == ApplyExpr(
        "Ite",
        (
            SymbolRef("B"),
            SymbolRef("V"),
            ConstExpr(hex(2 * (1 << 64) + 5)),
        ),
    )


def test_coalesce_dynamic_pair_defs_h_in_static_prefix():
    """Pair slots that are DSA-dynamic (defs in two blocks): the
    Ite-RHS branch is rewritten in place and H lands in the static
    prefix, before the first dynamic command."""
    body = (
        "\tBlock e Succ [t, f] {\n"
        + _PAIR_PRELUDE
        + "\t\tJumpiCmd t f B\n"
        + "\t}\n"
        + "\tBlock t Succ [j] {\n"
        + "\t\tAssignHavocCmd B2\n"
        + "\t\tAssignExpCmd SL Ite(B2 VL WL)\n"
        + "\t\tAssignExpCmd SH Ite(B2 VH WH)\n"
        + "\t\tJumpCmd j\n"
        + "\t}\n"
        + "\tBlock f Succ [j] {\n"
        + "\t\tAssignExpCmd SL 0x0\n"
        + "\t\tAssignExpCmd SH 0x0\n"
        + "\t\tJumpCmd j\n"
        + "\t}\n"
        + "\tBlock j Succ [] {\n"
        + "\t\tAssertCmd Lt(SL SH)\n"
        + "\t}"
    )
    tac = parse_string(
        _wrap(body, syms=_PAIR_SYMS + "\n\tB2:bool"), path="<s>"
    )
    res = coalesce_chunk_pairs(tac.program, symbol_sorts=tac.symbol_sorts)
    assert res.hits == 1
    blocks = {b.id: b for b in res.program.blocks}
    t_cmds = blocks["t"].commands
    # H def must precede the first dynamic (SL's def).
    h_idx = next(
        i for i, c in enumerate(t_cmds)
        if isinstance(c, AssignExpCmd) and c.lhs == "H0"
    )
    sl_idx = next(
        i for i, c in enumerate(t_cmds)
        if isinstance(c, AssignExpCmd) and c.lhs == "SL"
    )
    assert h_idx < sl_idx
    assert _def_of(res.program, "H0") == ApplyExpr(
        "Ite", (SymbolRef("B2"), SymbolRef("V"), SymbolRef("W"))
    )
    # The f-branch const defs are untouched (no Ite — increment 1.5).
    f_defs = [
        c.rhs for c in blocks["f"].commands if isinstance(c, AssignExpCmd)
    ]
    assert ConstExpr("0x0") in f_defs


def test_coalesce_mismatched_conds_no_fire():
    body = (
        "\tBlock e Succ [] {\n"
        + _PAIR_PRELUDE
        + "\t\tAssignHavocCmd B2\n"
        + "\t\tAssignExpCmd SL Ite(B VL WL)\n"
        + "\t\tAssignExpCmd SH Ite(B2 VH WH)\n"
        + "\t\tAssumeExpCmd Lt(SL SH)\n"
        + "\t\tAssertCmd false\n"
        + "\t}"
    )
    tac = parse_string(
        _wrap(body, syms=_PAIR_SYMS + "\n\tB2:bool"), path="<s>"
    )
    res = coalesce_chunk_pairs(tac.program, symbol_sorts=tac.symbol_sorts)
    assert res.hits == 0


def test_coalesce_unbounded_widen_no_fire():
    """(sym, 0) widen feed without a u64 bound on sym: no fire
    (the chunk relation Mod(H, 2^64) == sym would not hold)."""
    body = (
        "\tBlock e Succ [] {\n"
        + _PAIR_PRELUDE
        + "\t\tAssignHavocCmd U\n"
        + "\t\tAssignExpCmd SL Ite(B VL U)\n"
        + "\t\tAssignExpCmd SH Ite(B VH 0x0)\n"
        + "\t\tAssumeExpCmd Lt(SL SH)\n"
        + "\t\tAssertCmd false\n"
        + "\t}"
    )
    tac = parse_string(
        _wrap(body, syms=_PAIR_SYMS + "\n\tU:bv256"), path="<s>"
    )
    res = coalesce_chunk_pairs(tac.program, symbol_sorts=tac.symbol_sorts)
    assert res.hits == 0


def test_recomb_witness_dynamic_slot():
    """A post-join recombination over a dynamic pair seeds a slot:
    per-branch H defs (chunk-pair branch resolves to the extraction
    source; const branch folds) and the consumer rewrites to H."""
    body = (
        "\tBlock e Succ [t, f] {\n"
        "\t\tAssignHavocCmd V\n"
        f"\t\tAssumeExpCmd Le(V {_U128MAX})\n"
        "\t\tAssignHavocCmd B\n"
        f"\t\tAssignExpCmd VL Mod(V {_TWO64})\n"
        f"\t\tAssignExpCmd VH Div(V {_TWO64})\n"
        "\t\tJumpiCmd t f B\n"
        "\t}\n"
        "\tBlock t Succ [j] {\n"
        "\t\tAssignExpCmd PL VL\n"
        "\t\tAssignExpCmd PH VH\n"
        "\t\tJumpCmd j\n"
        "\t}\n"
        "\tBlock f Succ [j] {\n"
        "\t\tAssignExpCmd PL 0x5\n"
        "\t\tAssignExpCmd PH 0x2\n"
        "\t\tJumpCmd j\n"
        "\t}\n"
        "\tBlock j Succ [] {\n"
        "\t\tAssignExpCmd R Add(ShiftLeft(PH 0x40) PL)\n"
        "\t\tAssertCmd Lt(R V)\n"
        "\t}"
    )
    syms = "V:bv256\n\tB:bool\n\tVL:bv256\n\tVH:bv256\n\tPL:bv256\n\tPH:bv256\n\tR:bv256"
    tac = parse_string(_wrap(body, syms=syms), path="<s>")
    res = coalesce_chunk_pairs(tac.program, symbol_sorts=tac.symbol_sorts)
    assert res.hits == 1
    assert _def_of(res.program, "R") == SymbolRef("H0")
    blocks = {b.id: b for b in res.program.blocks}
    t_defs = {
        c.lhs: c.rhs for c in blocks["t"].commands
        if isinstance(c, AssignExpCmd)
    }
    f_defs = {
        c.lhs: c.rhs for c in blocks["f"].commands
        if isinstance(c, AssignExpCmd)
    }
    assert t_defs["H0"] == SymbolRef("V")
    assert f_defs["H0"] == ConstExpr(hex((2 << 64) + 5))


def test_recomb_witness_inline_arm_hoist():
    """A branch whose pair defs carry inline exprs: the arms hoist as
    static defs and the branch value is their definitional recomb."""
    body = (
        "\tBlock e Succ [t, f] {\n"
        "\t\tAssignHavocCmd A\n"
        f"\t\tAssumeExpCmd Le(A {_U64MAX})\n"
        "\t\tAssignHavocCmd B\n"
        "\t\tJumpiCmd t f B\n"
        "\t}\n"
        "\tBlock t Succ [j] {\n"
        "\t\tAssignExpCmd PL IntAdd(A 0x1(int))\n"
        "\t\tAssignExpCmd PH 0x0\n"
        "\t\tJumpCmd j\n"
        "\t}\n"
        "\tBlock f Succ [j] {\n"
        "\t\tAssignExpCmd PL 0x0\n"
        "\t\tAssignExpCmd PH 0x0\n"
        "\t\tJumpCmd j\n"
        "\t}\n"
        "\tBlock j Succ [] {\n"
        "\t\tAssignExpCmd R Add(ShiftLeft(PH 0x40) PL)\n"
        "\t\tAssertCmd Lt(R A)\n"
        "\t}"
    )
    syms = "A:bv256\n\tB:bool\n\tPL:bv256\n\tPH:bv256\n\tR:bv256"
    tac = parse_string(_wrap(body, syms=syms), path="<s>")
    res = coalesce_chunk_pairs(tac.program, symbol_sorts=tac.symbol_sorts)
    assert res.hits == 1
    assert _def_of(res.program, "R") == SymbolRef("H2")
    blocks = {b.id: b for b in res.program.blocks}
    t_lhs = [c.lhs for c in blocks["t"].commands if isinstance(c, AssignExpCmd)]
    # Hoisted arm + definitional recomb precede the dynamic pair defs.
    assert t_lhs.index("H1") < t_lhs.index("PL")
    assert t_lhs.index("H0") < t_lhs.index("H1")


def test_recomb_witness_same_block_dynamic_ref_abstains():
    """A branch RHS referencing a dynamic redefined in the same block
    cannot be hoisted (the value would change) — slot abstains."""
    body = (
        "\tBlock e Succ [t, f] {\n"
        "\t\tAssignHavocCmd A\n"
        "\t\tAssignHavocCmd B\n"
        "\t\tJumpiCmd t f B\n"
        "\t}\n"
        "\tBlock t Succ [j] {\n"
        "\t\tAssignExpCmd Q A\n"
        "\t\tAssignExpCmd PL Q\n"
        "\t\tAssignExpCmd PH 0x0\n"
        "\t\tJumpCmd j\n"
        "\t}\n"
        "\tBlock f Succ [j] {\n"
        "\t\tAssignExpCmd Q 0x1\n"
        "\t\tAssignExpCmd PL IntAdd(Q 0x1(int))\n"
        "\t\tAssignExpCmd PH 0x0\n"
        "\t\tJumpCmd j\n"
        "\t}\n"
        "\tBlock j Succ [] {\n"
        "\t\tAssignExpCmd R Add(ShiftLeft(PH 0x40) PL)\n"
        "\t\tAssertCmd Lt(R A)\n"
        "\t}"
    )
    syms = "A:bv256\n\tB:bool\n\tQ:bv256\n\tPL:bv256\n\tPH:bv256\n\tR:bv256"
    tac = parse_string(_wrap(body, syms=syms), path="<s>")
    res = coalesce_chunk_pairs(tac.program, symbol_sorts=tac.symbol_sorts)
    assert res.hits == 0
