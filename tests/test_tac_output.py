"""Tests for ``ctac.tool.tac_output`` helpers — particularly the
``filter_live_extra_symbols`` pass that prunes orphan symbol-table
declarations before render."""

from __future__ import annotations

from ctac.parse import parse_string
from ctac.tool.tac_output import filter_live_extra_symbols


def _wrap(body: str, *, syms: str = "R0:bv256") -> str:
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
\tBlock e Succ [] {{
{body}
\t}}
}}
Axioms {{
}}
Metas {{
  "0": []
}}
"""


def test_filter_drops_unused_extra_symbols() -> None:
    """A program that doesn't reference ``T_dead`` anywhere should
    drop it from the extra-symbols list. ``T_used``, referenced as
    a SymbolRef in some RHS, is preserved."""
    tac = parse_string(
        _wrap(
            "\t\tAssignHavocCmd R0\n"
            "\t\tAssignHavocCmd T_used\n"
            "\t\tAssignExpCmd R0 IntAdd(T_used 0x1(int))",
            syms="R0:bv256\n\tT_used:bv256",
        ),
        path="<s>",
    )
    extra = (("T_used", "bv256"), ("T_dead", "bv256"))
    result = filter_live_extra_symbols(extra, tac.program)
    assert result == (("T_used", "bv256"),)


def test_filter_preserves_weak_use_via_annotation() -> None:
    """An annotation's weak ref counts as a use for symbol-table
    preservation. ``T_anno`` appears only inside an annotation's
    weak-refs payload — extract_def_use's weak-use detection picks
    it up, so the declaration must survive the filter even though
    no RHS reads it."""
    # Build an annotation that references T_anno in its weak refs.
    # AnnotationCmd's weak_refs are extracted from the JSON payload's
    # symbol-shaped fields; a Snippet with namePrefix is one example.
    anno = (
        'AnnotationCmd JSON{"key":{"name":"snippet.cmd","type":'
        '"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},'
        '"value":{"#class":"vc.data.SnippetCmd.CexPrintValue","sym":'
        '{"namePrefix":"T_anno","tag":{"#class":"tac.Tag.Bit256"},'
        '"callIndex":0},"label":"x"}}'
    )
    tac = parse_string(
        _wrap(
            "\t\tAssignHavocCmd R0\n"
            f"\t\t{anno}\n",
            syms="R0:bv256\n\tT_anno:bv256",
        ),
        path="<s>",
    )
    extra = (("T_anno", "bv256"), ("T_dead", "bv256"))
    result = filter_live_extra_symbols(extra, tac.program)
    # T_anno survives the filter (weak use), T_dead doesn't.
    names = {n for n, _ in result}
    assert "T_anno" in names, (
        "T_anno is referenced via annotation weak-refs; declaration "
        "should survive for traceability"
    )
    assert "T_dead" not in names


def test_filter_empty_input_is_empty() -> None:
    """Filter of empty extra-symbols is empty (fast path)."""
    tac = parse_string(_wrap("\t\tAssignHavocCmd R0"), path="<s>")
    assert filter_live_extra_symbols((), tac.program) == ()


def test_filter_preserves_def_only() -> None:
    """A symbol that's defined (e.g., ``AssignHavocCmd``) but has no
    other reference is still considered live — its def site is in
    the program. The declaration is kept."""
    tac = parse_string(
        _wrap(
            "\t\tAssignHavocCmd R0\n"
            "\t\tAssignHavocCmd T_def_only",
            syms="R0:bv256\n\tT_def_only:bv256",
        ),
        path="<s>",
    )
    extra = (("T_def_only", "bv256"),)
    result = filter_live_extra_symbols(extra, tac.program)
    assert result == (("T_def_only", "bv256"),)
