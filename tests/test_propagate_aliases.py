"""Unit tests for ``ctac.rewrite.propagate_aliases``."""

from __future__ import annotations

import json

from ctac.parse import parse_string
from ctac.rewrite.propagate_aliases import (
    _build_alias_map,
    _resolve,
    _substitute_in_payload,
    propagate_aliases_into_annotations,
)


def _wrap(body: str, *, syms: str = "R0:bv256\n\tR1:bv256\n\tR2:bv256") -> str:
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


def _snippet_payload(symbol: str, message: str = "label") -> str:
    obj = {
        "key": {
            "name": "snippet.cmd",
            "type": "vc.data.SnippetCmd",
            "erasureStrategy": "CallTrace",
        },
        "value": {
            "#class": "vc.data.SnippetCmd.CvlrSnippetCmd.CexPrintValues",
            "displayMessage": message,
            "symbols": [
                {
                    "namePrefix": symbol,
                    "tag": {"#class": "tac.Tag.Bit256"},
                    "callIndex": 0,
                }
            ],
        },
    }
    return "JSON" + json.dumps(obj, separators=(",", ":"))


def test_build_alias_map_picks_up_symbolref_rhs():
    """``X = SymbolRef(Y)`` enters the alias map; non-SymRef RHSes don't."""
    body = (
        "\t\tAssignHavocCmd R0\n"
        "\t\tAssignExpCmd R1 R0\n"
        "\t\tAssignExpCmd R2 Add(R0 R1)"
    )
    tac = parse_string(_wrap(body), path="<s>")
    alias = _build_alias_map(tac.program)
    assert alias == {"R1": "R0"}


def test_resolve_walks_alias_chain():
    """X -> Y -> Z resolves to Z."""
    alias = {"X": "Y", "Y": "Z"}
    assert _resolve("X", alias) == "Z"
    assert _resolve("Y", alias) == "Z"
    assert _resolve("Z", alias) == "Z"
    assert _resolve("W", alias) == "W"


def test_resolve_breaks_on_cycle():
    """A self- or mutual-alias cycle aborts cleanly (defensive)."""
    alias = {"X": "Y", "Y": "X"}
    # Doesn't matter which side we land on; just must not loop.
    result = _resolve("X", alias)
    assert result in {"X", "Y"}


def test_substitute_in_payload_replaces_symbol_position_string():
    payload = _snippet_payload("R83", message="total_for_user")
    new_payload, n = _substitute_in_payload(payload, {"R83": "R82"})
    assert n == 1
    assert '"namePrefix":"R82"' in new_payload
    assert '"R83"' not in new_payload
    # Display message untouched.
    assert "total_for_user" in new_payload


def test_substitute_in_payload_skips_display_keys():
    """``displayMessage`` is in the skip set: a display string that
    happens to match a symbol name must not be rewritten."""
    # Pathological: display string literally is "R83".
    obj = {
        "key": {"name": "snippet.cmd", "type": "t", "erasureStrategy": "X"},
        "value": {
            "#class": "C",
            "displayMessage": "R83",
            "symbols": [
                {"namePrefix": "R83", "tag": {"#class": "T"}, "callIndex": 0}
            ],
        },
    }
    payload = "JSON" + json.dumps(obj, separators=(",", ":"))
    new_payload, _ = _substitute_in_payload(payload, {"R83": "R82"})
    # symbols[0].namePrefix was substituted; displayMessage was NOT.
    assert '"displayMessage":"R83"' in new_payload
    assert '"namePrefix":"R82"' in new_payload


def test_substitute_in_payload_non_json_unchanged():
    payload = "freeform annotation, no JSON shape"
    new_payload, n = _substitute_in_payload(payload, {"R83": "R82"})
    assert new_payload == payload
    assert n == 0


def test_propagate_aliases_into_annotations_end_to_end():
    """An alias ``R1 = R0`` propagates into the cex-print payload's
    namePrefix and into the AnnotationCmd's weak_refs tuple."""
    payload = _snippet_payload("R1")
    body = (
        "\t\tAssignHavocCmd R0\n"
        "\t\tAssignExpCmd R1 R0\n"
        f"\t\tAnnotationCmd {payload}"
    )
    tac = parse_string(_wrap(body), path="<s>")
    new_program, hits = propagate_aliases_into_annotations(tac.program)
    assert hits == 1
    # Find the AnnotationCmd in the new program and check the substitution.
    from ctac.ast.nodes import AnnotationCmd

    annotated = [
        cmd
        for block in new_program.blocks
        for cmd in block.commands
        if isinstance(cmd, AnnotationCmd)
    ]
    assert len(annotated) == 1
    new_cmd = annotated[0]
    assert '"namePrefix":"R0"' in new_cmd.payload
    assert '"R1"' not in new_cmd.payload
    assert all(ref.name == "R0" for ref in new_cmd.weak_refs)
    # ``raw`` must be re-rendered so render_program emits the new payload.
    assert '"namePrefix":"R0"' in new_cmd.raw


def test_propagate_aliases_no_op_when_no_aliases():
    body = (
        "\t\tAssignHavocCmd R0\n"
        f"\t\tAnnotationCmd {_snippet_payload('R0')}"
    )
    tac = parse_string(_wrap(body), path="<s>")
    new_program, hits = propagate_aliases_into_annotations(tac.program)
    assert hits == 0
    assert new_program is tac.program  # identity preserved


def test_propagate_aliases_chains_transitively():
    """``R1 = R0; R2 = R1`` collapses to R0 in the annotation."""
    payload = _snippet_payload("R2")
    body = (
        "\t\tAssignHavocCmd R0\n"
        "\t\tAssignExpCmd R1 R0\n"
        "\t\tAssignExpCmd R2 R1\n"
        f"\t\tAnnotationCmd {payload}"
    )
    tac = parse_string(_wrap(body), path="<s>")
    new_program, _ = propagate_aliases_into_annotations(tac.program)
    from ctac.ast.nodes import AnnotationCmd

    annotated = [
        cmd
        for block in new_program.blocks
        for cmd in block.commands
        if isinstance(cmd, AnnotationCmd)
    ]
    assert len(annotated) == 1
    assert '"namePrefix":"R0"' in annotated[0].payload
