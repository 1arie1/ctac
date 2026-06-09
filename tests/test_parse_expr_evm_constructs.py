"""EVM-side TAC constructs in the expression parser / use extraction.

Both regressions come from the metamorpho (Solidity-target) dump in
the benchmark suite: `AnnotationExp(e, JSON{...})` ghost-read wrappers
and unregistered `:bif` function heads (`to_skey:bif`) surfaced as
phantom undefined symbols in use-before-def.
"""

from __future__ import annotations

from ctac.analysis.expr_walk import iter_expr_symbols
from ctac.ast.nodes import ApplyExpr, ConstExpr, SymbolRef
from ctac.ast.parse_expr import parse_expr
from ctac.rewrite.unparse import unparse_expr


def test_json_payload_parses_as_const_literal():
    src = 'AnnotationExp(Eq(CANON1!!44:76 0x33b2e3c9fd0803ce8000000 ) JSON{"key":{"name":"snippet.cmd"}})'
    e = parse_expr(src)
    assert isinstance(e, ApplyExpr) and e.op == "AnnotationExp"
    eq, payload = e.args
    assert isinstance(eq, ApplyExpr) and eq.op == "Eq"
    assert isinstance(payload, ConstExpr)
    assert payload.value.startswith("JSON{")
    # The payload is not a dataflow use; only the wrapped expression's
    # symbol surfaces.
    assert list(iter_expr_symbols(e)) == ["CANON1!!44"]


def test_json_payload_round_trips_verbatim():
    payload = 'JSON{"key":{"name":"snippet.cmd"}}'
    assert unparse_expr(parse_expr(payload)) == payload


def test_json_payload_with_spaces_stays_atomic():
    # The payload's `value` field carries free text with spaces (and
    # balanced/embedded parens). The arg splitter must not shred it: the
    # AnnotationExp keeps exactly two args (wrapped expr + JSON literal),
    # and none of the value's words leak out as phantom symbols.
    src = (
        'AnnotationExp(Add(r1 0xffffffffffffffe0) '
        'JSON{"key":{"name":"sbf.tac.cannot.overflow"},'
        '"value":"pointer addition at 896_120-5: r1:sp(4064) = +  -32"})'
    )
    e = parse_expr(src)
    assert isinstance(e, ApplyExpr) and e.op == "AnnotationExp"
    assert len(e.args) == 2
    add, payload = e.args
    assert isinstance(add, ApplyExpr) and add.op == "Add"
    assert isinstance(payload, ConstExpr) and payload.value.startswith("JSON{")
    assert list(iter_expr_symbols(e)) == ["r1"]
    assert unparse_expr(e) == src


def test_unknown_bif_head_not_a_dataflow_use():
    # `to_skey:bif` is not in ctac's builtin registry, but the `:bif`
    # suffix marks it as a function symbol by the dump format itself.
    e = ApplyExpr(
        "Select",
        (
            SymbolRef("tacExtcodesize!!53:82"),
            ApplyExpr("Apply", (SymbolRef("to_skey:bif"), SymbolRef("R3:112"))),
        ),
    )
    assert list(iter_expr_symbols(e)) == ["tacExtcodesize!!53", "R3"]
