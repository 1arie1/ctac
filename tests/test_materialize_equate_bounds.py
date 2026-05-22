"""Unit tests for ``ctac.rewrite.materialize_equate_bounds``."""

from __future__ import annotations

from ctac.ast.nodes import ApplyExpr, AssumeExpCmd, ConstExpr, SymbolRef
from ctac.parse import parse_string
from ctac.rewrite.materialize_equate_bounds import (
    materialize_havoc_equate_bounds,
)


def _wrap(body: str, *, syms: str) -> str:
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


def _assumes(prog):
    return [
        cmd
        for block in prog.blocks
        for cmd in block.commands
        if isinstance(cmd, AssumeExpCmd)
    ]


def test_materialize_bound_after_equality():
    """The canonical SBF nondet pattern: havoc R, bound R, define X
    later, equate, then bound on X must appear right after the equality."""
    body = (
        "\t\tAssignHavocCmd R\n"
        "\t\tAssumeExpCmd Le(R 0x3ffffffffffff)\n"
        "\t\tAssignHavocCmd Z\n"
        "\t\tAssignExpCmd X Div(Z 0x4000)\n"
        "\t\tAssumeExpCmd Eq(R X)\n"
    )
    tac = parse_string(_wrap(body, syms="R:bv256\n\tZ:bv256\n\tX:bv256"), path="<s>")
    res = materialize_havoc_equate_bounds(tac.program, symbol_sorts=tac.symbol_sorts)
    assert res.hits == 1
    assumes = _assumes(res.program)
    # Expect three assumes now: original bound on R, original equality,
    # materialized bound on X (in that source order).
    assert len(assumes) == 3
    assert assumes[2].condition == ApplyExpr(
        "Le", (SymbolRef("X"), ConstExpr("0x3ffffffffffff"))
    )


def test_eq_orientation_x_first():
    """Eq(X, R) — same pattern, args swapped."""
    body = (
        "\t\tAssignHavocCmd R\n"
        "\t\tAssumeExpCmd Le(R 0xff)\n"
        "\t\tAssignHavocCmd Z\n"
        "\t\tAssignExpCmd X Div(Z 0x4000)\n"
        "\t\tAssumeExpCmd Eq(X R)\n"
    )
    tac = parse_string(_wrap(body, syms="R:bv256\n\tZ:bv256\n\tX:bv256"), path="<s>")
    res = materialize_havoc_equate_bounds(tac.program, symbol_sorts=tac.symbol_sorts)
    assert res.hits == 1
    assumes = _assumes(res.program)
    assert assumes[2].condition == ApplyExpr(
        "Le", (SymbolRef("X"), ConstExpr("0xff"))
    )


def test_no_havoc_no_fire():
    """If R isn't havoc-defined, nothing to materialize from."""
    body = (
        "\t\tAssignHavocCmd Z\n"
        "\t\tAssignExpCmd R Div(Z 0x100)\n"
        "\t\tAssumeExpCmd Le(R 0xff)\n"
        "\t\tAssignHavocCmd W\n"
        "\t\tAssignExpCmd X Div(W 0x100)\n"
        "\t\tAssumeExpCmd Eq(R X)\n"
    )
    tac = parse_string(
        _wrap(body, syms="R:bv256\n\tZ:bv256\n\tX:bv256\n\tW:bv256"),
        path="<s>",
    )
    res = materialize_havoc_equate_bounds(tac.program, symbol_sorts=tac.symbol_sorts)
    assert res.hits == 0
    # Both sides non-havoc: skipped.


def test_no_constraint_no_fire():
    """If R has no constraint assume (just the equality), there's
    nothing to materialize."""
    body = (
        "\t\tAssignHavocCmd R\n"
        "\t\tAssignHavocCmd Z\n"
        "\t\tAssignExpCmd X Div(Z 0x4000)\n"
        "\t\tAssumeExpCmd Eq(R X)\n"
    )
    tac = parse_string(_wrap(body, syms="R:bv256\n\tZ:bv256\n\tX:bv256"), path="<s>")
    res = materialize_havoc_equate_bounds(tac.program, symbol_sorts=tac.symbol_sorts)
    assert res.hits == 0


def test_idempotent_on_existing_materialization():
    """Running the pass twice does not duplicate the materialized assume."""
    body = (
        "\t\tAssignHavocCmd R\n"
        "\t\tAssumeExpCmd Le(R 0xff)\n"
        "\t\tAssignHavocCmd Z\n"
        "\t\tAssignExpCmd X Div(Z 0x4000)\n"
        "\t\tAssumeExpCmd Eq(R X)\n"
    )
    tac = parse_string(_wrap(body, syms="R:bv256\n\tZ:bv256\n\tX:bv256"), path="<s>")
    once = materialize_havoc_equate_bounds(
        tac.program, symbol_sorts=tac.symbol_sorts
    )
    twice = materialize_havoc_equate_bounds(
        once.program, symbol_sorts=tac.symbol_sorts
    )
    assert twice.hits == 0
    assert len(_assumes(twice.program)) == len(_assumes(once.program))


def test_multiple_constraints_each_materialized():
    """Two bound assumes on R: both get materialized onto X."""
    body = (
        "\t\tAssignHavocCmd R\n"
        "\t\tAssumeExpCmd Le(R 0xff)\n"
        "\t\tAssumeExpCmd Ge(R 0x10)\n"
        "\t\tAssignHavocCmd Z\n"
        "\t\tAssignExpCmd X Div(Z 0x4000)\n"
        "\t\tAssumeExpCmd Eq(R X)\n"
    )
    tac = parse_string(_wrap(body, syms="R:bv256\n\tZ:bv256\n\tX:bv256"), path="<s>")
    res = materialize_havoc_equate_bounds(tac.program, symbol_sorts=tac.symbol_sorts)
    assert res.hits == 2
    assumes = _assumes(res.program)
    # Original 3 + 2 materialized.
    assert len(assumes) == 5
    conditions = {tuple(_canon(a.condition)) for a in assumes}
    assert ("Le", "X", "0xff") in conditions
    assert ("Ge", "X", "0x10") in conditions


def test_sort_mismatch_skipped():
    """R bv256 vs X bool: type mismatch is a hard skip."""
    body = (
        "\t\tAssignHavocCmd R\n"
        "\t\tAssumeExpCmd Le(R 0xff)\n"
        "\t\tAssignHavocCmd X\n"
        "\t\tAssumeExpCmd Eq(R X)\n"
    )
    tac = parse_string(_wrap(body, syms="R:bv256\n\tX:bool"), path="<s>")
    res = materialize_havoc_equate_bounds(tac.program, symbol_sorts=tac.symbol_sorts)
    assert res.hits == 0


def _canon(cond):
    """Flatten ``Op(SymRef(name), Const(value))`` to a tuple for set membership."""
    if isinstance(cond, ApplyExpr) and len(cond.args) == 2:
        a, b = cond.args
        if isinstance(a, SymbolRef) and isinstance(b, ConstExpr):
            return (cond.op, a.name, b.value)
    return (None,)
