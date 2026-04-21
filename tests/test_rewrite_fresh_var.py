"""Tests for the fresh-var + entry-block insertion machinery."""

from __future__ import annotations

from ctac.ast.nodes import (
    ApplyExpr,
    AssignHavocCmd,
    AssumeExpCmd,
    ConstExpr,
    JumpCmd,
    SymbolRef,
    TacExpr,
)
from ctac.parse import parse_string, render_tac_file
from ctac.rewrite import rewrite_program
from ctac.rewrite.context import RewriteCtx
from ctac.rewrite.framework import Rule


def _single_block_tac() -> str:
    return """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tR0:bv256
\tR1:bv256
\tR2:bv256
}
Program {
\tBlock e Succ [] {
\t\tAssignHavocCmd R0
\t\tAssignHavocCmd R1
\t\tAssignExpCmd R2 IntMul(R0 R1)
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""


def _two_block_tac() -> str:
    """Program with an entry block (has a terminator) and a successor block."""
    return """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tR0:bv256
\tR1:bv256
\tR2:bv256
}
Program {
\tBlock entry Succ [next] {
\t\tAssignHavocCmd R0
\t\tJumpCmd next
\t}
\tBlock next Succ [] {
\t\tAssignHavocCmd R1
\t\tAssignExpCmd R2 IntMul(R0 R1)
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""


def _rule_once(fn) -> Rule:
    """Wrap a one-shot rule that fires at most once per program to avoid loops."""
    fired = {"n": 0}

    def wrap(expr: TacExpr, ctx: RewriteCtx) -> TacExpr | None:
        if fired["n"] >= 1:
            return None
        r = fn(expr, ctx)
        if r is not None:
            fired["n"] += 1
        return r

    return Rule(name="TEST", fn=wrap, description="test rule")


def test_emit_fresh_var_entry_placement_appends_before_terminator():
    """``placement='entry'`` puts havoc + assume at end of entry block, before its JumpCmd."""

    def test_rule(expr: TacExpr, ctx: RewriteCtx) -> TacExpr | None:
        if not (isinstance(expr, ApplyExpr) and expr.op == "IntMul"):
            return None
        return ctx.emit_fresh_var(
            prefix="t_test",
            placement="entry",
            assumes_fn=lambda t: [
                ApplyExpr("Ge", (t, ConstExpr("0x0(int)"))),
            ],
        )

    tac = parse_string(_two_block_tac(), path="<s>")
    res = rewrite_program(tac.program, (_rule_once(test_rule),))

    entry = res.program.blocks[0]
    assert isinstance(entry.commands[-1], JumpCmd)
    assert any(
        isinstance(c, AssignHavocCmd) and c.lhs.startswith("t_test")
        for c in entry.commands
    )
    assume_positions = [
        i for i, c in enumerate(entry.commands) if isinstance(c, AssumeExpCmd)
    ]
    havoc_positions = [
        i
        for i, c in enumerate(entry.commands)
        if isinstance(c, AssignHavocCmd) and c.lhs.startswith("t_test")
    ]
    assert havoc_positions and assume_positions
    assert max(havoc_positions) < min(assume_positions)
    assert max(assume_positions) < len(entry.commands) - 1


def test_emit_fresh_var_current_placement_inserts_before_current_cmd():
    """Default ``placement='current'`` inserts in the block where the rule fires,
    just before the triggering command."""

    def test_rule(expr: TacExpr, ctx: RewriteCtx) -> TacExpr | None:
        if not (isinstance(expr, ApplyExpr) and expr.op == "IntMul"):
            return None
        return ctx.emit_fresh_var(
            prefix="t_here",
            assumes_fn=lambda t: [ApplyExpr("Ge", (t, ConstExpr("0x0(int)")))],
        )

    tac = parse_string(_two_block_tac(), path="<s>")
    res = rewrite_program(tac.program, (_rule_once(test_rule),))

    # The IntMul is in block 'next', not entry. Insertion should be in 'next'.
    next_block = next(b for b in res.program.blocks if b.id == "next")
    havocs = [
        c
        for c in next_block.commands
        if isinstance(c, AssignHavocCmd) and c.lhs.startswith("t_here")
    ]
    assert len(havocs) == 1
    # Entry block is untouched.
    entry = res.program.blocks[0]
    assert not any(
        isinstance(c, AssignHavocCmd) and c.lhs.startswith("t_here")
        for c in entry.commands
    )


def test_emit_fresh_var_surfaces_extra_symbols():
    """Symbol-table entries surface on RewriteResult and render into .tac output."""

    def test_rule(expr: TacExpr, ctx: RewriteCtx) -> TacExpr | None:
        if not (isinstance(expr, ApplyExpr) and expr.op == "IntMul"):
            return None
        return ctx.emit_fresh_var(
            prefix="t_sym",
            assumes_fn=lambda t: [ApplyExpr("Ge", (t, ConstExpr("0x0(int)")))],
            sort="int",
        )

    tac = parse_string(_single_block_tac(), path="<s>")
    res = rewrite_program(tac.program, (_rule_once(test_rule),))

    assert len(res.extra_symbols) == 1
    name, sort = res.extra_symbols[0]
    assert name.startswith("t_sym")
    assert sort == "int"

    text = render_tac_file(tac, program=res.program, extra_symbols=res.extra_symbols)
    # The new name appears inside the symbol table block.
    assert f"{name}:int" in text
    # Rendered output still re-parses cleanly.
    reparsed = parse_string(text, path="<s2>")
    assert reparsed.program.blocks


def test_fresh_names_dont_collide_with_existing_symbols():
    """If a name like ``T0`` already exists, the generator skips past it.

    (Names follow the ``<prefix><N>`` convention — no separator — to match
    the existing ``R``/``I`` register style.)
    """
    tac_src = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tR0:bv256
\tT0:bv256
\tR2:bv256
}
Program {
\tBlock e Succ [] {
\t\tAssignHavocCmd R0
\t\tAssignHavocCmd T0
\t\tAssignExpCmd R2 IntMul(R0 T0)
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""

    def test_rule(expr: TacExpr, ctx: RewriteCtx) -> TacExpr | None:
        if not (isinstance(expr, ApplyExpr) and expr.op == "IntMul"):
            return None
        return ctx.emit_fresh_var(
            prefix="T",
            assumes_fn=lambda t: [],
        )

    tac = parse_string(tac_src, path="<s>")
    res = rewrite_program(tac.program, (_rule_once(test_rule),))
    names = {n for n, _ in res.extra_symbols}
    assert names
    assert "T0" not in names  # the existing one is preserved
    assert any(n.startswith("T") for n in names)


def test_is_entry_defined():
    """`is_entry_defined` distinguishes entry-defined from non-entry-defined symbols."""
    tac = parse_string(_two_block_tac(), path="<s>")
    ctx = RewriteCtx(tac.program)
    assert ctx.is_entry_defined("R0")  # havoc'd in entry
    assert not ctx.is_entry_defined("R1")  # havoc'd in 'next'
    assert not ctx.is_entry_defined("R2")  # assigned in 'next'


def test_default_fresh_name_prefix_is_T():
    """Fresh names default to ``T<N>`` — short, uppercase, no-separator register-style."""

    def test_rule(expr: TacExpr, ctx: RewriteCtx) -> TacExpr | None:
        if not (isinstance(expr, ApplyExpr) and expr.op == "IntMul"):
            return None
        # Call without explicit prefix — gets the default "T".
        return ctx.emit_fresh_var(
            assumes_fn=lambda t: [ApplyExpr("Ge", (t, ConstExpr("0x0(int)")))]
        )

    tac = parse_string(_single_block_tac(), path="<s>")
    res = rewrite_program(tac.program, (_rule_once(test_rule),))
    names = {n for n, _ in res.extra_symbols}
    assert any(n == "T0" for n in names), names


def test_reuse_name_does_not_add_new_symbol():
    """``emit_fresh_var(reuse_name=X)`` reuses an existing declared name — no new symbol entry."""

    def test_rule(expr: TacExpr, ctx: RewriteCtx) -> TacExpr | None:
        if not (isinstance(expr, ApplyExpr) and expr.op == "IntMul"):
            return None
        host = ctx.current_cmd()
        from ctac.ast.nodes import AssignExpCmd

        if not (ctx.at_cmd_top() and isinstance(host, AssignExpCmd)):
            return None
        result = ctx.emit_fresh_var(
            assumes_fn=lambda t: [ApplyExpr("Ge", (t, ConstExpr("0x0(int)")))],
            reuse_name=host.lhs,
        )
        ctx.skip_current_cmd()
        return result

    tac = parse_string(_single_block_tac(), path="<s>")
    res = rewrite_program(tac.program, (_rule_once(test_rule),))
    # No new symbol entries — R2's name was reused.
    assert res.extra_symbols == ()
    # R2 now has a havoc def (no longer an AssignExpCmd with IntMul RHS).
    entry = res.program.blocks[0]
    r2_havocs = [c for c in entry.commands if isinstance(c, AssignHavocCmd) and c.lhs == "R2"]
    assert len(r2_havocs) == 1


def test_fresh_counter_produces_distinct_names_within_iteration():
    """Multiple `emit_fresh_var` calls within one iteration return distinct names."""
    tac_src = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tR0:bv256
\tR1:bv256
\tR2:bv256
\tR3:bv256
}
Program {
\tBlock e Succ [] {
\t\tAssignHavocCmd R0
\t\tAssignHavocCmd R1
\t\tAssignExpCmd R2 IntMul(R0 R1)
\t\tAssignExpCmd R3 IntMul(R0 R1)
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""

    def test_rule(expr: TacExpr, ctx: RewriteCtx) -> TacExpr | None:
        if not (isinstance(expr, ApplyExpr) and expr.op == "IntMul"):
            return None
        return ctx.emit_fresh_var(
            prefix="T",
            assumes_fn=lambda t: [ApplyExpr("Ge", (t, ConstExpr("0x0(int)")))],
        )

    tac = parse_string(tac_src, path="<s>")
    res = rewrite_program(tac.program, (Rule(name="TEST", fn=test_rule),))
    names = [n for n, _ in res.extra_symbols]
    # Two IntMul sites -> two distinct fresh names; counter persists.
    assert len(names) == 2
    assert len(set(names)) == 2
    # Short, register-style names (`T0`, `T1`, ... — no separator).
    assert all(n.startswith("T") and n[1:].isdigit() for n in names)


def test_rewrite_output_reparses_with_extra_symbols():
    """The rewritten .tac with fresh symbols round-trips through the parser."""

    def test_rule(expr: TacExpr, ctx: RewriteCtx) -> TacExpr | None:
        if not (isinstance(expr, ApplyExpr) and expr.op == "IntMul"):
            return None
        return ctx.emit_fresh_var(
            prefix="t_rt",
            assumes_fn=lambda t: [
                ApplyExpr("Le", (ApplyExpr("IntMul", (SymbolRef("R0"), t)), SymbolRef("R1"))),
            ],
        )

    tac = parse_string(_single_block_tac(), path="<s>")
    res = rewrite_program(tac.program, (_rule_once(test_rule),))
    text = render_tac_file(tac, program=res.program, extra_symbols=res.extra_symbols)
    reparsed = parse_string(text, path="<s2>")
    # Entry block has the new havoc + assume.
    entry = reparsed.program.blocks[0]
    assert any(
        isinstance(c, AssignHavocCmd) and c.lhs.startswith("t_rt")
        for c in entry.commands
    )
