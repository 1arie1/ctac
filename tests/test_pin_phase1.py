"""Tests for ctac.transform.pin Phase 1 (static analysis).

Tests both the static_eval_bool primitive and the compute_dead_blocks
graph-level fixpoint, using small synthetic TAC programs.
"""

from __future__ import annotations

from ctac.ast.nodes import ApplyExpr, ConstExpr, SymbolRef
from ctac.parse import parse_string
from ctac.transform.pin import (
    compute_dead_blocks,
    static_eval_bool,
    validate_plan_against,
)


T = ConstExpr("true")
F = ConstExpr("false")


# ----------------------------------------------------- static_eval_bool


def test_static_eval_const_true_false():
    assert static_eval_bool(T, {}) is True
    assert static_eval_bool(F, {}) is False


def test_static_eval_non_bool_const_unknown():
    assert static_eval_bool(ConstExpr("0"), {}) is None


def test_static_eval_symbol_via_subs():
    assert static_eval_bool(SymbolRef("X"), {"X": T}) is True
    assert static_eval_bool(SymbolRef("X"), {"X": F}) is False


def test_static_eval_symbol_unknown_when_no_sub_no_def():
    assert static_eval_bool(SymbolRef("X"), {}) is None


def test_static_eval_symbol_via_def():
    defs = {"X": T}
    assert static_eval_bool(SymbolRef("X"), {}, defs) is True


def test_static_eval_symbol_subs_overrides_def():
    defs = {"X": T}
    assert static_eval_bool(SymbolRef("X"), {"X": F}, defs) is False


def test_static_eval_lnot():
    assert static_eval_bool(ApplyExpr("LNot", (T,)), {}) is False
    assert static_eval_bool(ApplyExpr("LNot", (F,)), {}) is True
    assert static_eval_bool(
        ApplyExpr("LNot", (SymbolRef("X"),)), {}
    ) is None


def test_static_eval_land_three_valued():
    # Concrete False short-circuits even with unknown other operands
    assert static_eval_bool(
        ApplyExpr("LAnd", (F, SymbolRef("X"))), {}
    ) is False
    # All concrete true -> True
    assert static_eval_bool(ApplyExpr("LAnd", (T, T)), {}) is True
    # Mix of true + unknown -> None
    assert static_eval_bool(
        ApplyExpr("LAnd", (T, SymbolRef("X"))), {}
    ) is None


def test_static_eval_lor_three_valued():
    # Concrete True short-circuits even with unknown other operands
    assert static_eval_bool(
        ApplyExpr("LOr", (T, SymbolRef("X"))), {}
    ) is True
    # All concrete false -> False
    assert static_eval_bool(ApplyExpr("LOr", (F, F)), {}) is False
    # Mix of false + unknown -> None
    assert static_eval_bool(
        ApplyExpr("LOr", (F, SymbolRef("X"))), {}
    ) is None


def test_static_eval_eq_bools():
    assert static_eval_bool(ApplyExpr("Eq", (T, T)), {}) is True
    assert static_eval_bool(ApplyExpr("Eq", (T, F)), {}) is False
    assert static_eval_bool(
        ApplyExpr("Eq", (T, SymbolRef("X"))), {}
    ) is None


def test_static_eval_ite():
    assert static_eval_bool(ApplyExpr("Ite", (T, T, F)), {}) is True
    assert static_eval_bool(ApplyExpr("Ite", (F, T, F)), {}) is False
    # Unknown guard
    assert static_eval_bool(
        ApplyExpr("Ite", (SymbolRef("X"), T, F)), {}
    ) is None


def test_static_eval_compound_demorgan():
    # LNot(LAnd(true, X)) with X=false -> LNot(LAnd(true,false)) -> LNot(false) -> true
    expr = ApplyExpr(
        "LNot",
        (ApplyExpr("LAnd", (T, SymbolRef("X"))),),
    )
    assert static_eval_bool(expr, {"X": F}) is True


def test_static_eval_cycle_in_defs():
    """X depends on Y, Y on X; should bail to None (no infinite loop)."""
    defs = {"X": SymbolRef("Y"), "Y": SymbolRef("X")}
    assert static_eval_bool(SymbolRef("X"), {}, defs) is None


# -------------------------------------------------- compute_dead_blocks
# Build small synthetic programs and check the dead set.


def _wrap(blocks_text: str, *, syms: str = "B0:bool") -> str:
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
{blocks_text}
}}
Axioms {{
}}
Metas {{
  "0": []
}}
"""


def test_compute_dead_blocks_no_drops_returns_empty():
    """A trivially live program with no drops returns no dead blocks."""
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [exit] {\n"
            "\t\tJumpCmd exit\n"
            "\t}\n"
            "\tBlock exit Succ [] {\n"
            "\t\tNoSuchCmd\n"
            "\t}\n"
        ),
        path="<s>",
    )
    res = compute_dead_blocks(tac.program, [], {})
    assert res.dead == frozenset()


def test_compute_dead_blocks_user_drop_simple():
    """e -> a -> exit; drop a -> a is dropped, exit becomes orphan."""
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [a] {\n"
            "\t\tJumpCmd a\n"
            "\t}\n"
            "\tBlock a Succ [exit] {\n"
            "\t\tJumpCmd exit\n"
            "\t}\n"
            "\tBlock exit Succ [] {\n"
            "\t\tNoSuchCmd\n"
            "\t}\n"
        ),
        path="<s>",
    )
    res = compute_dead_blocks(tac.program, ["a"], {})
    # Dropping 'a' makes 'exit' unreachable from entry, and 'e' has no
    # path to a live terminal (its only successor is dropped). Since
    # there's no live-exit-reachable path, every block becomes dead.
    assert "a" in res.dead
    assert "exit" in res.dead


def test_compute_dead_blocks_jumpi_with_user_bind():
    """e -> if B0 then a else b -> a/b -> exit. Bind B0=false drops a."""
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [a, b] {\n"
            "\t\tJumpiCmd a b B0\n"
            "\t}\n"
            "\tBlock a Succ [exit] {\n"
            "\t\tJumpCmd exit\n"
            "\t}\n"
            "\tBlock b Succ [exit] {\n"
            "\t\tJumpCmd exit\n"
            "\t}\n"
            "\tBlock exit Succ [] {\n"
            "\t\tNoSuchCmd\n"
            "\t}\n"
        ),
        path="<s>",
    )
    # Bind B0=false: jumpi's condition is false, then-edge dies, 'a' becomes
    # forward-unreachable.
    res = compute_dead_blocks(tac.program, [], {"B0": F})
    assert "a" in res.dead
    assert "b" not in res.dead
    assert "e" not in res.dead
    assert "exit" not in res.dead


def test_compute_dead_blocks_rc_cascade():
    """Drop a; via the auto-RC bind, a JumpiCmd guarded by RC_a folds and
    drops further blocks."""
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [merge] {\n"
            "\t\tJumpCmd merge\n"
            "\t}\n"
            "\tBlock merge Succ [aside, exit] {\n"
            "\t\tJumpiCmd aside exit ReachabilityCertoraa\n"
            "\t}\n"
            "\tBlock aside Succ [exit] {\n"
            "\t\tJumpCmd exit\n"
            "\t}\n"
            "\tBlock exit Succ [] {\n"
            "\t\tNoSuchCmd\n"
            "\t}\n"
            "\tBlock a Succ [] {\n"
            "\t\tAssignHavocCmd ReachabilityCertoraa\n"
            "\t}\n",
            syms="B0:bool",
        ),
        path="<s>",
    )
    # Drop block 'a': auto-bind RC_a := false; jumpi at 'merge' falls
    # through to else=exit; 'aside' becomes unreachable.
    res = compute_dead_blocks(tac.program, ["a"], {})
    assert "a" in res.dead
    assert "aside" in res.dead


def test_compute_dead_blocks_iteration_count():
    """Sanity: the iteration count is at least 1 on no-op and grows
    by at least one when a cascade fires."""
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [exit] {\n"
            "\t\tJumpCmd exit\n"
            "\t}\n"
            "\tBlock exit Succ [] {\n"
            "\t\tNoSuchCmd\n"
            "\t}\n"
        ),
        path="<s>",
    )
    res = compute_dead_blocks(tac.program, [], {})
    assert res.iterations >= 1


# ------------------------------------------------------- validate_plan


def test_validate_plan_rejects_unknown_drop():
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tNoSuchCmd\n"
            "\t}\n"
        ),
        path="<s>",
    )
    issues = validate_plan_against(tac.program, drops=["nope"])
    assert any("nope" in i for i in issues)


def test_validate_plan_rejects_rc_bind():
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tNoSuchCmd\n"
            "\t}\n"
        ),
        path="<s>",
    )
    issues = validate_plan_against(
        tac.program,
        binds={"ReachabilityCertorae": F},
    )
    assert any("ReachabilityCertorae" in i for i in issues)


def test_validate_plan_clean_when_no_issues():
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tNoSuchCmd\n"
            "\t}\n"
        ),
        path="<s>",
    )
    assert validate_plan_against(tac.program, drops=[], binds={}) == []
