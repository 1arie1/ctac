"""Tests for ``ctac.rewrite.trail``.

Covers: Trail dedup, transitive lookup, cycle guard, JSON round-trip,
and ``resolve_substitutions`` inlining for trail targets that get
DCE'd from the rewritten program.
"""

from __future__ import annotations

from ctac.ast.nodes import ApplyExpr, ConstExpr, SymbolRef
from ctac.parse import parse_string
from ctac.rewrite.framework import rewrite_program
from ctac.rewrite.rules import default_pipeline
from ctac.rewrite.trail import (
    Substitution,
    Trail,
    resolve_substitutions,
)


def test_lookup_direct():
    t = Trail.from_substitutions(
        (Substitution("R120", SymbolRef("R306"), "HavocEquateFold"),)
    )
    assert t.lookup("R120") == SymbolRef("R306")


def test_lookup_strips_dsa_suffix():
    t = Trail.from_substitutions(
        (Substitution("R120", SymbolRef("R306"), "HavocEquateFold"),)
    )
    assert t.lookup("R120:0") == SymbolRef("R306")


def test_lookup_misses_when_not_recorded():
    t = Trail.from_substitutions(
        (Substitution("R120", SymbolRef("R306"), "HavocEquateFold"),)
    )
    assert t.lookup("R999") is None


def test_dedup_on_var_keeps_first():
    t = Trail.from_substitutions(
        (
            Substitution("R120", SymbolRef("R306"), "HavocEquateFold"),
            Substitution("R120", SymbolRef("RX"), "duplicate"),
        )
    )
    assert len(t.substitutions) == 1
    assert t.lookup("R120") == SymbolRef("R306")


def test_transitive_lookup():
    t = Trail.from_substitutions(
        (
            Substitution("R1", SymbolRef("R2"), "HavocEquateFold"),
            Substitution("R2", SymbolRef("R3"), "HavocEquateFold"),
        )
    )
    assert t.lookup("R1") == SymbolRef("R3")


def test_cycle_returns_none():
    t = Trail.from_substitutions(
        (
            Substitution("A", SymbolRef("B"), "x"),
            Substitution("B", SymbolRef("A"), "y"),
        )
    )
    assert t.lookup("A") is None


def test_json_roundtrip():
    t = Trail.from_substitutions(
        (
            Substitution("R120", SymbolRef("R306"), "HavocEquateFold"),
            Substitution("R122", SymbolRef("R306"), "HavocEquateFold"),
        )
    )
    text = t.to_json()
    t2 = Trail.from_json(text)
    assert t2.substitutions == t.substitutions


def test_json_rejects_unsupported_version():
    bad = '{"version": 999, "substitutions": []}'
    try:
        Trail.from_json(bad)
    except ValueError as e:
        assert "version" in str(e)
    else:
        raise AssertionError("expected ValueError")


def test_merge_concatenates():
    a = Trail.from_substitutions(
        (Substitution("R1", SymbolRef("R2"), "step1"),)
    )
    b = Trail.from_substitutions(
        (Substitution("R2", SymbolRef("R3"), "step2"),)
    )
    composed = a.merge(b)
    # Transitive lookup composes across steps.
    assert composed.lookup("R1") == SymbolRef("R3")


def test_resolve_keeps_survivors_as_is():
    """Trail target that's in the rewritten program is not expanded."""
    raw = (Substitution("R1", SymbolRef("R2"), "HavocEquateSubst"),)
    original = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd R1\n"
            "\t\tAssignHavocCmd R2\n"
            "\t}\n",
            syms="R1:bv256\n\tR2:bv256",
        ),
        path="<orig>",
    )
    # R2 appears in the rewritten program too.
    rewritten = original.program
    resolved = resolve_substitutions(
        raw, original_program=original.program, rewritten_program=rewritten
    )
    assert resolved[0].replacement == SymbolRef("R2")


def test_resolve_expands_dce_target_through_original_def():
    """Trail target that's NOT in the rewritten program is inlined
    via the original AssignExpCmd RHS until the leaves are survivors."""
    # Original: R1 = havoc, R3 = R2, R2 = havoc. Rewritten: only R2
    # survives (R3 got DCE'd, R1 substituted to R3).
    original = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd R1\n"
            "\t\tAssignHavocCmd R2\n"
            "\t\tAssignExpCmd R3 R2\n"
            "\t}\n",
            syms="R1:bv256\n\tR2:bv256\n\tR3:bv256",
        ),
        path="<orig>",
    )
    rewritten = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd R2\n"
            "\t}\n",
            syms="R2:bv256",
        ),
        path="<rew>",
    )
    raw = (Substitution("R1", SymbolRef("R3"), "HavocEquateSubst"),)
    resolved = resolve_substitutions(
        raw,
        original_program=original.program,
        rewritten_program=rewritten.program,
    )
    # R3's def is `R2` in the original; resolve walks through to R2.
    assert resolved[0].replacement == SymbolRef("R2")


def test_resolve_handles_const_targets():
    raw = (Substitution("R1", ConstExpr("0x42"), "Synthetic"),)
    original = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd R1\n"
            "\t}\n",
            syms="R1:bv256",
        ),
        path="<orig>",
    )
    resolved = resolve_substitutions(
        raw,
        original_program=original.program,
        rewritten_program=original.program,
    )
    assert resolved[0].replacement == ConstExpr("0x42")


def test_resolve_inlines_through_apply():
    """When the trail target is `narrow(C * X)`, resolve_substitutions
    should walk through every ``SymbolRef`` operand."""
    original = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd R1\n"
            "\t\tAssignHavocCmd R306\n"
            "\t\tAssignExpCmd I307 IntMul(0x100000000(int) R306)\n"
            "\t\tAssignExpCmd R309 ShiftRightLogical(I307 0x20)\n"
            "\t}\n",
            syms="R1:bv256\n\tR306:bv256\n\tI307:int\n\tR309:bv256",
        ),
        path="<orig>",
    )
    rewritten = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd R306\n"
            "\t}\n",
            syms="R306:bv256",
        ),
        path="<rew>",
    )
    raw = (Substitution("R1", SymbolRef("R309"), "HavocEquateFold"),)
    resolved = resolve_substitutions(
        raw,
        original_program=original.program,
        rewritten_program=rewritten.program,
    )
    # R309 was DCE'd; its def is ShiftRightLogical(I307, 0x20); I307
    # was DCE'd; its def is IntMul(0x100000000, R306); R306 survives.
    expected = ApplyExpr(
        "ShiftRightLogical",
        (
            ApplyExpr(
                "IntMul",
                (ConstExpr("0x100000000(int)"), SymbolRef("R306")),
            ),
            ConstExpr("0x20"),
        ),
    )
    assert resolved[0].replacement == expected


# ----------------------------------------------------- rule integration


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
{body}
}}
Axioms {{
}}
Metas {{
  "0": []
}}
"""


def test_havoc_equate_fold_records_substitution():
    """When HavocEquateFold fires, the substitution is recorded
    in ``RewriteResult.substitutions``. X must be a non-dummy (have
    a non-assume use) so the rule doesn't reject X as a sibling
    dummy, and X's def must come after R's constraint assume so
    HavocEquateSubst can't apply first (which would also produce
    a substitution but tagged as ``HavocEquateSubst``)."""
    tac = parse_string(
        _wrap(
            "\tBlock e Succ [] {\n"
            "\t\tAssignHavocCmd R\n"
            "\t\tAssumeExpCmd Le(R 0x800000)\n"
            "\t\tAssignHavocCmd Z\n"
            "\t\tAssignExpCmd X Add(Z 0x1)\n"
            "\t\tAssumeExpCmd Eq(R X)\n"
            "\t\tAssignExpCmd Y X\n"
            "\t\tAssertCmd Le(Y 0x10000)\n"
            "\t}\n",
            syms="R:bv256\n\tX:bv256\n\tY:bv256\n\tZ:bv256",
        ),
        path="<s>",
    )
    res = rewrite_program(tac.program, default_pipeline, symbol_sorts=tac.symbol_sorts)
    fold_subs = [s for s in res.substitutions if s.rule == "HavocEquateFold"]
    assert len(fold_subs) == 1
    sub = fold_subs[0]
    assert sub.var == "R"
    assert sub.replacement == SymbolRef("X")
