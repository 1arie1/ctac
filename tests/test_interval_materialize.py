"""End-to-end validation of the interval domain via rw-eq.

For each fixture program:

1. Run ``materialize_intervals`` to emit inferred bounds as
   ``assume`` commands at end-of-block.
2. Run ``rw_eq.emit_equivalence_program(orig, materialized)`` —
   every materialized assume that the original doesn't have triggers
   rule 4 (rhs-only assume), emitting a CHK assertion that the
   condition holds.
3. Split via ``ua.split_asserts``; for every split tagged
   ``rw-eq:`` build a VC and run z3.

Every CHK must discharge ``unsat``. A SAT means the analysis
asserted a fact that doesn't follow from the original — i.e., the
analysis was unsound on that program.

Fast structural tests always run; the z3-discharging test is gated on
``z3`` being on PATH so devs without it still get the structural
feedback.
"""

from __future__ import annotations

import dataclasses
import shutil
import subprocess

import pytest

from ctac.analysis.abs_int import materialize_intervals
from ctac.ast.nodes import (
    ApplyExpr,
    AssertCmd,
    AssumeExpCmd,
    SymbolRef,
)
from ctac.ir.models import TacFile
from ctac.parse import parse_string
from ctac.rw_eq import emit_equivalence_program
from ctac.smt import build_vc, render_smt_script
from ctac.ua import split_asserts


def _z3_available() -> bool:
    return shutil.which("z3") is not None


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


# ---- Fixtures ---------------------------------------------------------

# Single block with an entry-block range assume + a derived value.
# After analysis: static[X] = [0, 100], static[Y] = [0, 200] (precise
# via IntMul). Materialization emits both at entry's end. rw-eq
# should produce CHKs that all discharge unsat.
SIMPLE_RANGE_FIXTURE = _wrap(
    "\tBlock e Succ [] {\n"
    "\t\tAssignHavocCmd X\n"
    "\t\tAssumeExpCmd Le(X 0x64)\n"
    "\t\tAssignExpCmd Y IntMul(0x2(int) X)\n"
    "\t\tAssertCmd:1 Le(Y 0x12c) \"y_bounded\"\n"
    "\t}",
    syms="X:int\n\tY:int",
)


# Diamond CFG: entry → BT/BF → BJ. Refinements on BT and BF that lub
# at BJ. Tests join soundness of materialized refinements.
DIAMOND_FIXTURE = _wrap(
    "\tBlock e Succ [BT, BF] {\n"
    "\t\tAssignHavocCmd X\n"
    "\t\tAssumeExpCmd Le(X 0x64)\n"
    "\t\tAssignHavocCmd c\n"
    "\t\tJumpiCmd BT BF c\n"
    "\t}\n"
    "\tBlock BT Succ [BJ] {\n"
    "\t\tAssumeExpCmd Le(X 0xa)\n"
    "\t\tJumpCmd BJ\n"
    "\t}\n"
    "\tBlock BF Succ [BJ] {\n"
    "\t\tAssumeExpCmd Ge(X 0x32)\n"
    "\t\tJumpCmd BJ\n"
    "\t}\n"
    "\tBlock BJ Succ [] {\n"
    "\t\tAssertCmd:1 Le(X 0x64) \"x_still_bounded_after_join\"\n"
    "\t}",
    syms="X:int\n\tc:bool",
)


# bv256 with safe_math_narrow_bv256 wrapping IntAdd: the canonical
# wrap-checked form in the corpus. Tests narrow_clamp + IntAdd
# precision propagation.
NARROW_FIXTURE = _wrap(
    "\tBlock e Succ [] {\n"
    "\t\tAssignHavocCmd A\n"
    "\t\tAssumeExpCmd Le(A 0x64)\n"
    "\t\tAssignHavocCmd B\n"
    "\t\tAssumeExpCmd Le(B 0xc8)\n"
    "\t\tAssignExpCmd S Apply(safe_math_narrow_bv256:bif IntAdd(A B))\n"
    "\t\tAssertCmd:1 Le(S 0x12c) \"sum_bounded\"\n"
    "\t}",
    syms="A:bv256\n\tB:bv256\n\tS:bv256",
)


# Eq-to-const refinement: assume X == 42 pins X to a single point.
EQ_POINT_FIXTURE = _wrap(
    "\tBlock e Succ [] {\n"
    "\t\tAssignHavocCmd X\n"
    "\t\tAssumeExpCmd Eq(X 0x2a)\n"
    "\t\tAssignExpCmd Y IntAdd(X 0x1(int))\n"
    "\t\tAssertCmd:1 Eq(Y 0x2b) \"y_is_43\"\n"
    "\t}",
    syms="X:int\n\tY:int",
)


_FIXTURES = [
    ("simple_range", SIMPLE_RANGE_FIXTURE),
    ("diamond", DIAMOND_FIXTURE),
    ("narrow", NARROW_FIXTURE),
    ("eq_point", EQ_POINT_FIXTURE),
]


# ---- Structural tests -------------------------------------------------


@pytest.mark.parametrize("name,src", _FIXTURES, ids=[n for n, _ in _FIXTURES])
def test_materialize_then_rw_eq_runs_without_exceptions(
    name: str, src: str
) -> None:
    """Plumbing check: parse → materialize → rw-eq → split. No
    exceptions, well-formed outputs."""
    tac = parse_string(src, path=f"<{name}>")
    materialized, report = materialize_intervals(
        tac.program, symbol_sorts=tac.symbol_sorts
    )
    assert report.assumes_emitted > 0, (
        f"{name}: nothing materialized — fixture isn't exercising the "
        f"analysis"
    )
    eq = emit_equivalence_program(tac.program, materialized)
    # Rule 4 (rhs-only assume) should fire for every materialized
    # assume the original doesn't pair with.
    assert eq.rule_hits.get("4_rhs_assume", 0) >= report.assumes_emitted, (
        f"{name}: rw-eq accepted fewer rhs-only assumes than emitted "
        f"({eq.rule_hits=}, materialized={report.assumes_emitted})"
    )
    split = split_asserts(eq.program)
    assert split.outputs, f"{name}: split produced no outputs"


# ---- z3-discharging test ---------------------------------------------


def _build_smt_for(tac_file: TacFile, program_override) -> str:
    """Build SMT-LIB script for a single-assert program reusing the
    fixture's symbol table / axioms / metas envelope."""
    new_tac = dataclasses.replace(tac_file, program=program_override)
    script = build_vc(new_tac)
    return render_smt_script(script)


@pytest.mark.skipif(not _z3_available(), reason="z3 not on PATH")
@pytest.mark.parametrize("name,src", _FIXTURES, ids=[n for n, _ in _FIXTURES])
def test_materialized_assumes_discharge_unsat(name: str, src: str) -> None:
    """For every CHK assertion (tagged ``rw-eq:`` by
    ``emit_equivalence_program``), z3 must discharge ``unsat`` —
    meaning the original program's state at the emission point
    implies the materialized assume's condition."""
    tac = parse_string(src, path=f"<{name}>")
    materialized, _ = materialize_intervals(
        tac.program, symbol_sorts=tac.symbol_sorts
    )
    eq = emit_equivalence_program(tac.program, materialized)
    split = split_asserts(eq.program)

    rw_eq_splits = [
        out for out in split.outputs if (out.message or "").startswith("rw-eq:")
    ]
    assert rw_eq_splits, (
        f"{name}: no rw-eq tagged splits — the test isn't checking "
        f"materialized-assume soundness"
    )

    for out in rw_eq_splits:
        smt_text = _build_smt_for(tac, out.program)
        result = subprocess.run(
            ["z3", "-smt2", "-T:5", "-in"],
            input=smt_text,
            capture_output=True,
            text=True,
            timeout=30,
        )
        verdict = (
            result.stdout.strip().splitlines()[0] if result.stdout else ""
        )
        assert verdict == "unsat", (
            f"{name}: rw-eq split #{out.index} ({out.message!r}) returned "
            f"{verdict!r} (expected unsat). z3 stdout:\n{result.stdout}\n"
            f"z3 stderr:\n{result.stderr}"
        )


# ---- Static-fact emission site regression -----------------------------
# Pins the latest materialization fix: a DSA-static var defined in a
# non-entry block must have its static assume emitted at the def
# block's end, NOT at entry's end. Emitting at entry would reference
# a symbol the original program hasn't defined yet — sea_vc would
# (correctly) reject with use-before-def, breaking the pipeline on
# any real-target program where some bool/int is defined downstream.


def _refers_to(expr, var_name: str) -> bool:
    """Recursive: does the expression reference SymbolRef(name=var)?"""
    if isinstance(expr, SymbolRef):
        return expr.name == var_name
    if isinstance(expr, ApplyExpr):
        return any(_refers_to(a, var_name) for a in expr.args)
    return False


def _block_assume_vars(block) -> set[str]:
    """Symbols mentioned in any AssumeExpCmd in this block."""
    out: set[str] = set()
    for cmd in block.commands:
        if isinstance(cmd, AssumeExpCmd):
            _collect_symbols(cmd.condition, out)
    return out


def _collect_symbols(expr, out: set[str]) -> None:
    if isinstance(expr, SymbolRef):
        out.add(expr.name)
    elif isinstance(expr, ApplyExpr):
        for a in expr.args:
            _collect_symbols(a, out)


def test_static_var_defined_in_non_entry_emits_at_def_block_not_entry() -> None:
    """Regression: when X is DSA-static but defined in a non-entry
    block, materialize_intervals must emit its static assume at the
    def block's end, not at the entry block's end.

    The bug we're pinning: an earlier materialize implementation put
    every static fact at entry's end. For X defined in a downstream
    block, that produced ``Le(X, ...)`` referencing a not-yet-defined
    symbol → sea_vc rejects with use-before-def at first encode."""
    src = _wrap(
        "\tBlock e Succ [B1] {\n"
        "\t\tJumpCmd B1\n"
        "\t}\n"
        "\tBlock B1 Succ [] {\n"
        "\t\tAssignHavocCmd X\n"
        "\t\tAssumeExpCmd Le(X 0x64)\n"
        "\t\tAssertCmd:1 Le(X 0x64) \"x_bounded\"\n"
        "\t}",
        syms="X:bv256",
    )
    tac = parse_string(src, path="<def_in_b1>")
    augmented, _ = materialize_intervals(
        tac.program, symbol_sorts=tac.symbol_sorts
    )

    by_id = augmented.block_by_id()
    e_assume_vars = _block_assume_vars(by_id["e"])
    b1_assume_vars = _block_assume_vars(by_id["B1"])

    # Entry must NOT mention X — at entry's end, X has no def yet.
    assert "X" not in e_assume_vars, (
        f"entry block leaked an assume on undefined X: {e_assume_vars}"
    )
    # B1 (the def block) is where the materialized assume must land.
    assert "X" in b1_assume_vars, (
        f"B1's local refinement on X wasn't materialized: {b1_assume_vars}"
    )

    # End-to-end check: the augmented program should encode without
    # use-before-def. (The earlier bug would fail right here.)
    new_tac = dataclasses.replace(tac, program=augmented)
    build_vc(new_tac)  # raises SmtEncodingError if anything is off


def test_materialize_skips_emission_at_non_dominated_block() -> None:
    """Dominance gate: a var defined in only one branch of a join
    must NOT have its assume materialized at the join. The join
    isn't dominated by the def block; sea_vc's unconditional def
    encoding could otherwise let z3 construct counter-examples by
    taking the un-defining path."""
    src = _wrap(
        # Diamond: e splits to BT or BF; both join at J.
        # X is defined only in BT. J is NOT dominated by BT.
        "\tBlock e Succ [BT, BF] {\n"
        "\t\tAssignHavocCmd c\n"
        "\t\tJumpiCmd BT BF c\n"
        "\t}\n"
        "\tBlock BT Succ [J] {\n"
        "\t\tAssignHavocCmd X\n"
        "\t\tAssumeExpCmd Le(X 0x64)\n"
        "\t\tJumpCmd J\n"
        "\t}\n"
        "\tBlock BF Succ [J] {\n"
        "\t\tJumpCmd J\n"
        "\t}\n"
        "\tBlock J Succ [] {\n"
        "\t\tAssertCmd:1 Eq(0x0 0x0) \"trivial\"\n"
        "\t}",
        syms="X:bv256\n\tc:bool",
    )
    tac = parse_string(src, path="<diamond>")
    augmented, _ = materialize_intervals(
        tac.program, symbol_sorts=tac.symbol_sorts
    )
    by_id = {b.id: b for b in augmented.blocks}
    # BT (the def block, which dominates itself) → emission allowed.
    bt_assumes = [
        c for c in by_id["BT"].commands if isinstance(c, AssumeExpCmd)
    ]
    bt_x_assume = any(
        "X" in (c.raw or "") for c in bt_assumes
    )
    assert bt_x_assume, "expected materialized assume on X at BT (def block)"
    # J (NOT dominated by BT) → no emission for X.
    j_cmds = by_id["J"].commands
    j_x_assumes = [
        c for c in j_cmds
        if isinstance(c, AssumeExpCmd) and "X" in (c.raw or "")
    ]
    assert not j_x_assumes, (
        f"materialization emitted an X-assume at non-dominated join J: "
        f"{[c.raw for c in j_x_assumes]}"
    )


def test_materialize_emits_at_dominated_block() -> None:
    """A linear chain ``e → B1 → B2``: B2 IS dominated by B1, so a
    refinement on a B1-defined var emitted via B1's local should
    propagate to B2 via the analysis and be materializable there
    too. Pinning the positive case so the dominance gate isn't
    over-restrictive."""
    src = _wrap(
        "\tBlock e Succ [B1] {\n"
        "\t\tAssignHavocCmd X\n"
        "\t\tJumpCmd B1\n"
        "\t}\n"
        "\tBlock B1 Succ [B2] {\n"
        "\t\tAssumeExpCmd Le(X 0x64)\n"
        "\t\tJumpCmd B2\n"
        "\t}\n"
        "\tBlock B2 Succ [] {\n"
        "\t\tAssertCmd:1 Eq(0x0 0x0) \"trivial\"\n"
        "\t}",
        syms="X:bv256",
    )
    tac = parse_string(src, path="<chain>")
    augmented, _ = materialize_intervals(
        tac.program, symbol_sorts=tac.symbol_sorts
    )
    by_id = {b.id: b for b in augmented.blocks}
    # X is defined at e (DSA-static, single havoc). e's def block is e
    # itself, which dominates B1 and B2. The refinement at B1 should
    # propagate via analysis and materialize at B1 / B2 ends.
    b1_x_assumes = [
        c for c in by_id["B1"].commands
        if isinstance(c, AssumeExpCmd) and "X" in (c.raw or "")
    ]
    # B1 has the original assume + a materialized one on X.
    assert len(b1_x_assumes) >= 1
    # B2 is dominated by e (X's def block) → can carry the propagated
    # local refinement and materialize.
    b2_x_assumes = [
        c for c in by_id["B2"].commands
        if isinstance(c, AssumeExpCmd) and "X" in (c.raw or "")
    ]
    assert b2_x_assumes, "expected materialized assume on X at dominated block B2"


def test_materialized_assumes_inserted_before_terminator_not_after() -> None:
    """Regression for emission-at-end-of-block: the materialized
    assume must come BEFORE the block's terminator (JumpCmd /
    JumpiCmd / AssertCmd), not appended after. A post-terminator
    assume would be unreachable in the merged program."""
    src = _wrap(
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd X\n"
        "\t\tAssumeExpCmd Le(X 0x64)\n"
        "\t\tAssertCmd:1 Le(X 0x64) \"bound\"\n"
        "\t}",
        syms="X:bv256",
    )
    tac = parse_string(src, path="<terminator>")
    augmented, _ = materialize_intervals(
        tac.program, symbol_sorts=tac.symbol_sorts
    )
    cmds = augmented.blocks[0].commands
    assume_indices = [
        i for i, c in enumerate(cmds) if isinstance(c, AssumeExpCmd)
    ]
    # Identify the terminator (the AssertCmd here is the last cmd
    # because emission inserts before it).
    assert_indices = [
        i for i, c in enumerate(cmds) if isinstance(c, AssertCmd)
    ]
    assert assert_indices, "fixture lost its assert"
    last_assume = max(assume_indices)
    assert last_assume < assert_indices[0], (
        f"a materialized assume landed at index {last_assume} but the "
        f"terminator AssertCmd is at {assert_indices[0]} — assumes must "
        f"sit before the terminator"
    )


# ---- Negative test (unsound materialization → sat) ------------------
# Confirms the validator actually catches bad assumes — without this,
# "unsat" could be vacuous (e.g., if the validation pipeline silently
# dropped CHKs).


def _inject_assume_at_entry_end(
    tac: TacFile, condition_src: str, *, raw: str
):
    """Build a copy of `tac.program` with an extra assume manually
    injected before the entry block's terminator. Used to seed
    deliberately-unsound materializations for the negative test."""
    from ctac.ast.nodes import (
        ApplyExpr,
        AssumeExpCmd,
        ConstExpr,
        SymbolRef,
    )
    from ctac.ir.models import TacBlock, TacProgram

    # Hand-built condition for `Le(X 0x32)` (= X <= 50). Used to inject
    # a too-tight bound when X is only known to be <= 100.
    if condition_src == "Le(X 0x32)":
        cond = ApplyExpr(
            op="Le", args=(SymbolRef(name="X"), ConstExpr(value="0x32"))
        )
    else:
        raise ValueError(f"unknown condition: {condition_src}")

    new_blocks = []
    for i, b in enumerate(tac.program.blocks):
        if i != 0:
            new_blocks.append(b)
            continue
        # Insert before the terminator (last cmd).
        cmds = list(b.commands)
        injected = AssumeExpCmd(raw=raw, condition=cond)
        # Find terminator index.
        from ctac.ast.nodes import AssertCmd, JumpCmd, JumpiCmd

        term_idx = len(cmds)
        for j in range(len(cmds) - 1, -1, -1):
            if isinstance(cmds[j], (AssertCmd, JumpCmd, JumpiCmd)):
                term_idx = j
                break
        new_cmds = cmds[:term_idx] + [injected] + cmds[term_idx:]
        new_blocks.append(
            TacBlock(id=b.id, successors=list(b.successors), commands=new_cmds)
        )
    return TacProgram(blocks=new_blocks)


@pytest.mark.skipif(not _z3_available(), reason="z3 not on PATH")
def test_unsound_assume_is_caught_by_rw_eq() -> None:
    """Inject an assume that's tighter than what the original program
    establishes (X <= 50 when only X <= 100 is known) and verify z3
    returns sat — confirming the validator detects unsoundness, not
    just plumbing-pass."""
    tac = parse_string(SIMPLE_RANGE_FIXTURE, path="<unsound>")
    # Original establishes X <= 100; this injection asserts X <= 50,
    # which can fail (e.g., X = 75).
    bad = _inject_assume_at_entry_end(tac, "Le(X 0x32)", raw="AssumeExpCmd Le(X 0x32)")
    eq = emit_equivalence_program(tac.program, bad)
    split = split_asserts(eq.program)
    rw_eq_splits = [
        out for out in split.outputs if (out.message or "").startswith("rw-eq:")
    ]
    assert rw_eq_splits, "no rw-eq splits — test setup wrong"
    found_sat = False
    for out in rw_eq_splits:
        smt_text = _build_smt_for(tac, out.program)
        result = subprocess.run(
            ["z3", "-smt2", "-T:5", "-in"],
            input=smt_text,
            capture_output=True,
            text=True,
            timeout=30,
        )
        verdict = (
            result.stdout.strip().splitlines()[0] if result.stdout else ""
        )
        if verdict == "sat":
            found_sat = True
            break
    assert found_sat, (
        "expected at least one rw-eq split to return sat for the "
        "deliberately-unsound assume Le(X, 0x32) when only Le(X, 0x64) "
        "is established by the original program"
    )
