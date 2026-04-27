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
