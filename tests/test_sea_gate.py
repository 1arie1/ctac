"""sea_gate encoder: thinned gated-SSA gates + verdict-equivalence with sea.

Soundness obligation: gate(k) == BLK_k under the CFG constraints, so
sea_gate must agree with sea on every verdict. These tests exercise both
phi seams (virtual DSA merges and materialized Ite-over-ReachabilityCertora)
across single / nested / multi-controller branching, plus the structural
gate shape.
"""

from __future__ import annotations

import pytest

from ctac.parse import parse_string
from ctac.smt import build_vc, render_smt_script

_HEAD = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\t%s
}
Program {
%s
}
Axioms {
}
Metas {
  "0": []
}
"""


def _wrap(syms: str, body: str) -> str:
    return _HEAD % (syms, body)


# Virtual phi: x is DSA-merged from the two arms of a diamond.
_DIAMOND = _wrap(
    "c:bool\n\tx:bv256",
    "\tBlock entry Succ [t, e] {\n"
    "\t\tAssignHavocCmd c\n"
    "\t\tJumpiCmd t e c\n"
    "\t}\n"
    "\tBlock t Succ [m] {\n"
    "\t\tAssignExpCmd x 0x1\n"
    "\t\tJumpCmd m\n"
    "\t}\n"
    "\tBlock e Succ [m] {\n"
    "\t\tAssignExpCmd x 0x2\n"
    "\t\tJumpCmd m\n"
    "\t}\n"
    "\tBlock m Succ [] {\n"
    "\t\tAssertCmd %s\n"
    "\t}",
)

# Materialized phi: an Ite over a free-havoc'd ReachabilityCertora bool,
# the production-pipeline shape. Block "1" is entry's then-target so
# ReachabilityCertora1 reaches gate__1 == c.
_MATERIALIZED = _wrap(
    "c:bool\n\txt:bv256\n\txe:bv256\n\tx:bv256\n\tReachabilityCertora1:bool",
    "\tBlock entry Succ [1, 2] {\n"
    "\t\tAssignHavocCmd c\n"
    "\t\tAssignHavocCmd ReachabilityCertora1\n"
    "\t\tJumpiCmd 1 2 c\n"
    "\t}\n"
    "\tBlock 1 Succ [3] {\n"
    "\t\tAssignExpCmd xt 0x1\n"
    "\t\tJumpCmd 3\n"
    "\t}\n"
    "\tBlock 2 Succ [3] {\n"
    "\t\tAssignExpCmd xe 0x2\n"
    "\t\tJumpCmd 3\n"
    "\t}\n"
    "\tBlock 3 Succ [] {\n"
    "\t\tAssignExpCmd x Ite(ReachabilityCertora1 xt xe)\n"
    "\t\tAssertCmd %s\n"
    "\t}",
)

# Multi-controller merge: n is control-dependent on both a and b, each of
# which can also bypass it. gate(n) is the disjunction of the two oriented
# paths. All arms write the same value so the assert is valid.
_MULTI = _wrap(
    "c1:bool\n\tc2:bool\n\tc3:bool\n\tx:bv256",
    "\tBlock entry Succ [a, b] {\n"
    "\t\tAssignHavocCmd c1\n"
    "\t\tJumpiCmd a b c1\n"
    "\t}\n"
    "\tBlock a Succ [n, xx] {\n"
    "\t\tAssignHavocCmd c2\n"
    "\t\tJumpiCmd n xx c2\n"
    "\t}\n"
    "\tBlock b Succ [n, yy] {\n"
    "\t\tAssignHavocCmd c3\n"
    "\t\tJumpiCmd n yy c3\n"
    "\t}\n"
    "\tBlock n Succ [z] {\n\t\tAssignExpCmd x 0x5\n\t\tJumpCmd z\n\t}\n"
    "\tBlock xx Succ [z] {\n\t\tAssignExpCmd x 0x5\n\t\tJumpCmd z\n\t}\n"
    "\tBlock yy Succ [z] {\n\t\tAssignExpCmd x 0x5\n\t\tJumpCmd z\n\t}\n"
    "\tBlock z Succ [] {\n\t\tAssertCmd %s\n\t}",
)

# Diamond whose merged x feeds the assert, plus an irrelevant straight-line
# chain (junk) that feeds nothing. COI must keep the virtual phi + its gate
# and drop junk.
_DIAMOND_JUNK = _wrap(
    "c:bool\n\tx:bv256\n\tjunk1:bv256\n\tjunk2:bv256",
    "\tBlock entry Succ [t, e] {\n"
    "\t\tAssignHavocCmd c\n"
    "\t\tAssignExpCmd junk1 0x7\n"
    "\t\tAssignExpCmd junk2 Add(junk1 0x1)\n"
    "\t\tJumpiCmd t e c\n"
    "\t}\n"
    "\tBlock t Succ [m] {\n\t\tAssignExpCmd x 0x1\n\t\tJumpCmd m\n\t}\n"
    "\tBlock e Succ [m] {\n\t\tAssignExpCmd x 0x2\n\t\tJumpCmd m\n\t}\n"
    "\tBlock m Succ [] {\n\t\tAssertCmd Le(x 0x2) \"valid\"\n\t}",
)

# Straight-line program: no RC vars, no DSA merges -> no gates at all.
_STRAIGHT = _wrap(
    "a:bv256\n\tb:bv256",
    "\tBlock entry Succ [] {\n"
    "\t\tAssignExpCmd a 0x1\n"
    "\t\tAssignExpCmd b Add(a 0x1)\n"
    "\t\tAssertCmd Eq(b 0x2) \"b==2\"\n"
    "\t}",
)


def _verdict(program_text: str, encoding: str) -> str:
    z3 = pytest.importorskip("z3")
    rendered = render_smt_script(build_vc(parse_string(program_text), encoding=encoding))
    solver = z3.Solver()
    solver.from_string(rendered)
    return str(solver.check())


@pytest.mark.parametrize(
    "template,predicate,expected",
    [
        (_DIAMOND, 'Le(x 0x2) "valid"', "unsat"),
        (_DIAMOND, 'Eq(x 0x1) "violable"', "sat"),
        (_MATERIALIZED, 'Le(x 0x2) "valid"', "unsat"),
        (_MATERIALIZED, 'Eq(x 0x1) "violable"', "sat"),
        (_MULTI, 'Eq(x 0x5) "valid"', "unsat"),
        (_MULTI, 'Eq(x 0x4) "violable"', "sat"),
    ],
)
def test_sea_gate_matches_sea_and_expected(template: str, predicate: str, expected: str) -> None:
    program = template % predicate
    sea = _verdict(program, "sea")
    sea_gate = _verdict(program, "sea_gate")
    assert sea == sea_gate == expected


def test_virtual_phi_gated_on_branch_condition() -> None:
    rendered = render_smt_script(
        build_vc(parse_string(_DIAMOND % 'Le(x 0x2) "valid"'), encoding="sea_gate")
    )
    # gate chain over branch conditions, and the merge gated on it.
    assert "(define-fun gate_t () Bool (and gate_entry c))" in rendered
    assert "(define-fun gate_e () Bool (and gate_entry (not c)))" in rendered
    assert "(ite gate_t " in rendered


def test_materialized_phi_alias_retargeted_to_gate() -> None:
    rendered = render_smt_script(
        build_vc(parse_string(_MATERIALIZED % 'Le(x 0x2) "valid"'), encoding="sea_gate")
    )
    # the ReachabilityCertora alias points at its gate (not BLK_).
    assert "(define-fun ReachabilityCertora1 () Bool gate__1)" in rendered
    assert "(define-fun gate__1 () Bool (and gate_entry c))" in rendered


def test_multi_controller_gate_is_disjunctive() -> None:
    rendered = render_smt_script(
        build_vc(parse_string(_MULTI % 'Eq(x 0x5) "valid"'), encoding="sea_gate")
    )
    assert "(define-fun gate_n () Bool (or (and gate_b c3) (and gate_a c2)))" in rendered


def test_coi_keeps_virtual_phi_and_drops_irrelevant() -> None:
    program = _DIAMOND_JUNK
    rendered = render_smt_script(build_vc(parse_string(program), encoding="sea_gate"))
    # virtual phi for x kept, gated on the branch condition...
    assert "(ite gate_t " in rendered
    assert "(define-fun gate_t () Bool (and gate_entry c))" in rendered
    # ...while the assert-irrelevant chain is pruned.
    assert "junk1" not in rendered
    assert "junk2" not in rendered
    # and the verdict still matches sea.
    assert _verdict(program, "sea") == _verdict(program, "sea_gate") == "unsat"


def test_coi_drops_irrelevant_static_def() -> None:
    program = _wrap(
        "a:bv256\n\tb:bv256\n\tjunk:bv256",
        "\tBlock entry Succ [] {\n"
        "\t\tAssignExpCmd a 0x1\n"
        "\t\tAssignExpCmd b Add(a 0x1)\n"
        "\t\tAssignExpCmd junk 0x7\n"
        "\t\tAssertCmd Eq(b 0x2) \"b==2\"\n"
        "\t}",
    )
    sea = render_smt_script(build_vc(parse_string(program), encoding="sea"))
    sea_gate = render_smt_script(build_vc(parse_string(program), encoding="sea_gate"))
    assert "junk" in sea
    assert "junk" not in sea_gate
    assert _verdict(program, "sea") == _verdict(program, "sea_gate") == "unsat"


def test_no_gates_without_phis() -> None:
    # A straight-line program has no RC vars and no DSA merges, so sea_gate
    # emits no gate define-funs and matches sea byte-for-byte (bar banner).
    sea = render_smt_script(build_vc(parse_string(_STRAIGHT), encoding="sea"))
    sea_gate = render_smt_script(build_vc(parse_string(_STRAIGHT), encoding="sea_gate"))
    assert "gate_" not in sea_gate
    assert sea.replace("encoding: sea", "X") == sea_gate.replace("encoding: sea_gate", "X")
