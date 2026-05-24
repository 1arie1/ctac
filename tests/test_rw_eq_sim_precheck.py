"""Unit tests for the rw-eq stuttering-simulation structural pre-check.

Pure-structural tests: no SMT, no walker integration. Each test
constructs an (orig, rw) pair via parse_string and calls
``analyze_simulation``.
"""

from __future__ import annotations

import pytest

from ctac.parse import parse_string
from ctac.rw_eq.model import BlockRef, StructuralSimError
from ctac.rw_eq.sim_precheck import analyze_simulation


def _wrap(blocks: str) -> str:
    """Minimal TAC envelope around a Program body. The block-level
    pre-check only inspects ids and successors; the body cmds and
    symbol table can be empty for these tests."""
    return f"""TACSymbolTable {{
\tUserDefined {{
\t}}
\tBuiltinFunctions {{
\t}}
\tUninterpretedFunctions {{
\t}}
}}
Program {{
{blocks}
}}
Axioms {{
}}
Metas {{
  "0": []
}}
"""


def _bref(bid: str) -> BlockRef:
    return BlockRef(id=bid)


# --- Test 1: simple A -> S -> B vs A -> B -------------------------------


def test_decomp_simple():
    """LHS A -> S -> B; RHS A -> B. Single divergence, single stutter,
    single sync. The canonical baseline shape."""
    orig_src = _wrap(
        "\tBlock A Succ [S] {\n"
        "\t}\n"
        "\tBlock S Succ [B] {\n"
        "\t}\n"
        "\tBlock B Succ [] {\n"
        "\t}"
    )
    rw_src = _wrap(
        "\tBlock A Succ [B] {\n"
        "\t}\n"
        "\tBlock B Succ [] {\n"
        "\t}"
    )
    orig = parse_string(orig_src, path="<o>").program
    rw = parse_string(rw_src, path="<r>").program

    decomp = analyze_simulation(orig, rw)

    assert decomp.matched == frozenset({_bref("A"), _bref("B")})
    assert decomp.stutter == frozenset({_bref("S")})
    assert decomp.divergence_points == frozenset({_bref("A")})
    assert decomp.sync_points == frozenset({_bref("B")})
    assert decomp.stutter_owner == {_bref("S"): _bref("A")}


# --- Test 2: two disjoint divergence regions ----------------------------


def test_disjoint_passes():
    """Two divergence points feeding disjoint stutter regions. Pre-check
    returns a clean decomposition; both owners are correctly assigned."""
    # LHS:                     RHS:
    #   E (entry)               E (entry)
    #   ├→ A1 → S1 → B1         ├→ A1 → B1
    #   └→ A2 → S2 → B2         └→ A2 → B2
    #
    # E's successor lists are the same in LHS and RHS, so E is not
    # a divergence point — only A1 and A2 are.
    orig_src = _wrap(
        "\tBlock E Succ [A1, A2] {\n"
        "\t}\n"
        "\tBlock A1 Succ [S1] {\n"
        "\t}\n"
        "\tBlock A2 Succ [S2] {\n"
        "\t}\n"
        "\tBlock S1 Succ [B1] {\n"
        "\t}\n"
        "\tBlock S2 Succ [B2] {\n"
        "\t}\n"
        "\tBlock B1 Succ [] {\n"
        "\t}\n"
        "\tBlock B2 Succ [] {\n"
        "\t}"
    )
    rw_src = _wrap(
        "\tBlock E Succ [A1, A2] {\n"
        "\t}\n"
        "\tBlock A1 Succ [B1] {\n"
        "\t}\n"
        "\tBlock A2 Succ [B2] {\n"
        "\t}\n"
        "\tBlock B1 Succ [] {\n"
        "\t}\n"
        "\tBlock B2 Succ [] {\n"
        "\t}"
    )
    orig = parse_string(orig_src, path="<o>").program
    rw = parse_string(rw_src, path="<r>").program

    decomp = analyze_simulation(orig, rw)

    assert decomp.stutter == frozenset({_bref("S1"), _bref("S2")})
    assert decomp.divergence_points == frozenset({_bref("A1"), _bref("A2")})
    assert decomp.sync_points == frozenset({_bref("B1"), _bref("B2")})
    assert decomp.stutter_owner == {
        _bref("S1"): _bref("A1"),
        _bref("S2"): _bref("A2"),
    }


# --- Test 3: shared stutter region between divergence points raises ----


def test_shared_stutter_fails():
    """Two divergence points A1 and A2 both reach a stutter block S via
    disjoint LHS subgraphs, both feed into B. Per-A DEST picker would
    be ambiguous — pre-check must reject.

    Concrete shape (the journal's counterexample):
        E
        ├→ A1 → S
        └→ A2 → S
              S → B
              B → exit
    RHS:
        E → A1, A2
        A1 → B; A2 → B; B → exit.
    """
    orig_src = _wrap(
        "\tBlock E Succ [A1, A2] {\n"
        "\t}\n"
        "\tBlock A1 Succ [S] {\n"
        "\t}\n"
        "\tBlock A2 Succ [S] {\n"
        "\t}\n"
        "\tBlock S Succ [B] {\n"
        "\t}\n"
        "\tBlock B Succ [] {\n"
        "\t}"
    )
    rw_src = _wrap(
        "\tBlock E Succ [A1, A2] {\n"
        "\t}\n"
        "\tBlock A1 Succ [B] {\n"
        "\t}\n"
        "\tBlock A2 Succ [B] {\n"
        "\t}\n"
        "\tBlock B Succ [] {\n"
        "\t}"
    )
    orig = parse_string(orig_src, path="<o>").program
    rw = parse_string(rw_src, path="<r>").program

    with pytest.raises(StructuralSimError) as ei:
        analyze_simulation(orig, rw)
    msg = str(ei.value)
    # Diagnostic must name the shared stutter and both divergence points.
    assert "'S'" in msg
    assert "'A1'" in msg
    assert "'A2'" in msg


# --- Test 4: joint-post-dominator violation raises ---------------------


def test_joint_post_dom_violation():
    """A's stutter region reaches a matched block outside RHS's target
    set at A. The simulation relation is not well-defined — pre-check
    must reject.

    LHS:                       RHS:
      A → S                      A → B
      S → B                      B → C
      S → C   (leak to C)        C → exit
      B → C
      C → exit
    """
    orig_src = _wrap(
        "\tBlock A Succ [S] {\n"
        "\t}\n"
        "\tBlock S Succ [B, C] {\n"
        "\t}\n"
        "\tBlock B Succ [C] {\n"
        "\t}\n"
        "\tBlock C Succ [] {\n"
        "\t}"
    )
    rw_src = _wrap(
        "\tBlock A Succ [B] {\n"
        "\t}\n"
        "\tBlock B Succ [C] {\n"
        "\t}\n"
        "\tBlock C Succ [] {\n"
        "\t}"
    )
    orig = parse_string(orig_src, path="<o>").program
    rw = parse_string(rw_src, path="<r>").program

    with pytest.raises(StructuralSimError) as ei:
        analyze_simulation(orig, rw)
    msg = str(ei.value)
    assert "'A'" in msg
    # The expected frontier at A is just {B}; the actual frontier
    # includes C (the leak), so C must appear as "extra".
    assert "'C'" in msg


# --- Bonus: rw with a block not in orig is rejected --------------------


def test_rw_extra_block_rejected():
    """rw introducing a block id not present in orig is a contract
    violation — stuttering means rw is a subgraph, not a superset."""
    orig_src = _wrap(
        "\tBlock A Succ [B] {\n"
        "\t}\n"
        "\tBlock B Succ [] {\n"
        "\t}"
    )
    rw_src = _wrap(
        "\tBlock A Succ [X] {\n"
        "\t}\n"
        "\tBlock X Succ [B] {\n"
        "\t}\n"
        "\tBlock B Succ [] {\n"
        "\t}"
    )
    orig = parse_string(orig_src, path="<o>").program
    rw = parse_string(rw_src, path="<r>").program

    with pytest.raises(StructuralSimError) as ei:
        analyze_simulation(orig, rw)
    assert "'X'" in str(ei.value)


# --- Bonus: orphan stutter (unreachable from any divergence) rejected --


def test_orphan_stutter_rejected():
    """LHS contains a stutter block that no divergence point hands off
    to. This means rw "drops" a region of LHS without any divergence
    explanation — not a sound stuttering rewrite."""
    # LHS: A → B → C; with an orphan stutter O reachable only from C.
    # RHS keeps A, B, C but drops O. C's RHS successors are [] vs.
    # LHS's [O], so C is a divergence point — and O is reachable
    # from C, so it IS owned. Actually this construction has O
    # legitimately owned by C. Let me build a true orphan instead:
    # an LHS that has a disconnected stutter sibling.
    orig_src = _wrap(
        "\tBlock A Succ [B] {\n"
        "\t}\n"
        "\tBlock B Succ [] {\n"
        "\t}\n"
        "\tBlock O Succ [] {\n"
        "\t}"
    )
    rw_src = _wrap(
        "\tBlock A Succ [B] {\n"
        "\t}\n"
        "\tBlock B Succ [] {\n"
        "\t}"
    )
    orig = parse_string(orig_src, path="<o>").program
    rw = parse_string(rw_src, path="<r>").program

    with pytest.raises(StructuralSimError) as ei:
        analyze_simulation(orig, rw)
    assert "'O'" in str(ei.value)
