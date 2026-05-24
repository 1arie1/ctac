"""Unit tests for ctac.transform.cfg_simplify.

Synthetic ``parse_string`` fixtures exercise each shape of
fall-through and the safety-skipping behavior.
"""

from __future__ import annotations

from ctac.ast.nodes import JumpCmd, JumpiCmd
from ctac.parse import parse_string
from ctac.transform.cfg_simplify import simplify_cfg


def _wrap(blocks: str, *, syms: str = "") -> str:
    sym_line = f"\t{syms}" if syms else ""
    return f"""TACSymbolTable {{
\tUserDefined {{
\t}}
\tBuiltinFunctions {{
\t}}
\tUninterpretedFunctions {{
\t}}
{sym_line}
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


def _block(program, bid: str):
    for b in program.blocks:
        if b.id == bid:
            return b
    raise AssertionError(f"no block {bid!r} in result")


def _ids(program) -> list[str]:
    return [b.id for b in program.blocks]


# --- Fixture 1: simplest fall-through chain ----------------------------


def test_simple_annotation_only_falls_through():
    """LHS A -> X -> B where X has only annotation/label cmds and no
    terminator. After: X dropped, A's JumpCmd retargets B."""
    src = _wrap(
        '\tBlock A Succ [X] {\n'
        '\t\tJumpCmd X\n'
        '\t}\n'
        '\tBlock X Succ [B] {\n'
        '\t\tAnnotationCmd JSON{"key":"foo"}\n'
        '\t\tLabelCmd "marker"\n'
        '\t}\n'
        '\tBlock B Succ [] {\n'
        '\t}'
    )
    prog = parse_string(src, path="<t>").program
    new_prog, report = simplify_cfg(prog)

    assert report.dropped_blocks == ("X",)
    assert report.rewires == (("A", "X", "B"),)
    assert report.skipped_multipred == ()
    assert _ids(new_prog) == ["A", "B"]

    a = _block(new_prog, "A")
    assert a.successors == ["B"]
    assert isinstance(a.commands[-1], JumpCmd)
    assert a.commands[-1].target == "B"


# --- Fixture 2: JumpiCmd predecessor with one drop arm ----------------


def test_jumpicmd_pred_retarget():
    """Pred P's JumpiCmd has then=X (drop) else=Z. X falls through to Y.
    After: P has JumpiCmd then=Y else=Z."""
    src = _wrap(
        '\tBlock P Succ [X, Z] {\n'
        '\t\tAssignExpCmd C true\n'
        '\t\tJumpiCmd X Z C\n'
        '\t}\n'
        '\tBlock X Succ [Y] {\n'
        '\t\tAnnotationCmd JSON{"k":"v"}\n'
        '\t}\n'
        '\tBlock Y Succ [] {\n'
        '\t}\n'
        '\tBlock Z Succ [] {\n'
        '\t}',
        syms="C:bool",
    )
    prog = parse_string(src, path="<t>").program
    new_prog, report = simplify_cfg(prog)

    assert report.dropped_blocks == ("X",)
    assert report.rewires == (("P", "X", "Y"),)
    assert "X" not in _ids(new_prog)

    p = _block(new_prog, "P")
    assert p.successors == ["Y", "Z"]
    term = p.commands[-1]
    assert isinstance(term, JumpiCmd)
    assert term.then_target == "Y"
    assert term.else_target == "Z"
    assert term.condition == "C"


# --- Fixture 3: both JumpiCmd arms collapse ----------------------------


def test_both_jumpicmd_arms_collapse_to_jumpcmd():
    """Pred P has JumpiCmd then=X1 else=X2 where both X1 and X2 are
    fall-throughs into Y. After: P has JumpCmd Y (collapsed)."""
    src = _wrap(
        '\tBlock P Succ [X1, X2] {\n'
        '\t\tAssignExpCmd C true\n'
        '\t\tJumpiCmd X1 X2 C\n'
        '\t}\n'
        '\tBlock X1 Succ [Y] {\n'
        '\t\tAnnotationCmd JSON{"k":1}\n'
        '\t}\n'
        '\tBlock X2 Succ [Y] {\n'
        '\t\tAnnotationCmd JSON{"k":2}\n'
        '\t}\n'
        '\tBlock Y Succ [] {\n'
        '\t}',
        syms="C:bool",
    )
    prog = parse_string(src, path="<t>").program
    new_prog, report = simplify_cfg(prog)

    assert set(report.dropped_blocks) == {"X1", "X2"}
    # Two rewires (one per arm) collapsing to the same target
    assert sorted(report.rewires) == [("P", "X1", "Y"), ("P", "X2", "Y")]

    p = _block(new_prog, "P")
    term = p.commands[-1]
    assert isinstance(term, JumpCmd)
    assert term.target == "Y"
    assert p.successors == ["Y"]


# --- Fixture 4: multi-pred fall-through skipped ------------------------


def test_multi_pred_fall_through_skipped():
    """Fall-through X with two LHS preds. Skipped (would violate
    rw-eq's disjoint-stutter-region invariant)."""
    src = _wrap(
        '\tBlock E Succ [P1, P2] {\n'
        '\t\tAssignExpCmd C0 true\n'
        '\t\tJumpiCmd P1 P2 C0\n'
        '\t}\n'
        '\tBlock P1 Succ [X] {\n'
        '\t\tJumpCmd X\n'
        '\t}\n'
        '\tBlock P2 Succ [X] {\n'
        '\t\tJumpCmd X\n'
        '\t}\n'
        '\tBlock X Succ [Y] {\n'
        '\t\tAnnotationCmd JSON{"k":1}\n'
        '\t}\n'
        '\tBlock Y Succ [] {\n'
        '\t}',
        syms="C0:bool",
    )
    prog = parse_string(src, path="<t>").program
    new_prog, report = simplify_cfg(prog)

    assert report.dropped_blocks == ()
    assert report.rewires == ()
    assert report.skipped_multipred == ("X",)
    # Program is unchanged
    assert _ids(new_prog) == _ids(prog)


# --- Fixture 5: executable cmd disqualifies ---------------------------


def test_executable_cmd_blocks_disqualified():
    """A block with an AssignExpCmd is not a fall-through candidate
    even if it also has annotations."""
    src = _wrap(
        '\tBlock A Succ [X] {\n'
        '\t\tJumpCmd X\n'
        '\t}\n'
        '\tBlock X Succ [B] {\n'
        '\t\tAnnotationCmd JSON{"k":1}\n'
        '\t\tAssignExpCmd R 0x1\n'
        '\t}\n'
        '\tBlock B Succ [] {\n'
        '\t}',
        syms="R:bv256",
    )
    prog = parse_string(src, path="<t>").program
    new_prog, report = simplify_cfg(prog)

    assert report.is_noop
    assert _ids(new_prog) == _ids(prog)


# --- Fixture 6: idempotence ------------------------------------------


def test_idempotent():
    """Re-running on the simplified result is a no-op."""
    src = _wrap(
        '\tBlock A Succ [X] {\n'
        '\t\tJumpCmd X\n'
        '\t}\n'
        '\tBlock X Succ [B] {\n'
        '\t\tAnnotationCmd JSON{"k":1}\n'
        '\t}\n'
        '\tBlock B Succ [] {\n'
        '\t}'
    )
    prog = parse_string(src, path="<t>").program
    new_prog, report = simplify_cfg(prog)
    assert report.n_dropped == 1

    new_prog2, report2 = simplify_cfg(new_prog)
    assert report2.is_noop
    assert _ids(new_prog2) == _ids(new_prog)


# --- Fixture 7: self-loop skipped ------------------------------------


def test_self_loop_skipped():
    """Annotation-only block with Succ [self] is degenerate; skipped."""
    src = _wrap(
        '\tBlock A Succ [X] {\n'
        '\t\tJumpCmd X\n'
        '\t}\n'
        '\tBlock X Succ [X] {\n'
        '\t\tAnnotationCmd JSON{"k":1}\n'
        '\t}'
    )
    prog = parse_string(src, path="<t>").program
    new_prog, report = simplify_cfg(prog)
    assert report.is_noop
    assert "X" in _ids(new_prog)


# --- Fixture 8: entry block excluded (no preds) ----------------------


def test_entry_block_excluded():
    """An annotation-only entry block (no LHS predecessors) isn't a
    droppable candidate because there's nothing to rewire."""
    src = _wrap(
        '\tBlock E Succ [B] {\n'
        '\t\tAnnotationCmd JSON{"k":1}\n'
        '\t}\n'
        '\tBlock B Succ [] {\n'
        '\t}'
    )
    prog = parse_string(src, path="<t>").program
    new_prog, report = simplify_cfg(prog)
    assert report.is_noop
    assert _ids(new_prog) == ["E", "B"]


# --- Bonus: chain of fall-throughs collapses in one pass --------------


def test_fixpoint_iteration_unlocks_followups():
    """A block that's multi-pred in the original may become single-
    pred after a first round of drops removes its other predecessors.
    Verify simplify_cfg iterates internally and catches the followup."""
    # LHS:                     after pass 1:           after pass 2:
    #   E → P1, P2               E → P1, P2              E → P1, P2
    #   P1 → S1 → M              P1 → M                  P1 → M
    #   P2 → S2 → M              P2 → M                  P2 → M
    #   M → A (stutter)          M → A (stutter)         M → end
    #   A → end                  A → end
    # In the original, M's preds = {S1, S2}; M is multi-pred.
    # After pass 1 drops S1, S2 (each single-pred), P1 → M and
    # P2 → M directly — but M's pred set is now {P1, P2}, still
    # multi. So this specific fixture doesn't unlock M.
    #
    # Build a tighter case: a chain that gives M a unique pred only
    # after stutter drops.
    #   LHS: E → S1 → M → A → end          (S1, A are stutters with
    #                                        unique preds)
    #   After pass 1: E → M → end          (S1 and A dropped)
    #   After pass 2: M, if now annotation-only, gets dropped.
    # But M has executable content here; the test fixture needs M
    # to be annotation-only to test the followup-unlock.
    #
    # Concrete fixture: A → X1 → M → X2 → B, where X1 and X2 are
    # multi-pred initially but become unique after some other drop.
    src = _wrap(
        '\tBlock E Succ [P] {\n'
        '\t\tJumpCmd P\n'
        '\t}\n'
        '\tBlock P Succ [F1, F2] {\n'
        '\t\tAssignExpCmd C true\n'
        '\t\tJumpiCmd F1 F2 C\n'
        '\t}\n'
        '\tBlock F1 Succ [J] {\n'
        '\t\tAnnotationCmd JSON{"k":1}\n'
        '\t}\n'
        '\tBlock F2 Succ [J] {\n'
        '\t\tAnnotationCmd JSON{"k":2}\n'
        '\t}\n'
        '\tBlock J Succ [End] {\n'
        '\t\tAnnotationCmd JSON{"k":3}\n'
        '\t}\n'
        '\tBlock End Succ [] {\n'
        '\t}',
        syms="C:bool",
    )
    prog = parse_string(src, path="<t>").program
    new_prog, report = simplify_cfg(prog)
    # Pass 1: F1, F2 (each unique-pred via P's JumpiCmd arms) drop;
    # P's JumpiCmd both arms collapse to → J, becoming JumpCmd J.
    # Now J has unique pred {P}; J was multi-pred in the original
    # ({F1, F2}) → would have been skipped in single-pass mode.
    # Pass 2: J (annotation-only, unique pred now) drops; P → End.
    assert set(report.dropped_blocks) == {"F1", "F2", "J"}
    assert "J" not in [b.id for b in new_prog.blocks]
    # P ends up with JumpCmd End (both JumpiCmd arms collapsed
    # twice, through F1/F2 then J).
    p = _block(new_prog, "P")
    assert isinstance(p.commands[-1], JumpCmd)
    assert p.commands[-1].target == "End"


def test_chain_of_fall_throughs():
    """LHS A -> X -> Y -> Z; X and Y both annotation-only fall-throughs.
    One invocation drops both and rewires A directly to Z."""
    src = _wrap(
        '\tBlock A Succ [X] {\n'
        '\t\tJumpCmd X\n'
        '\t}\n'
        '\tBlock X Succ [Y] {\n'
        '\t\tAnnotationCmd JSON{"k":1}\n'
        '\t}\n'
        '\tBlock Y Succ [Z] {\n'
        '\t\tAnnotationCmd JSON{"k":2}\n'
        '\t}\n'
        '\tBlock Z Succ [] {\n'
        '\t}'
    )
    prog = parse_string(src, path="<t>").program
    new_prog, report = simplify_cfg(prog)

    assert set(report.dropped_blocks) == {"X", "Y"}
    assert ("A", "X", "Z") in report.rewires
    assert _ids(new_prog) == ["A", "Z"]
    a = _block(new_prog, "A")
    assert a.successors == ["Z"]
    assert a.commands[-1].target == "Z"
