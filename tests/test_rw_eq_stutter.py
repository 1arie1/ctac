"""End-to-end fixtures for the rw-eq stuttering-simulation walker.

Each test constructs an (orig, rw) pair by hand via ``parse_string``
(no rewriter pass involved — that's intentional; the CFG-cleanup
rewriter doesn't exist yet) and runs ``emit_equivalence_program``,
verifying the emission shape, symbol minting, and CHK count.

End-to-end SMT discharge tests (UNSAT for sound rewrites, SAT for
the intentionally unsound case) live in fixtures 5–8, landed in the
following commit.
"""

from __future__ import annotations

from ctac.ast.nodes import (
    ApplyExpr,
    AssertCmd,
    AssignExpCmd,
    ConstExpr,
    JumpCmd,
    SymbolRef,
)
from ctac.parse import parse_string
from ctac.rw_eq import emit_equivalence_program
from ctac.rw_eq.model import BlockRef


def _wrap(body: str, *, syms: str = "") -> str:
    """Minimal TAC envelope. Caller supplies the Program body and any
    symbol declarations needed for the test's commands."""
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
{body}
}}
Axioms {{
}}
Metas {{
  "0": []
}}
"""


def _b(bid: str) -> BlockRef:
    return BlockRef(id=bid)


def _block(program, bid: str):
    for b in program.blocks:
        if b.id == bid:
            return b
    raise AssertionError(f"no block {bid!r}")


def _sym_names(res) -> list[str]:
    return [name for name, _ in res.extra_symbols]


# --- Fixture 1: simple A -> S -> B chain ------------------------------


def test_stutter_simple_chain():
    """LHS A -> S -> B with all unconditional jumps; RHS A -> B
    directly. A is a divergence point; S is the single stutter; B is
    a sync point with one LHS predecessor (S). The IN_DEST ITE chain
    degenerates to ``IN_DEST_B := DEST_A``."""
    orig_src = _wrap(
        "\tBlock A Succ [S] {\n"
        "\t\tJumpCmd S\n"
        "\t}\n"
        "\tBlock S Succ [B] {\n"
        "\t\tJumpCmd B\n"
        "\t}\n"
        "\tBlock B Succ [] {\n"
        "\t}"
    )
    rw_src = _wrap(
        "\tBlock A Succ [B] {\n"
        "\t\tJumpCmd B\n"
        "\t}\n"
        "\tBlock B Succ [] {\n"
        "\t}"
    )
    orig = parse_string(orig_src, path="<o>").program
    rw = parse_string(rw_src, path="<r>").program

    res = emit_equivalence_program(orig, rw)

    # Decomposition surfaces in EquivResult
    assert res.stutter_blocks == (_b("S"),)
    assert res.divergence_points == (_b("A"),)
    assert res.sync_points == (_b("B"),)

    # Symbols minted: DEST_A (for divergence A), IN_DEST_B (for sync B
    # with preds), CHK0 (for the IN_DEST equality)
    names = _sym_names(res)
    assert "DEST_A" in names
    assert "IN_DEST_B" in names
    assert any(n.startswith("CHK") for n in names)

    # Block A keeps its LHS terminator (JumpCmd S) and has DEST_A := 1
    # spliced in before it (id_of[B] = 1 under sorted({A, B}) → A=0, B=1).
    a_block = _block(res.program, "A")
    a_cmds = a_block.commands
    # Last cmd should be JumpCmd S (LHS terminator)
    assert isinstance(a_cmds[-1], JumpCmd) and a_cmds[-1].target == "S"
    # The penultimate cmd should be the DEST_A assignment
    dest_cmd = next(
        c for c in a_cmds if isinstance(c, AssignExpCmd) and c.lhs == "DEST_A"
    )
    # id_of[B] = 1 (B is the larger of {A, B} sorted)
    assert dest_cmd.rhs == ConstExpr(value="1")

    # Block B has IN_DEST_B := DEST_A at entry, then CHK = Eq(IN_DEST_B, 1),
    # then assert CHK.
    b_block = _block(res.program, "B")
    b_cmds = b_block.commands
    in_dest_assign = next(
        c for c in b_cmds if isinstance(c, AssignExpCmd) and c.lhs == "IN_DEST_B"
    )
    # Single-pred degenerate ITE → val_S directly = DEST_A (S's owner)
    assert in_dest_assign.rhs == SymbolRef(name="DEST_A")
    # An AssertCmd appears in B
    assert any(isinstance(c, AssertCmd) for c in b_cmds)


# --- Fixture 2: conditional divergence (JumpiCmd on COND) -------------


def test_stutter_conditional_divergence():
    """LHS A → {S1, S2} (JumpiCmd on COND); S1 → B; S2 → C. RHS
    A → {B, C} (same COND). Two divergence-derived sync points; one
    pred each (S1 / S2)."""
    orig_src = _wrap(
        "\tBlock A Succ [S1, S2] {\n"
        "\t\tAssignExpCmd COND true\n"
        "\t\tJumpiCmd S1 S2 COND\n"
        "\t}\n"
        "\tBlock S1 Succ [B] {\n"
        "\t\tJumpCmd B\n"
        "\t}\n"
        "\tBlock S2 Succ [C] {\n"
        "\t\tJumpCmd C\n"
        "\t}\n"
        "\tBlock B Succ [] {\n"
        "\t}\n"
        "\tBlock C Succ [] {\n"
        "\t}",
        syms="COND:bool",
    )
    rw_src = _wrap(
        "\tBlock A Succ [B, C] {\n"
        "\t\tAssignExpCmd COND true\n"
        "\t\tJumpiCmd B C COND\n"
        "\t}\n"
        "\tBlock B Succ [] {\n"
        "\t}\n"
        "\tBlock C Succ [] {\n"
        "\t}",
        syms="COND:bool",
    )
    orig = parse_string(orig_src, path="<o>").program
    rw = parse_string(rw_src, path="<r>").program

    res = emit_equivalence_program(orig, rw)

    assert res.stutter_blocks == (_b("S1"), _b("S2"))
    assert res.divergence_points == (_b("A"),)
    assert res.sync_points == (_b("B"), _b("C"))

    names = _sym_names(res)
    assert "DEST_A" in names
    assert "IN_DEST_B" in names
    assert "IN_DEST_C" in names

    # id_of after sort({A, B, C}) → A=0, B=1, C=2
    # DEST_A := ite(COND, id_of[B], id_of[C]) = ite(COND, 1, 2)
    a_block = _block(res.program, "A")
    dest_cmd = next(
        c for c in a_block.commands
        if isinstance(c, AssignExpCmd) and c.lhs == "DEST_A"
    )
    assert isinstance(dest_cmd.rhs, ApplyExpr)
    assert dest_cmd.rhs.op == "Ite"
    assert dest_cmd.rhs.args[0] == SymbolRef(name="COND")
    assert dest_cmd.rhs.args[1] == ConstExpr(value="1")
    assert dest_cmd.rhs.args[2] == ConstExpr(value="2")

    # B's IN_DEST_B := DEST_A (single pred S1 → owner A)
    b_block = _block(res.program, "B")
    b_in_dest = next(
        c for c in b_block.commands
        if isinstance(c, AssignExpCmd) and c.lhs == "IN_DEST_B"
    )
    assert b_in_dest.rhs == SymbolRef(name="DEST_A")


# --- Fixture 3: two disjoint divergence regions -----------------------


def test_multi_divergence_disjoint():
    """E -> A1 / A2 (both div), A1 -> S1 -> B1 (sync), A2 -> S2 -> B2
    (sync). Two independent divergence points / stutter regions /
    sync points."""
    orig_src = _wrap(
        "\tBlock E Succ [A1, A2] {\n"
        "\t\tAssignExpCmd C0 true\n"
        "\t\tJumpiCmd A1 A2 C0\n"
        "\t}\n"
        "\tBlock A1 Succ [S1] {\n"
        "\t\tJumpCmd S1\n"
        "\t}\n"
        "\tBlock A2 Succ [S2] {\n"
        "\t\tJumpCmd S2\n"
        "\t}\n"
        "\tBlock S1 Succ [B1] {\n"
        "\t\tJumpCmd B1\n"
        "\t}\n"
        "\tBlock S2 Succ [B2] {\n"
        "\t\tJumpCmd B2\n"
        "\t}\n"
        "\tBlock B1 Succ [] {\n"
        "\t}\n"
        "\tBlock B2 Succ [] {\n"
        "\t}",
        syms="C0:bool",
    )
    rw_src = _wrap(
        "\tBlock E Succ [A1, A2] {\n"
        "\t\tAssignExpCmd C0 true\n"
        "\t\tJumpiCmd A1 A2 C0\n"
        "\t}\n"
        "\tBlock A1 Succ [B1] {\n"
        "\t\tJumpCmd B1\n"
        "\t}\n"
        "\tBlock A2 Succ [B2] {\n"
        "\t\tJumpCmd B2\n"
        "\t}\n"
        "\tBlock B1 Succ [] {\n"
        "\t}\n"
        "\tBlock B2 Succ [] {\n"
        "\t}",
        syms="C0:bool",
    )
    orig = parse_string(orig_src, path="<o>").program
    rw = parse_string(rw_src, path="<r>").program

    res = emit_equivalence_program(orig, rw)

    assert res.stutter_blocks == (_b("S1"), _b("S2"))
    assert res.divergence_points == (_b("A1"), _b("A2"))
    assert res.sync_points == (_b("B1"), _b("B2"))

    names = _sym_names(res)
    assert "DEST_A1" in names
    assert "DEST_A2" in names
    assert "IN_DEST_B1" in names
    assert "IN_DEST_B2" in names

    # Each sync's IN_DEST points to its own DEST (no cross-contamination)
    b1 = _block(res.program, "B1")
    b1_in_dest = next(
        c for c in b1.commands if isinstance(c, AssignExpCmd) and c.lhs == "IN_DEST_B1"
    )
    assert b1_in_dest.rhs == SymbolRef(name="DEST_A1")
    b2 = _block(res.program, "B2")
    b2_in_dest = next(
        c for c in b2.commands if isinstance(c, AssignExpCmd) and c.lhs == "IN_DEST_B2"
    )
    assert b2_in_dest.rhs == SymbolRef(name="DEST_A2")


# --- Fixture 4: three-way case split at a sync point ------------------


def test_three_way_case_split():
    """Sync point B has three LHS preds with distinct case classes:
    one stutter (S, owned by div A), one divergence common (X), and
    one non-divergence common (N). Verify the IN_DEST ITE chain mixes
    the three val shapes correctly.

    LHS:                          RHS:
      E → A, N (JumpiCmd C0)       E → A, N
      A → S, X (JumpiCmd C1)       A → B, X (JumpiCmd C1)
      S → B (stutter to B)         X → B, C (JumpiCmd C2)
      X → S2, B (JumpiCmd C2)      N → B
      S2 → C (stutter to C)        B → exit
      N → B                        C → exit
      B → exit
      C → exit

    A is divergence (succ_L={S,X}, succ_R={B,X}). A's τ-frontier
    via {S, A, X(matched), B(matched)} = {X, B}. T = {B, X}. ✓
    X is divergence (succ_L={S2,B}, succ_R={B,C}). X's τ-frontier
    via {S2, X, B, C} = {B, C}. T = {B, C}. ✓
    N is non-divergence common (succ_L=succ_R={B}).

    B's LHS preds: {S, X, N}. RHS preds: {A, X, N}. Different → sync.
    Sorted as [N, S, X]:
      N: non-div common → val_N = id_of[B]
      S: stutter (owned by A) → val_S = DEST_A
      X: divergence common → val_X = DEST_X
    """
    orig_src = _wrap(
        "\tBlock E Succ [A, N] {\n"
        "\t\tAssignExpCmd C0 true\n"
        "\t\tJumpiCmd A N C0\n"
        "\t}\n"
        "\tBlock A Succ [S, X] {\n"
        "\t\tAssignExpCmd C1 true\n"
        "\t\tJumpiCmd S X C1\n"
        "\t}\n"
        "\tBlock S Succ [B] {\n"
        "\t\tJumpCmd B\n"
        "\t}\n"
        "\tBlock X Succ [S2, B] {\n"
        "\t\tAssignExpCmd C2 true\n"
        "\t\tJumpiCmd S2 B C2\n"
        "\t}\n"
        "\tBlock S2 Succ [C] {\n"
        "\t\tJumpCmd C\n"
        "\t}\n"
        "\tBlock N Succ [B] {\n"
        "\t\tJumpCmd B\n"
        "\t}\n"
        "\tBlock B Succ [] {\n"
        "\t}\n"
        "\tBlock C Succ [] {\n"
        "\t}",
        syms="C0:bool\n\tC1:bool\n\tC2:bool",
    )
    rw_src = _wrap(
        "\tBlock E Succ [A, N] {\n"
        "\t\tAssignExpCmd C0 true\n"
        "\t\tJumpiCmd A N C0\n"
        "\t}\n"
        "\tBlock A Succ [B, X] {\n"
        "\t\tAssignExpCmd C1 true\n"
        "\t\tJumpiCmd B X C1\n"
        "\t}\n"
        "\tBlock X Succ [B, C] {\n"
        "\t\tAssignExpCmd C2 true\n"
        "\t\tJumpiCmd B C C2\n"
        "\t}\n"
        "\tBlock N Succ [B] {\n"
        "\t\tJumpCmd B\n"
        "\t}\n"
        "\tBlock B Succ [] {\n"
        "\t}\n"
        "\tBlock C Succ [] {\n"
        "\t}",
        syms="C0:bool\n\tC1:bool\n\tC2:bool",
    )
    orig = parse_string(orig_src, path="<o>").program
    rw = parse_string(rw_src, path="<r>").program

    res = emit_equivalence_program(orig, rw)

    assert res.stutter_blocks == (_b("S"), _b("S2"))
    assert res.divergence_points == (_b("A"), _b("X"))
    assert _b("B") in res.sync_points

    # id_of: sorted matched = [A, B, C, E, N, X] → id_of[B] = 1
    b_block = _block(res.program, "B")
    b_in_dest = next(
        c for c in b_block.commands
        if isinstance(c, AssignExpCmd) and c.lhs == "IN_DEST_B"
    )
    # Preds sorted: [N, S, X]. Chain:
    #   Ite(RC_N, val_N=ConstExpr("1"),
    #     Ite(RC_S, val_S=DEST_A,
    #         val_X=DEST_X))
    outer = b_in_dest.rhs
    assert isinstance(outer, ApplyExpr) and outer.op == "Ite"
    rc_n, val_n, inner = outer.args
    assert rc_n == SymbolRef(name="ReachabilityCertoraN")
    assert val_n == ConstExpr(value="1")

    assert isinstance(inner, ApplyExpr) and inner.op == "Ite"
    rc_s, val_s, val_x = inner.args
    assert rc_s == SymbolRef(name="ReachabilityCertoraS")
    assert val_s == SymbolRef(name="DEST_A")
    assert val_x == SymbolRef(name="DEST_X")


# --- Sanity: existing lockstep mode still triggers when ids match ----


def test_lockstep_mode_unchanged():
    """When orig and rw have identical block-id sets in the same order,
    the existing lockstep path engages (no stutter machinery, no extras)."""
    src = _wrap(
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd X\n"
        "\t}",
        syms="X:bv256",
    )
    orig = parse_string(src, path="<o>").program
    rw = parse_string(src, path="<r>").program

    res = emit_equivalence_program(orig, rw)
    assert res.stutter_blocks == ()
    assert res.divergence_points == ()
    assert res.sync_points == ()
    # No DEST/IN_DEST symbols minted in lockstep mode
    names = _sym_names(res)
    assert not any(n.startswith("DEST_") for n in names)
    assert not any(n.startswith("IN_DEST_") for n in names)
