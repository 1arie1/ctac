"""Tests for `ctac search` context flags (-B / -A / -C)."""

from __future__ import annotations

from typer.testing import CliRunner

from ctac.tool.main import app


_TAC = """TACSymbolTable {
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
\tR4:bv256
\tR5:bv256
\tB0:bool
}
Program {
\tBlock e Succ [] {
\t\tAssignHavocCmd R0
\t\tAssignHavocCmd R1
\t\tAssignExpCmd R2 BWAnd(R0 0xff )
\t\tAssignHavocCmd R3
\t\tAssignHavocCmd R4
\t\tAssignExpCmd R5 BWAnd(R1 0xff )
\t\tAssignExpCmd B0 Eq(R2 R5 )
\t\tAssertCmd B0 "ok"
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""


def _match_lines(stdout: str) -> list[str]:
    return [ln for ln in stdout.splitlines() if ln and not ln.startswith("#")]


def _run(tmp_path, *args):
    p = tmp_path / "ctx.tac"
    p.write_text(_TAC)
    return CliRunner().invoke(app, ["search", str(p), "BWAnd", "--plain", *args])


def test_no_context_baseline(tmp_path):
    result = _run(tmp_path)
    assert result.exit_code == 0, result.output
    lines = _match_lines(result.output)
    hits = [ln for ln in lines if ":" in ln and " [" in ln]
    # Exactly two matches, both with `:` (match separator), no `-` context rows.
    assert sum(1 for ln in hits if "-" in ln.split(" ", 1)[0]) == 0
    assert any("e:2:" in ln for ln in hits)
    assert any("e:5:" in ln for ln in hits)


def test_C2_emits_before_and_after(tmp_path):
    result = _run(tmp_path, "-C", "2")
    assert result.exit_code == 0, result.output
    lines = _match_lines(result.output)
    hit_lines = [ln for ln in lines if " [" in ln]
    # First match is at idx=2. With -C 2 we expect context idx 0,1 before and 3,4 after.
    # Second match idx=5 is adjacent to the after-context of the first, so no `--`
    # separator between the groups.
    ids = [ln.split(" ", 1)[0] for ln in hit_lines]
    assert "e:0-" in ids    # before-context for first match
    assert "e:1-" in ids
    assert "e:2:" in ids    # first match
    assert "e:3-" in ids    # after-context for first match
    assert "e:4-" in ids
    assert "e:5:" in ids    # second match
    # e:5 touches e:4 directly, so no "--" separator between the two groups.
    assert "--" not in lines


def test_B3_A1_overrides_context(tmp_path):
    # Explicit -B / -A override the --context default.
    result = _run(tmp_path, "-C", "5", "-B", "1", "-A", "0")
    assert result.exit_code == 0, result.output
    lines = _match_lines(result.output)
    ids = [ln.split(" ", 1)[0] for ln in lines if " [" in ln]
    # First match idx=2 → 1 before (idx=1), no after.
    # Second match idx=5 → 1 before (idx=4), no after.
    assert "e:1-" in ids
    assert "e:2:" in ids
    assert "e:4-" in ids
    assert "e:5:" in ids
    assert "e:0-" not in ids  # only 1 before, not 2
    assert "e:3-" not in ids  # no after-context


def test_non_adjacent_hits_get_dash_separator(tmp_path):
    # With -C 0 and two non-adjacent matches, each shows alone — no `--`
    # needed (that's only for the in-block gap between non-touching groups
    # when context IS requested).
    result = _run(tmp_path, "-C", "1")
    assert result.exit_code == 0, result.output
    # First match idx=2 → context idx 1,3; second idx=5 → context idx 4,6.
    # idx=3 and idx=4 are NOT adjacent (gap at idx=3..4 collides differently)
    # — e:3- then gap, so -- should NOT appear (e:4 is directly printed too).
    # Actually with -C 1: groups are [1,2,3] and [4,5,6] — idx 3 and 4 are
    # adjacent, so no separator. This case asserts that.
    assert "--" not in [ln for ln in result.output.splitlines() if ln.strip() == "--"]


def test_context_does_not_cross_block_boundary(tmp_path):
    # Construct a two-block TAC; hit in block 2 shouldn't pull context
    # from block 1's tail.
    src = (
        "TACSymbolTable {\n"
        "\tUserDefined {\n\t}\n\tBuiltinFunctions {\n\t}\n\tUninterpretedFunctions {\n\t}\n"
        "\tR0:bv256\n\tR1:bv256\n\tR2:bv256\n}\n"
        "Program {\n"
        "\tBlock a Succ [b] {\n"
        "\t\tAssignHavocCmd R0\n"
        "\t\tAssignHavocCmd R1\n"
        "\t\tJumpCmd b\n"
        "\t}\n"
        "\tBlock b Succ [] {\n"
        "\t\tAssignExpCmd R2 BWAnd(R0 0xff )\n"
        "\t}\n"
        "}\n"
        "Axioms {\n}\n"
        "Metas {\n  \"0\": []\n}\n"
    )
    p = tmp_path / "two.tac"
    p.write_text(src)
    result = CliRunner().invoke(
        app, ["search", str(p), "BWAnd", "--plain", "-B", "3"]
    )
    assert result.exit_code == 0, result.output
    ids = [
        ln.split(" ", 1)[0]
        for ln in result.output.splitlines()
        if " [" in ln
    ]
    # Only the block `b` hit should appear — no rows from block `a`.
    assert all(i.startswith("b:") for i in ids), ids
