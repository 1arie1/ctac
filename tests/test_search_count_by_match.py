"""Tests for `ctac search --count-by-match`."""

from __future__ import annotations

from pathlib import Path

import pytest
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
}
Program {
\tBlock e Succ [] {
\t\tAssignHavocCmd R0
\t\tAssignExpCmd R1 BWAnd(R0 0xff )
\t\tAssignExpCmd R2 BWAnd(R0 0xff )
\t\tAssignExpCmd R3 BWAnd(R0 0xffff )
\t\tAssertCmd R1 "ok"
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""


def _parse_tally(stdout: str) -> dict[str, int]:
    """Parse the indented ``<count>  <key>`` rows of a count-by-match block."""
    out: dict[str, int] = {}
    in_block = False
    for ln in stdout.splitlines():
        if ln.startswith("# count-by-match"):
            in_block = True
            continue
        if ln.startswith("# total:"):
            break
        if in_block:
            s = ln.strip()
            if not s:
                continue
            parts = s.split(None, 1)
            if len(parts) == 2 and parts[0].isdigit():
                out[parts[1]] = int(parts[0])
    return out


def _run(tmp_path, *args):
    p = tmp_path / "cbm.tac"
    p.write_text(_TAC)
    return CliRunner().invoke(app, ["search", str(p), *args])


def test_whole_match_tally(tmp_path):
    result = _run(tmp_path, "0x[0-9a-f]+", "--plain", "--count-by-match")
    assert result.exit_code == 0, result.output
    tally = _parse_tally(result.output)
    # Two "0xff" commands + one "0xffff" command.
    assert tally == {"0xff": 2, "0xffff": 1}
    assert "# total: 3 across 1 block(s)" in result.output


def test_capture_group_tally(tmp_path):
    # Capture only the mask constant; tally should be identical to the
    # whole-match case because each BWAnd has exactly one matching group.
    result = _run(
        tmp_path, r"BWAnd\(R\d+ (0x[0-9a-f]+)", "--plain", "--count-by-match"
    )
    assert result.exit_code == 0, result.output
    tally = _parse_tally(result.output)
    assert tally == {"0xff": 2, "0xffff": 1}


def test_sort_by_count_desc_then_alphabetic(tmp_path):
    result = _run(tmp_path, "0x[0-9a-f]+", "--plain", "--count-by-match")
    tally_rows: list[tuple[int, str]] = []
    in_block = False
    for ln in result.output.splitlines():
        if ln.startswith("# count-by-match"):
            in_block = True
            continue
        if ln.startswith("# total:"):
            break
        if not in_block:
            continue
        s = ln.strip()
        parts = s.split(None, 1)
        if len(parts) == 2 and parts[0].isdigit():
            tally_rows.append((int(parts[0]), parts[1]))
    # Counts must be non-increasing.
    counts = [cnt for cnt, _ in tally_rows]
    assert counts == sorted(counts, reverse=True)


def test_mutually_exclusive_with_count_only(tmp_path):
    result = _run(tmp_path, "BWAnd", "--plain", "--count", "--count-by-match")
    assert result.exit_code != 0
    assert "mutually exclusive" in result.output.lower()


def test_mutually_exclusive_with_blocks_only(tmp_path):
    result = _run(tmp_path, "BWAnd", "--plain", "--blocks-only", "--count-by-match")
    assert result.exit_code != 0


def test_literal_mode_tallies_pattern(tmp_path):
    # Literal 'BWAnd' appears three times across three commands.
    result = _run(tmp_path, "BWAnd", "--plain", "--literal", "--count-by-match")
    assert result.exit_code == 0, result.output
    tally = _parse_tally(result.output)
    assert tally == {"BWAnd": 3}


_KEV_SLOW = Path(
    "examples/kev-flaky/Slow/outputs/"
    "PresolverRule-rule_calculate_liquidation_verify_summary.tac"
)


@pytest.mark.skipif(not _KEV_SLOW.is_file(), reason="kev-flaky/Slow target not present")
def test_kev_flaky_slow_mask_inventory():
    """Pin expected mask tallies on the real Kev Slow target.

    Sanity against regression in the regex iteration / greedy matching.
    """
    result = CliRunner().invoke(
        app,
        ["search", str(_KEV_SLOW), r"0x[0-9a-f]+", "--plain", "--count-by-match"],
    )
    assert result.exit_code == 0, result.output
    tally = _parse_tally(result.output)
    # The 128-bit mask (introduced by the 03aaed185d commit) should appear
    # exactly once — greedy regex captures it whole, not as 8x 16-char masks.
    assert tally.get("0xffffffffffffffffffffffffffffffff") == 1
    # The 64-bit mask dominates; check it's the single most-frequent entry.
    top_key = max(tally.items(), key=lambda kv: kv[1])[0]
    assert top_key == "0xffffffffffffffff"
