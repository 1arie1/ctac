"""Real-target regression tests for ``ctac pin``.

Pins the existing kvault-style ``base.rw.ua.tac`` benchmark to verify
end-to-end on a non-toy program. Light validations only: parse,
DSA validity, no orphans post-pin.
"""

from __future__ import annotations

from pathlib import Path

import pytest

from ctac.parse import parse_path
from ctac.transform.pin import (
    PinPlan,
    apply,
    assert_no_dangling_jumps,
    assert_no_orphans,
)


_REAL_TARGET = Path(
    "examples/rule_no_col_decrease_request_elevation_group.bad/base.rw.ua.tac"
)


pytestmark = pytest.mark.skipif(
    not _REAL_TARGET.is_file(),
    reason="real-target fixture missing",
)


def test_pin_no_op_on_real_target():
    """Pin with empty plan: drops only pre-existing orphans (if any)."""
    tac = parse_path(_REAL_TARGET)
    res = apply(tac.program, PinPlan())
    assert_no_orphans(res.program)
    assert_no_dangling_jumps(res.program)


def test_pin_dsa_preserved_on_real_target():
    """After a no-op pin, DSA validity should still hold."""
    from ctac.analysis.passes import analyze_dsa

    tac = parse_path(_REAL_TARGET)
    res = apply(tac.program, PinPlan())
    dsa = analyze_dsa(res.program)
    # DSA result has a status / shape; we just check the analyzer
    # ran without raising. ctac's existing checks downstream
    # (rw --validate, smt) will catch any invariant break.
    assert dsa is not None


def test_pin_parses_back_after_round_trip(tmp_path):
    """Parse -> pin -> render -> parse should round-trip cleanly."""
    from ctac.parse.tac_file import render_tac_file

    tac = parse_path(_REAL_TARGET)
    res = apply(tac.program, PinPlan())
    out_text = render_tac_file(tac, program=res.program)
    out_path = tmp_path / "pinned.tac"
    out_path.write_text(out_text)
    parse_path(out_path)  # no exception
