"""Unit + CLI tests for the ``--trace`` JSONL rule-fire log."""

from __future__ import annotations

import json
from pathlib import Path

from typer.testing import CliRunner

from ctac.parse import parse_string
from ctac.rewrite import rewrite_program
from ctac.rewrite.framework import TraceEntry
from ctac.rewrite.rules import (
    ADD_BV_TO_INT,
    EQ_CONST_FOLD,
    MUL_BV_TO_INT,
    N2_LOW_MASK,
    RANGE_FOLD,
)
from ctac.tool.main import app


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
\tBlock e Succ [] {{
{body}
\t}}
}}
Axioms {{
}}
Metas {{
  "0": []
}}
"""


def _collect(rules, body: str, *, syms: str, phase: str = "test") -> list[TraceEntry]:
    tac = parse_string(_wrap(body, syms=syms), path="<s>")
    out: list[TraceEntry] = []
    rewrite_program(
        tac.program,
        rules,
        phase=phase,
        trace_sink=out.append,
        symbol_sorts=tac.symbol_sorts,
    )
    return out


def test_trace_records_top_level_fire() -> None:
    """A rule that fires at the top of the RHS records ``path == ()``."""
    entries = _collect(
        (N2_LOW_MASK,),
        "\t\tAssignExpCmd R1 BWAnd(R0 0xff)",
        syms="R0:bv256\n\tR1:bv256",
    )
    assert len(entries) == 1
    e = entries[0]
    assert e.rule == "N2"
    assert e.path == ()
    assert e.host_kind == "assign"
    assert e.host_lhs == "R1"
    assert e.before.startswith("BWAnd(")
    assert e.after.startswith("Mod(")
    assert e.phase == "test"
    assert e.iteration == 1


def test_trace_records_subexpression_path() -> None:
    """A rule that fires inside a sub-arg records the descent path.

    ``Add(R0, BWAnd(R1, 0xff))``: N2 fires inside ``args[1]`` only — the
    only N2-shaped sub-expression. The top-level ``Add`` is untouched."""
    entries = _collect(
        (N2_LOW_MASK,),
        "\t\tAssignExpCmd R2 Add(R0 BWAnd(R1 0xff))",
        syms="R0:bv256\n\tR1:bv256\n\tR2:bv256",
    )
    n2_hits = [e for e in entries if e.rule == "N2"]
    assert len(n2_hits) == 1
    assert n2_hits[0].path == (1,)
    assert n2_hits[0].host_lhs == "R2"


def test_trace_chain_preserves_before_after_invariant() -> None:
    """Successive fires at the same path satisfy ``entries[k+1].before
    == entries[k].after``. The MUL_BV_TO_INT -> RangeFold chain on
    ``Mul(0x0, R0)`` is the canonical example."""
    entries = _collect(
        (MUL_BV_TO_INT, RANGE_FOLD),
        "\t\tAssignHavocCmd R0\n\t\tAssignExpCmd R1 Mul(0x0 R0)",
        syms="R0:bv256\n\tR1:bv256",
    )
    same_path = [e for e in entries if e.path == () and e.host_lhs == "R1"]
    assert len(same_path) >= 2
    for prev, cur in zip(same_path, same_path[1:]):
        assert cur.before == prev.after


def test_trace_iteration_tagging() -> None:
    """A fixed-point that takes >1 round emits entries with iterations
    1..N. Use ``Add(0x0, BWAnd(R0, 0xff))``: iter 1 turns ``BWAnd`` into
    ``Mod`` (N2) and ``Add`` into ``IntAdd`` (ADD_BV_TO_INT) at the top;
    iter 2 has nothing to do, terminating."""
    entries = _collect(
        (N2_LOW_MASK, ADD_BV_TO_INT),
        "\t\tAssignExpCmd R1 Add(0x0 BWAnd(R0 0xff))",
        syms="R0:bv256\n\tR1:bv256",
    )
    iters = sorted({e.iteration for e in entries})
    assert iters[0] == 1
    # Both rules fired in iteration 1 — the test pins lower-bound only;
    # exact iteration count depends on rule ordering invariants.


def test_trace_phase_tag_propagates() -> None:
    """The ``phase`` arg shows up verbatim on every record."""
    entries = _collect(
        (N2_LOW_MASK,),
        "\t\tAssignExpCmd R1 BWAnd(R0 0xff)",
        syms="R0:bv256\n\tR1:bv256",
        phase="cse-early",
    )
    assert len(entries) == 1
    assert entries[0].phase == "cse-early"


def test_trace_disabled_skips_pretty_printer(monkeypatch) -> None:
    """When ``trace_sink is None``, no ``RawPrettyPrinter`` instance is
    constructed and ``print_expr`` is never called. Monkeypatch
    ``print_expr`` to raise; the no-trace path must still succeed."""
    from ctac.ast import pretty as pretty_mod

    def boom(*_args, **_kwargs):  # pragma: no cover - asserted not-called
        raise AssertionError("RawPrettyPrinter.print_expr should not be called")

    monkeypatch.setattr(pretty_mod.RawPrettyPrinter, "print_expr", boom)
    tac = parse_string(
        _wrap(
            "\t\tAssignExpCmd R1 BWAnd(R0 0xff)",
            syms="R0:bv256\n\tR1:bv256",
        ),
        path="<s>",
    )
    res = rewrite_program(tac.program, (N2_LOW_MASK,))
    assert res.hits_by_rule == {"N2": 1}


def test_trace_assume_host_kind() -> None:
    """``host_kind`` is ``"assume"`` when the rule fires inside an
    ``AssumeExpCmd.condition``; ``host_lhs`` is None."""
    entries = _collect(
        (EQ_CONST_FOLD,),
        "\t\tAssumeExpCmd Eq(0x1 0x1)",
        syms="R0:bv256",
    )
    assert len(entries) == 1
    assert entries[0].host_kind == "assume"
    assert entries[0].host_lhs is None


def test_trace_assert_host_kind() -> None:
    """``host_kind == "assert"`` for ``AssertCmd.predicate`` rewrites."""
    entries = _collect(
        (EQ_CONST_FOLD,),
        "\t\tAssertCmd Eq(0x1 0x1) \"msg\"",
        syms="R0:bv256",
    )
    assert any(e.host_kind == "assert" for e in entries)
    assert all(e.host_lhs is None for e in entries if e.host_kind == "assert")


def test_cli_trace_writes_jsonl(tmp_path: Path) -> None:
    """End-to-end: ``ctac rw --trace <path>`` writes one JSON object per
    line, with the schema fields the user filters on."""
    src = _wrap(
        "\t\tAssignHavocCmd R0\n"
        "\t\tAssignExpCmd R1 Mul(0x0 R0)\n"
        "\t\tAssignExpCmd R2 Add(R0 R1)\n"
        "\t\tAssertCmd false \"boom\"",
        syms="R0:bv256\n\tR1:bv256\n\tR2:bv256",
    )
    src_path = tmp_path / "in.tac"
    out_path = tmp_path / "out.tac"
    trace_path = tmp_path / "trace.jsonl"
    src_path.write_text(src)

    runner = CliRunner()
    result = runner.invoke(
        app,
        ["rw", str(src_path), "--plain", "-o", str(out_path), "--trace", str(trace_path)],
    )
    assert result.exit_code == 0, result.output

    lines = trace_path.read_text().splitlines()
    assert lines, "expected at least one trace line"
    records = [json.loads(ln) for ln in lines]
    expected_keys = {
        "phase", "iteration", "block_id", "cmd_index",
        "host_kind", "host_lhs", "path", "rule", "before", "after",
    }
    for r in records:
        assert set(r.keys()) == expected_keys
    # The Mul(0x0, R0) -> IntMul -> 0x0 chain at R1 is the easy anchor.
    r1_records = [r for r in records if r.get("host_lhs") == "R1"]
    assert len(r1_records) >= 2
    rules_seen = {r["rule"] for r in r1_records}
    assert "MUL_BV_TO_INT" in rules_seen
