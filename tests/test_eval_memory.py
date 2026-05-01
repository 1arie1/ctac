"""Tests for bytemap-ro / bytemap-rw support in the interpreter + model parser."""

from __future__ import annotations

import pytest

from ctac.ast.nodes import ApplyExpr, ConstExpr, SymbolRef
from ctac.eval import MemoryModel, RunConfig, UnknownValueError, parse_model_text, run_program
from ctac.eval.interpreter import Evaluator
from ctac.eval.types import Value
from ctac.parse import parse_string


def _wrap(body: str, syms: str) -> str:
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


def _ev() -> Evaluator:
    mem = {"M16": MemoryModel(entries={16: 393216, 32: 6442450944}, default=0)}
    return Evaluator({}, normalize_symbol=lambda s: s.split(":", 1)[0], memory_store=mem)


def test_select_hits_known_index():
    ev = _ev()
    expr = ApplyExpr("Select", (SymbolRef("M16"), ConstExpr("0x10")))
    v = ev.eval_expr(expr)
    assert v.kind == "bv"
    assert v.data == 393216


def test_select_missing_index_returns_default():
    ev = _ev()
    expr = ApplyExpr("Select", (SymbolRef("M16"), ConstExpr("0x999")))
    v = ev.eval_expr(expr)
    assert v.data == 0


def test_select_on_unknown_memory_raises():
    """No model entry for the memory → raises UnknownValueError so callers
    can fall back to the model's value for the LHS scalar."""
    ev = Evaluator({}, normalize_symbol=lambda s: s, memory_store={})
    expr = ApplyExpr("Select", (SymbolRef("M99"), ConstExpr("42")))
    with pytest.raises(UnknownValueError):
        ev.eval_expr(expr)


def test_parse_tac_model_reads_memory_entries():
    txt = (
        "TAC model begin\n"
        "R0:bv256 --> 42\n"
        "M16:bytemap --> default 0\n"
        "M16:bytemap --> 12884911680 393216\n"
        "M16:bytemap --> 0x30000248 6442450944\n"
        "TAC model end\n"
    )
    model = parse_model_text(txt)
    assert model.values["R0"].data == 42
    assert "M16" in model.memory
    m = model.memory["M16"]
    assert m.default == 0
    assert m.entries[12884911680] == 393216
    # Hex indices parse too (via _parse_number_token).
    assert m.entries[0x30000248] == 6442450944


def test_parse_smt_model_reads_uf_ite_chain():
    txt = (
        "sat\n"
        "((define-fun R0 () Int 42)\n"
        " (define-fun M16 ((x!0 Int)) Int\n"
        "   (ite (= x!0 16) 393216\n"
        "   (ite (= x!0 32) 6442450944\n"
        "     0))))\n"
    )
    model = parse_model_text(txt)
    assert "R0" in model.values
    assert "M16" in model.memory
    m = model.memory["M16"]
    assert m.entries[16] == 393216
    assert m.entries[32] == 6442450944
    assert m.default == 0


def test_parse_smt_model_kev_style_uf_with_negative_and_default_zero():
    """Shape taken directly from the Kev target's z3 output.

    Seven hot indices with mixed values (one negative via unary minus)
    and an innermost ``0`` serving as the default.
    """
    txt = (
        "sat\n"
        "((define-fun M16 ((x!0 Int)) Int\n"
        "  (ite (= x!0 12884911680) 393216\n"
        "  (ite (= x!0 12884911568) 393216\n"
        "  (ite (= x!0 12884911960) (- 1125899906842624)\n"
        "  (ite (= x!0 12884911464) 6442450944\n"
        "  (ite (= x!0 12884911216) 393216\n"
        "  (ite (= x!0 12884911584) 393216\n"
        "  (ite (= x!0 12884911224) 6442450944\n"
        "    0)))))))))\n"
    )
    model = parse_model_text(txt)
    m = model.memory["M16"]
    assert m.default == 0
    assert m.entries[12884911960] == -1125899906842624
    assert m.entries[12884911680] == 393216
    assert len(m.entries) == 7

    # Select with an index not in the table returns the default.
    mem = {"M16": m}
    ev = Evaluator({}, normalize_symbol=lambda s: s.split(":", 1)[0], memory_store=mem)
    v_default = ev.eval_expr(
        ApplyExpr("Select", (SymbolRef("M16"), ConstExpr("99999")))
    )
    assert v_default.data == 0
    # And a known index returns the stored value.
    v_hit = ev.eval_expr(
        ApplyExpr("Select", (SymbolRef("M16"), ConstExpr("12884911680")))
    )
    assert v_hit.data == 393216


def test_select_negative_value_wraps_to_twos_complement_bv256():
    """Memory values from z3 can be negative (Int sort). TAC registers are
    bv256, so ``Select`` wraps via ``% MOD_256``."""
    from ctac.eval.constants import MOD_256

    neg = -1125899906842624
    mem = {"M16": MemoryModel(entries={12884911960: neg}, default=-5)}
    ev = Evaluator({}, normalize_symbol=lambda s: s.split(":", 1)[0], memory_store=mem)

    v_hit = ev.eval_expr(
        ApplyExpr("Select", (SymbolRef("M16"), ConstExpr("12884911960")))
    )
    assert v_hit.kind == "bv"
    assert v_hit.data == neg % MOD_256
    assert 0 <= v_hit.data < MOD_256

    # Default path (miss) also wraps — a negative default becomes its
    # 2's-complement bv256 representation.
    v_miss = ev.eval_expr(
        ApplyExpr("Select", (SymbolRef("M16"), ConstExpr("0x999")))
    )
    assert v_miss.data == (-5) % MOD_256


def test_negative_memory_entries_round_trip_through_tac_text():
    """TAC model text preserves negatives verbatim; Select re-wraps at read."""
    from ctac.eval import parse_model_text
    from ctac.eval.constants import MOD_256

    txt = (
        "TAC model begin\n"
        "M16:bytemap --> default -5\n"
        "M16:bytemap --> 12884911960 -1125899906842624\n"
        "TAC model end\n"
    )
    m = parse_model_text(txt)
    mm = m.memory["M16"]
    # Raw Int values are kept as-is in the MemoryModel.
    assert mm.default == -5
    assert mm.entries[12884911960] == -1125899906842624
    # At read time, Select wraps to bv256.
    ev = Evaluator({}, normalize_symbol=lambda s: s.split(":", 1)[0], memory_store=m.memory)
    v = ev.eval_expr(
        ApplyExpr("Select", (SymbolRef("M16"), ConstExpr("12884911960")))
    )
    assert v.data == (-1125899906842624) % MOD_256


def test_interpreter_consumes_model_memory_via_runconfig():
    src = _wrap(
        "\tBlock e Succ [] {\n"
        "\t\tAssignExpCmd R0 Select(M16 0x10)\n"
        "\t}",
        "R0:bv256\n\tM16:bytemap",
    )
    tac = parse_string(src, path="<s>")
    cfg = RunConfig(
        memory_store={
            "M16": MemoryModel(entries={16: 393216}, default=0),
        },
    )
    res = run_program(tac.program, config=cfg)
    assert res.status == "done"
    assert res.final_store["R0"].data == 393216


def _bm_evaluator(memory: dict[str, MemoryModel] | None = None,
                  store: dict[str, Value] | None = None,
                  symbol_sorts: dict[str, str] | None = None,
                  model_values: dict[str, Value] | None = None) -> Evaluator:
    return Evaluator(
        store or {},
        normalize_symbol=lambda s: s.split(":", 1)[0],
        memory_store=memory or {},
        symbol_sorts=symbol_sorts or {},
        model_values=model_values or {},
    )


def test_store_then_select_round_trip():
    ev = _bm_evaluator(memory={"M0": MemoryModel(entries={}, default=0)})
    new_mm = ev._eval_bytemap_expr(
        ApplyExpr("Store", (SymbolRef("M0"), ConstExpr("0x10"), ConstExpr("0x42")))
    )
    ev.memory_store["M1"] = new_mm
    assert ev.eval_expr(ApplyExpr("Select", (SymbolRef("M1"), ConstExpr("0x10")))).data == 0x42
    assert ev.eval_expr(ApplyExpr("Select", (SymbolRef("M1"), ConstExpr("0x99")))).data == 0
    # Source map unchanged.
    assert ev.eval_expr(ApplyExpr("Select", (SymbolRef("M0"), ConstExpr("0x10")))).data == 0


def test_chained_stores_independent_links():
    ev = _bm_evaluator(memory={"M0": MemoryModel(entries={}, default=0)})
    ev.memory_store["M1"] = ev._eval_bytemap_expr(
        ApplyExpr("Store", (SymbolRef("M0"), ConstExpr("5"), ConstExpr("7")))
    )
    ev.memory_store["M2"] = ev._eval_bytemap_expr(
        ApplyExpr("Store", (SymbolRef("M1"), ConstExpr("9"), ConstExpr("11")))
    )
    assert ev.eval_expr(ApplyExpr("Select", (SymbolRef("M2"), ConstExpr("5")))).data == 7
    assert ev.eval_expr(ApplyExpr("Select", (SymbolRef("M2"), ConstExpr("9")))).data == 11
    # M1 was not mutated by the M2 update.
    assert ev.eval_expr(ApplyExpr("Select", (SymbolRef("M1"), ConstExpr("9")))).data == 0


def test_store_does_not_mutate_source_entries_dict():
    src = MemoryModel(entries={1: 2}, default=0)
    ev = _bm_evaluator(memory={"M0": src})
    new_mm = ev._eval_bytemap_expr(
        ApplyExpr("Store", (SymbolRef("M0"), ConstExpr("3"), ConstExpr("4")))
    )
    assert dict(src.entries) == {1: 2}
    assert new_mm.entries == {1: 2, 3: 4}


def test_lazy_ite_does_not_force_unchosen_branch():
    """Eager Ite would force both branches; lazy Ite must not."""
    ev = _bm_evaluator()
    # The else branch references an unknown symbol — eager eval would
    # raise UnknownValueError. Lazy eval should pick `then` and skip it.
    expr = ApplyExpr(
        "Ite",
        (
            ConstExpr("true"),
            ConstExpr("0x42"),
            ApplyExpr("Select", (SymbolRef("M_unknown"), ConstExpr("0"))),
        ),
    )
    assert ev.eval_expr(expr).data == 0x42


def test_lazy_ite_over_bytemaps():
    M_a = MemoryModel(entries={1: 100}, default=0)
    ev = _bm_evaluator(memory={"M_a": M_a})
    # cond=true → pick M_a (known); cond=false → recurse on M_b (unknown) → raise.
    chose_a = ev._eval_bytemap_expr(
        ApplyExpr("Ite", (ConstExpr("true"), SymbolRef("M_a"), SymbolRef("M_b")))
    )
    assert chose_a.entries == {1: 100}
    with pytest.raises(UnknownValueError):
        ev._eval_bytemap_expr(
            ApplyExpr("Ite", (ConstExpr("false"), SymbolRef("M_a"), SymbolRef("M_b")))
        )


_RW = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tR0:bv256
\tM0:bytemap
\tM1:bytemap
}
Program {
\tBlock e Succ [] {
\t\tAssignHavocCmd M0
\t\tAssignExpCmd M1 Store(M0 0x10 0x42)
\t\tAssignExpCmd R0 Select(M1 0x10)
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""


def test_run_program_executes_store_with_modeled_source_map():
    tac = parse_string(_RW, path="<rw>")
    cfg = RunConfig(
        memory_store={"M0": MemoryModel(entries={}, default=0)},
        symbol_sorts=tac.symbol_sorts,
    )
    res = run_program(tac.program, config=cfg)
    assert res.status == "done"
    assert res.final_store["R0"].data == 0x42
    # M1 lives in memory_store, never in scalar store.
    assert "M1" not in res.final_store


def test_run_program_falls_back_to_model_when_select_unknown():
    """Source bytemap not in memory_store → Select propagates Unknown →
    the assigned scalar LHS is taken from model_values."""
    tac = parse_string(_RW, path="<rw>")
    cfg = RunConfig(
        # No M0 entry — M0 stays unknown after havoc; M1 = Store(M0,…) is
        # also unknown; Select(M1, 0x10) raises.
        symbol_sorts=tac.symbol_sorts,
        model_values={"R0": Value("bv", 0xCAFE)},
    )
    res = run_program(tac.program, config=cfg)
    assert res.status == "done"
    assert res.final_store["R0"].data == 0xCAFE
    assert "M1" not in res.final_store
    notes = [e.note for e in res.events]
    assert "bytemap unknown" in notes
    assert "from model" in notes


def test_run_program_unknown_without_model_drops_lhs():
    tac = parse_string(_RW, path="<rw>")
    cfg = RunConfig(symbol_sorts=tac.symbol_sorts)
    res = run_program(tac.program, config=cfg)
    assert res.status == "done"
    assert "R0" not in res.final_store
    notes = [e.note for e in res.events]
    assert "unknown" in notes


_RW_PARTIAL = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tR0:bv256
\tR1:bv256
\tR2:bv256
\tM0:bytemap
}
Program {
\tBlock e Succ [] {
\t\tAssignHavocCmd M0
\t\tAssignExpCmd R0 Select(M0 0x10)
\t\tAssignExpCmd R1 Select(M0 0x20)
\t\tAssignExpCmd R2 Add(R0 R1)
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""


def test_run_program_unknown_propagates_through_arithmetic():
    """`Add(Select(M_u, i1), Select(M_u, i2))` — both halves Unknown — and
    the model has only the resulting R2; verify each scalar is taken from
    the model on its own AssignExpCmd via the fallback path."""
    tac = parse_string(_RW_PARTIAL, path="<rwp>")
    cfg = RunConfig(
        symbol_sorts=tac.symbol_sorts,
        model_values={
            "R0": Value("bv", 1),
            "R1": Value("bv", 2),
            "R2": Value("bv", 3),
        },
    )
    res = run_program(tac.program, config=cfg)
    assert res.status == "done"
    assert res.final_store["R0"].data == 1
    assert res.final_store["R1"].data == 2
    assert res.final_store["R2"].data == 3


def test_assert_on_unknown_is_inconclusive():
    src = _wrap(
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd M0\n"
        "\t\tAssignExpCmd B0 Eq(Select(M0 0x10) 0x42)\n"
        "\t\tAssertCmd B0 \"check\"\n"
        "\t}",
        "B0:bool\n\tM0:bytemap",
    )
    tac = parse_string(src, path="<a>")
    cfg = RunConfig(symbol_sorts=tac.symbol_sorts)
    res = run_program(tac.program, config=cfg)
    assert res.assert_ok == 0
    assert res.assert_fail == 0
    assert any(e.note == "inconclusive" for e in res.events)


def test_ctac_run_executes_bytemap_rw(tmp_path):
    """The CLI no longer rejects bytemap-rw input."""
    from typer.testing import CliRunner

    from ctac.tool.main import app

    p = tmp_path / "rw.tac"
    p.write_text(_RW)
    runner = CliRunner()
    result = runner.invoke(app, ["run", str(p), "--plain"])
    # No model → R0 ends Unknown → final state has no R0 mismatch fail.
    assert "input error" not in result.output
    # Exit code: 0 ok, 2 stopped (assume), 3 error/max_steps. Either 0 or
    # 3 is acceptable on a model-less run.
    assert result.exit_code in (0, 2, 3), result.output


def test_ctac_run_trace_marks_default_sentinel_havoc(tmp_path):
    """When --model leaves a havoc'd symbol unconstrained, the trace
    line for that havoc is marked ``(default)``. Symbols the model
    does cover stay unmarked. Lets the reader tell at a glance which
    Ite arms / asserts are anchored on real model values vs the
    12_345_678 sentinel."""
    from typer.testing import CliRunner

    from ctac.tool.main import app

    tac = (
        "TACSymbolTable {\n"
        "\tUserDefined {\n\t}\n"
        "\tBuiltinFunctions {\n\t}\n"
        "\tUninterpretedFunctions {\n\t}\n"
        "\tR0:bv256\n"
        "\tR1:bv256\n"
        "\tR2:bv256\n"
        "}\n"
        "Program {\n"
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd R0\n"
        "\t\tAssignHavocCmd R1\n"
        "\t\tAssignExpCmd R2 Add(R0 R1)\n"
        "\t}\n"
        "}\n"
        "Axioms {\n}\n"
        'Metas {\n  "0": []\n}\n'
    )
    tac_path = tmp_path / "havoc_demo.tac"
    tac_path.write_text(tac)
    model_path = tmp_path / "havoc_demo.tacmodel"
    # Only R0 is in the model; R1 must hit the sentinel default.
    model_path.write_text(
        "TAC model begin\n"
        "R0:bv256 --> 0xcafe\n"
        "TAC model end\n"
    )
    runner = CliRunner()
    result = runner.invoke(
        app,
        ["run", str(tac_path), "--model", str(model_path), "--plain", "--trace"],
    )
    assert result.exit_code in (0, 2, 3), result.output

    lines = [ln for ln in result.output.splitlines() if "havoc" in ln or "= R0 + R1" in ln]
    # R0 had a model hit -> no marker.
    r0_line = next(ln for ln in lines if "R0 = havoc" in ln)
    assert "(default)" not in r0_line, r0_line
    # R1 missed the model -> sentinel -> (default) marker.
    r1_line = next(ln for ln in lines if "R1 = havoc" in ln)
    assert "(default)" in r1_line, r1_line
    assert "1234_5678" in r1_line  # decimal-grouped 12_345_678 sentinel
    # R2 is computed from operands, not a havoc -> no marker even though
    # one operand came from the sentinel.
    r2_line = next(ln for ln in lines if "= R0 + R1" in ln)
    assert "(default)" not in r2_line, r2_line


def test_ctac_run_executes_bytemap_rw_with_model_fallback(tmp_path):
    """End-to-end: source map absent → Select propagates Unknown → model
    fills the scalar LHS at the AssignExpCmd."""
    from typer.testing import CliRunner

    from ctac.tool.main import app

    tac_path = tmp_path / "rw.tac"
    tac_path.write_text(_RW)
    model_path = tmp_path / "rw.tacmodel"
    model_path.write_text(
        "TAC model begin\n"
        "R0:bv256 --> 0xcafe\n"
        "TAC model end\n"
    )
    runner = CliRunner()
    result = runner.invoke(
        app, ["run", str(tac_path), "--model", str(model_path), "--plain"]
    )
    assert "input error" not in result.output
    assert result.exit_code in (0, 2, 3), result.output


_CLI_BM_TAC = """TACSymbolTable {
\tUserDefined {
\t}
\tBuiltinFunctions {
\t}
\tUninterpretedFunctions {
\t}
\tR0:bv256
\tR1:bv256
\tB0:bool
\tM16:bytemap
}
Program {
\tBlock e Succ [] {
\t\tAssignHavocCmd M16
\t\tAssignExpCmd R0 Select(M16 0x10)
\t\tAssignExpCmd R1 Select(M16 0x20)
\t\tAssignExpCmd B0 Eq(R0 R1)
\t\tAssertCmd B0 "eq"
\t}
}
Axioms {
}
Metas {
  "0": []
}
"""


def test_ctac_run_loads_bytemap_from_tac_format_model(tmp_path):
    """The ``ctac run --model`` CLI handles bytemap entries in TAC text
    format (produced by ``ctac smt --model <path>``)."""
    from typer.testing import CliRunner

    from ctac.tool.main import app

    tac_path = tmp_path / "bm.tac"
    tac_path.write_text(_CLI_BM_TAC)

    model_path = tmp_path / "bm.tacmodel"
    model_path.write_text(
        "TAC model begin\n"
        "M16:bytemap --> default 0\n"
        "M16:bytemap --> 16 42\n"
        "M16:bytemap --> 32 7\n"
        "R0:bv256 --> 42\n"
        "R1:bv256 --> 7\n"
        "B0:bool --> false\n"
        "TAC model end\n"
    )

    runner = CliRunner()
    result = runner.invoke(
        app, ["run", str(tac_path), "--model", str(model_path), "--plain"]
    )
    assert result.exit_code in (0, 2, 3), result.output
    assert "# model memory: 1 bytemap(s), 2 entry(ies)" in result.output


def test_ctac_run_loads_bytemap_from_smt_format_model(tmp_path):
    """Same as above but the model is raw SMT-LIB (``z3 -model`` stdout)."""
    from typer.testing import CliRunner

    from ctac.tool.main import app

    tac_path = tmp_path / "bm.tac"
    tac_path.write_text(_CLI_BM_TAC)

    model_path = tmp_path / "bm.z3model"
    model_path.write_text(
        "sat\n"
        "(\n"
        "  (define-fun R0 () Int 42)\n"
        "  (define-fun R1 () Int 7)\n"
        "  (define-fun B0 () Bool false)\n"
        "  (define-fun M16 ((x!0 Int)) Int\n"
        "    (ite (= x!0 16) 42\n"
        "    (ite (= x!0 32) 7\n"
        "      0)))\n"
        ")\n"
    )

    runner = CliRunner()
    result = runner.invoke(
        app, ["run", str(tac_path), "--model", str(model_path), "--plain"]
    )
    assert result.exit_code in (0, 2, 3), result.output
    assert "# model memory: 1 bytemap(s), 2 entry(ies)" in result.output
