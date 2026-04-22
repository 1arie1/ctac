"""Tests for bytemap-ro support in the interpreter + model parser."""

from __future__ import annotations

from ctac.ast.nodes import ApplyExpr, ConstExpr, SymbolRef
from ctac.eval import MemoryModel, RunConfig, parse_model_text, run_program
from ctac.eval.interpreter import Evaluator
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


def test_select_on_unknown_memory_returns_zero():
    """No model entry for the memory → reads yield 0."""
    ev = Evaluator({}, normalize_symbol=lambda s: s, memory_store={})
    expr = ApplyExpr("Select", (SymbolRef("M99"), ConstExpr("42")))
    v = ev.eval_expr(expr)
    assert v.data == 0


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


def test_ctac_run_rejects_bytemap_rw(tmp_path):
    from typer.testing import CliRunner

    from ctac.tool.main import app

    src = _wrap(
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd M16\n"
        "\t\tAssignExpCmd M16 Store(M16 0x10 0x42)\n"
        "\t\tAssignExpCmd R0 Select(M16 0x10)\n"
        "\t}",
        "R0:bv256\n\tM16:bytemap",
    )
    p = tmp_path / "rw.tac"
    p.write_text(src)
    runner = CliRunner()
    result = runner.invoke(app, ["run", str(p), "--plain"])
    assert result.exit_code == 1, result.output
    assert "bytemap-rw" in result.output
