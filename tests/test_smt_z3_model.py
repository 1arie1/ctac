from __future__ import annotations

from ctac.smt.z3_model import parse_z3_sat_output, z3_model_to_tac_model_text


def test_parse_z3_sat_output_status_and_model_body() -> None:
    out = parse_z3_sat_output(
        "sat\n(model\n  (define-fun x () Int 7)\n  (define-fun b () Bool false)\n)\n"
    )
    assert out.status == "sat"
    assert out.model_text.startswith("(model")
    assert out.unsat_core_text == ""


def test_parse_z3_sat_output_unsat_core_mode() -> None:
    out = parse_z3_sat_output("unsat\n(TAC_1 TAC_2)\n", unsat_core=True)
    assert out.status == "unsat"
    assert out.model_text == ""
    assert out.unsat_core_text == "(TAC_1 TAC_2)"


def test_z3_model_to_tac_model_text_basic() -> None:
    model = """(model
  (define-fun x () Int 7)
  (define-fun b () Bool false)
  (define-fun y () Int (- 10))
)"""
    txt, warnings = z3_model_to_tac_model_text(
        model,
        symbol_sort={
            "x": "bv256",
            "b": "bool",
            "y": "int",
        },
    )
    assert "TAC model begin" in txt
    assert "x:bv256 --> 7" in txt
    assert "b:bool --> false" in txt
    assert "y:int --> -10" in txt
    assert warnings == []


def test_z3_model_to_tac_model_text_accepts_bare_define_list() -> None:
    model = """(
  (define-fun x () Int 7)
  (define-fun b () Bool false)
)"""
    txt, warnings = z3_model_to_tac_model_text(
        model,
        symbol_sort={
            "x": "bv256",
            "b": "bool",
        },
    )
    assert "x:bv256 --> 7" in txt
    assert "b:bool --> false" in txt
    assert warnings == []

