from __future__ import annotations

from pathlib import Path

from ctac.eval import parse_model_text, parse_tac_model_path, parse_tac_model_text


def test_parse_tac_model_text_scalars() -> None:
    text = """
prefix
-------- TAC model begin ------------
  R1:bv256  -->  0x20
  I7:int    -->  42
  B3:bool   -->  true
  from_skey:ghostmap((uninterp) skey->bv256)  --> {[x:bv256] -> x:bv256}
-------- TAC model end --------------
suffix
"""
    res = parse_tac_model_text(text)
    assert res.values["R1"].kind == "bv"
    assert int(res.values["R1"].data) == 0x20
    assert res.values["I7"].kind == "int"
    assert int(res.values["I7"].data) == 42
    assert res.values["B3"].kind == "bool"
    assert bool(res.values["B3"].data) is True
    assert "from_skey" not in res.values


def test_parse_tac_model_path_real_report() -> None:
    report = Path("examples/EmvOutput1/Reports/ctpp_liquidity_solvency_operate_borrow-Assertions.txt")
    res = parse_tac_model_path(report)
    assert "R0" in res.values
    assert "I1001" in res.values
    assert "ReachabilityCertora0_0_0_0_0_0" in res.values


def test_parse_model_text_smt_with_sat_prefix() -> None:
    text = """sat
(model
  (define-fun R1 () Int 32)
  (define-fun B3 () Bool true)
  (define-fun R2 () (_ BitVec 256) #x20)
)
"""
    res = parse_model_text(text)
    assert res.source_format == "smt"
    assert res.status == "sat"
    assert res.values["R1"].kind == "int"
    assert int(res.values["R1"].data) == 32
    assert res.values["B3"].kind == "bool"
    assert bool(res.values["B3"].data) is True
    assert res.values["R2"].kind == "bv"
    assert int(res.values["R2"].data) == 0x20


def test_parse_model_text_smt_unknown_no_model() -> None:
    res = parse_model_text("unknown\n")
    assert res.source_format == "smt"
    assert res.status == "unknown"
    assert res.values == {}


def test_parse_model_text_skips_z3_stats_block() -> None:
    """``z3 -st`` appends a ``(:keyword value …)`` statistics block
    after the model; the parser should drop it instead of erroring."""
    text = """sat
(
  (define-fun R1 () Int 32)
  (define-fun B3 () Bool true)
)
(:added-eqs                       64756
 :nlsat-conflicts                 12400
 :time                            6.12
 :total-time                      6.04)
"""
    res = parse_model_text(text)
    assert res.status == "sat"
    assert int(res.values["R1"].data) == 32
    assert bool(res.values["B3"].data) is True


def test_parse_model_text_skips_multiple_stats_blocks() -> None:
    """Multiple ``(:keyword …)`` blocks (e.g. across check-sat calls)
    are all dropped."""
    text = """sat
(
  (define-fun R1 () Int 7)
)
(:added-eqs 12)
(:time 0.5 :total-time 0.6)
"""
    res = parse_model_text(text)
    assert int(res.values["R1"].data) == 7


def test_parse_model_text_rejects_non_stats_trailing_sexpr() -> None:
    """A trailing sexpr that doesn't start with ``:keyword`` is still
    an error — silently dropping it would mask malformed models."""
    text = """sat
(
  (define-fun R1 () Int 1)
)
((this-is-not-stats foo bar))
"""
    try:
        parse_model_text(text)
    except ValueError as e:
        assert "trailing tokens" in str(e)
    else:
        raise AssertionError("expected ValueError")
