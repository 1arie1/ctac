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
    """Multiple non-stats sexprs is an error (silently dropping would
    mask malformed models). The trailing list `((this-is-not-stats
    ...))` is a list-of-lists, not a stats block."""
    text = """sat
(
  (define-fun R1 () Int 1)
)
((this-is-not-stats foo bar))
"""
    try:
        parse_model_text(text)
    except ValueError as e:
        # Either "multiple non-stats" (new error) or "trailing tokens"
        # (legacy). Both indicate the same failure mode.
        msg = str(e)
        assert ('multiple non-stats' in msg
                  or 'trailing tokens' in msg), msg
    else:
        raise AssertionError("expected ValueError")


def test_parse_model_text_tolerates_leading_stats_block() -> None:
    """Some z3 builds emit `-st` stats BEFORE the model. The parser
    handles either position (or both)."""
    text = """sat
(:added-eqs 12345 :time 0.5 :total-time 0.5)
(
  (define-fun R1 () Int 7)
  (define-fun b1 () Bool true)
)
"""
    m = parse_model_text(text)
    assert m.values['R1'].kind == 'int'
    assert int(m.values['R1'].data) == 7
    assert m.values['b1'].kind == 'bool'
    assert bool(m.values['b1'].data) is True
