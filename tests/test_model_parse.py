from __future__ import annotations

from pathlib import Path

from ctac.eval import parse_tac_model_path, parse_tac_model_text


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
