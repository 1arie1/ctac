"""Unit + lemma tests for the neg-s128 recombination pass."""

from __future__ import annotations

import shutil
import subprocess

import pytest

from ctac.ast.nodes import ApplyExpr, AssignExpCmd, ConstExpr, SymbolRef
from ctac.parse import parse_string
from ctac.rewrite.neg_s128_recombine import rewrite_neg_s128_recombine

_TWO64 = "0x10000000000000000"
_H64 = "0x8000000000000000"
_U128MAX = "0xffffffffffffffffffffffffffffffff"


def _wrap(body: str, *, syms: str) -> str:
    return f"""TACSymbolTable {{
\tUserDefined {{
\t}}
\tBuiltinFunctions {{
\t\tsafe_math_narrow_bv256:JSON{{"#class":"vc.data.TACBuiltInFunction.SafeMathNarrow","returnSort":{{"#class":"tac.Tag.Bit256"}}}}
\t\twrap_twos_complement_256:JSON{{"#class":"vc.data.TACBuiltInFunction.TwosComplementWrapping","returnSort":{{"#class":"tac.Tag.Bit256"}}}}
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


_SYMS = (
    "X:bv256\n\tLO:bv256\n\tHI:bv256\n\tN1:bv256\n\tY:bv256\n\tIH:int"
    "\n\tIL:int\n\tGH:bv256\n\tGL:bv256\n\tR:bv256\n\tTBZ:bool\n\tTBC:bool"
    "\n\tTBH:bool\n\tTBC2:bool\n\tTBL:bool"
)


def _chain_body(*, bounded: bool) -> str:
    bound = f"\t\tAssumeExpCmd Le(X {_U128MAX})\n" if bounded else ""
    return (
        "\tBlock e Succ [] {\n"
        "\t\tAssignHavocCmd X\n"
        + bound
        + f"\t\tAssignExpCmd LO Mod(X {_TWO64})\n"
        + f"\t\tAssignExpCmd HI Div(X {_TWO64})\n"
        + "\t\tAssignExpCmd TBZ Eq(LO 0x0)\n"
        + "\t\tAssignExpCmd N1 Apply(safe_math_narrow_bv256:bif Ite(TBZ HI IntAdd(HI 0x1(int))))\n"
        + f"\t\tAssignExpCmd Y Mod(N1 {_TWO64})\n"
        + f"\t\tAssignExpCmd TBC Lt(Y {_H64})\n"
        + f"\t\tAssignExpCmd IH IntMul(0x-1(int) Ite(TBC Y IntSub(Y {_TWO64}(int))))\n"
        + f"\t\tAssignExpCmd TBH Eq(Y {_H64})\n"
        + "\t\tAssignExpCmd GH Ite(TBH N1 Apply(wrap_twos_complement_256:bif IH))\n"
        + f"\t\tAssignExpCmd TBC2 Lt(LO {_H64})\n"
        + f"\t\tAssignExpCmd IL IntMul(0x-1(int) Ite(TBC2 LO IntSub(LO {_TWO64}(int))))\n"
        + f"\t\tAssignExpCmd TBL Eq(LO {_H64})\n"
        + "\t\tAssignExpCmd GL Ite(TBL LO Apply(wrap_twos_complement_256:bif IL))\n"
        + "\t\tAssignExpCmd R Add(ShiftLeft(GH 0x40) GL)\n"
        + "\t}"
    )


def _def_of(program, lhs):
    for block in program.blocks:
        for cmd in block.commands:
            if isinstance(cmd, AssignExpCmd) and cmd.lhs == lhs:
                return cmd.rhs
    raise AssertionError(f"no def of {lhs!r}")


def test_recombine_fires_on_full_chain():
    tac = parse_string(_wrap(_chain_body(bounded=True), syms=_SYMS), path="<s>")
    res = rewrite_neg_s128_recombine(
        tac.program, symbol_sorts=tac.symbol_sorts
    )
    assert res.hits == 1
    names = [n for n, _ in res.fresh_symbols]
    assert names == ["H0", "Q0", "Q1"]
    assert _def_of(res.program, "H0") == ApplyExpr(
        "Ite",
        (
            ApplyExpr("Eq", (SymbolRef("X"), ConstExpr("0x0"))),
            ConstExpr("0x0"),
            ApplyExpr(
                "IntSub",
                (
                    ConstExpr(f"0x{1 << 128:x}(int)"),
                    SymbolRef("X"),
                ),
            ),
        ),
    )
    r_def = _def_of(res.program, "R")
    # 3-arm Ite: MIN-hi, MIN-lo, signed-limb composite.
    assert isinstance(r_def, ApplyExpr) and r_def.op == "Ite"
    assert r_def.args[0] == SymbolRef("TBH")
    inner = r_def.args[2]
    assert isinstance(inner, ApplyExpr) and inner.op == "Ite"
    assert inner.args[0] == SymbolRef("TBL")
    composite = inner.args[2]
    assert isinstance(composite, ApplyExpr) and composite.op == "Apply"
    assert composite.args[0] == SymbolRef("wrap_twos_complement_256:bif")


def test_recombine_abstains_without_x_bound():
    """X unbounded: the identity needs X < 2^128 — no fire."""
    tac = parse_string(
        _wrap(_chain_body(bounded=False), syms=_SYMS), path="<s>"
    )
    res = rewrite_neg_s128_recombine(
        tac.program, symbol_sorts=tac.symbol_sorts
    )
    assert res.hits == 0


@pytest.mark.skipif(shutil.which("z3") is None, reason="z3 not on PATH")
@pytest.mark.parametrize("w", [64, 128])
def test_neg_s128_recombine_identity_via_z3(w):
    """The full-domain emit identity at both supported widths: the
    original shifted-sum of gadgets equals the 3-arm form with the
    named neg value and signed-limb composite. No gates — the MIN
    arms carry the exceptional encodings."""
    H = 1 << (w - 1)
    F = 1 << w
    F2 = 1 << (2 * w)
    M = 1 << 256
    script = f"""(set-logic QF_NIA)
(declare-const x Int)
(define-fun lo () Int (mod x {F}))
(define-fun hi () Int (div x {F}))
(define-fun n1 () Int (ite (= lo 0) hi (+ hi 1)))
(define-fun y () Int (mod n1 {F}))
(define-fun fy () Int (ite (< y {H}) y (- y {F})))
(define-fun flo () Int (ite (< lo {H}) lo (- lo {F})))
(define-fun ghi () Int (ite (= y {H}) n1 (mod (- 0 fy) {M})))
(define-fun glo () Int (ite (= lo {H}) lo (mod (- 0 flo) {M})))
(define-fun orig () Int (mod (+ (mod (* ghi {F}) {M}) glo) {M}))
(define-fun hn () Int (ite (= x 0) 0 (- {F2} x)))
(define-fun ql () Int (mod hn {F}))
(define-fun qh () Int (div hn {F}))
(define-fun fql () Int (ite (< ql {H}) ql (- ql {F})))
(define-fun fqh () Int (ite (< qh {H}) qh (- qh {F})))
(define-fun comp () Int (mod (+ (* fqh {F}) fql) {M}))
(define-fun new () Int
  (ite (= y {H}) (mod (+ (mod (* n1 {F}) {M}) glo) {M})
  (ite (= lo {H}) (mod (+ (mod (* (mod (- 0 fy) {M}) {F}) {M}) lo) {M})
       comp)))
(assert (and (<= 0 x) (< x {F2})))
(assert (not (= orig new)))
(check-sat)
"""
    proc = subprocess.run(
        ["z3", "-smt2", "-T:30", "-in"],
        input=script, capture_output=True, text=True, timeout=60,
    )
    assert proc.stdout.strip() == "unsat", (w, proc.stdout)
