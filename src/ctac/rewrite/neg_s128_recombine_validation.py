"""Soundness spec for the neg_s128 recombination rewrite
(``src/ctac/rewrite/neg_s128_recombine.py``).

The full-domain identity: the original shifted-sum of two
sign-extended negation gadgets equals the 3-arm form over a named
``HN = neg128(X)`` (negchunk-Ite spelling) with the signed-limb
composite in the clean arm. No gates — the gadget MIN arms carry the
exceptional encodings, so the identity holds for all ``X in
[0, 2^2w)``. Width-parametrized over w in {64, 128}.

Single source: ``tests/test_neg_s128_recombine.py`` imports this
builder.
"""

from __future__ import annotations

from ctac.rewrite.validation import ValidationCase


def neg_s128_recombine_identity(w: int) -> str:
    h, f, f2, m = 1 << (w - 1), 1 << w, 1 << (2 * w), 1 << 256
    return f"""(set-logic QF_NIA)
(declare-const x Int)
(define-fun lo () Int (mod x {f}))
(define-fun hi () Int (div x {f}))
(define-fun n1 () Int (ite (= lo 0) hi (+ hi 1)))
(define-fun y () Int (mod n1 {f}))
(define-fun fy () Int (ite (< y {h}) y (- y {f})))
(define-fun flo () Int (ite (< lo {h}) lo (- lo {f})))
(define-fun ghi () Int (ite (= y {h}) n1 (mod (- 0 fy) {m})))
(define-fun glo () Int (ite (= lo {h}) lo (mod (- 0 flo) {m})))
(define-fun orig () Int (mod (+ (mod (* ghi {f}) {m}) glo) {m}))
(define-fun hn () Int (ite (= x 0) 0 (- {f2} x)))
(define-fun ql () Int (mod hn {f}))
(define-fun qh () Int (div hn {f}))
(define-fun fql () Int (ite (< ql {h}) ql (- ql {f})))
(define-fun fqh () Int (ite (< qh {h}) qh (- qh {f})))
(define-fun comp () Int (mod (+ (* fqh {f}) fql) {m}))
(define-fun new () Int
  (ite (= y {h}) (mod (+ (mod (* n1 {f}) {m}) glo) {m})
  (ite (= lo {h}) (mod (+ (mod (* (mod (- 0 fy) {m}) {f}) {m}) lo) {m})
       comp)))
(assert (and (<= 0 x) (< x {f2})))
(assert (not (= orig new)))
(check-sat)
"""


NEG_S128_RECOMBINE_CASES: tuple[ValidationCase, ...] = tuple(
    ValidationCase(
        name="NegS128Recombine",
        case=f"w{w}",
        description=(
            "shifted-sum of two sign-extended negation gadgets == "
            "3-arm form over HN = neg128(X) with signed-limb composite "
            f"(full-domain, w={w})."
        ),
        smt2_text=neg_s128_recombine_identity(w),
    )
    for w in (64, 128)
)
