"""Soundness specs for the neg_s64 / sign-extension gadget family.

Each builder returns a self-contained SMT-LIB script whose expected
result is ``unsat`` (the rule's closed-form claim holds). The rules
live in ``src/ctac/rewrite/rules/sign_extend.py``; these scripts are
the z3-checked lemmas behind them, width-parametrized over the
supported signed widths.

Single source of truth: ``tests/test_rewrite_sign_extend.py`` imports
these builders so the CI z3 checks and ``ctac rw-valid``'s emitted
specs can never drift. The scripts are richer than the flat
``emit_flat_script`` envelope (multiple equivalences conjoined under a
domain assume, ite-defined intermediates), so they are built directly
and carry a single ``(assert (not (and ...)))`` / ``(assert (not (=
...)))`` soundness line.
"""

from __future__ import annotations

from ctac.rewrite.validation import ValidationCase


# --- gadget primitives, as SMT-LIB define-fun bodies over a width w ---
# from_s<w>(y) = ite(y < 2^(w-1), y, y - 2^w)               (signed decode)
# gadget(x, y) = ite(y == 2^(w-1), x, (-from_s<w>(y)) mod 2^256)  (neg gadget)


def neg_s64_zero_test(w: int) -> str:
    h, f, m = 1 << (w - 1), 1 << w, 1 << 256
    return f"""(set-logic QF_NIA)
(declare-const x Int)
(define-fun y () Int (mod x {f}))
(define-fun fs () Int (ite (< y {h}) y (- y {f})))
(define-fun wv () Int (mod (- 0 fs) {m}))
(define-fun lhs () Int (ite (= y {h}) x wv))
(assert (and (<= 0 x) (< x {m})))
(assert (not (= (= lhs 0) (= y 0))))
(check-sat)
"""


def wrap_compare_lift() -> str:
    m, c = 1 << 256, 10
    return f"""(set-logic QF_NIA)
(declare-const v Int)
(define-fun wv () Int (mod v {m}))
(assert (and (> v (- {c} {m})) (< v {m})))
(assert (not (and
  (= (= wv {c}) (= v {c}))
  (= (< wv {c}) (and (<= 0 v) (< v {c})))
  (= (<= wv {c}) (and (<= 0 v) (<= v {c})))
  (= (> wv {c}) (or (> v {c}) (< v 0)))
  (= (>= wv {c}) (or (>= v {c}) (< v 0))))))
(check-sat)
"""


def neg_s64_consumers(w: int) -> str:
    h, f, t255, m = 1 << (w - 1), 1 << w, 1 << 255, 1 << 256
    return f"""(set-logic QF_NIA)
(declare-const x Int)
(define-fun y () Int (mod x {f}))
(define-fun fs () Int (ite (< y {h}) y (- y {f})))
(define-fun wv () Int (mod (- 0 fs) {m}))
(define-fun n () Int (ite (= y {h}) x wv))
(assert (and (<= 0 x) (< x {t255})))
(assert (not (and
  (= (mod n {f}) (ite (= y 0) 0 (- {f} y)))
  (= (>= n {t255}) (and (< 0 y) (< y {h}))))))
(check-sat)
"""


def neg_s64_carry_and_double(w: int) -> str:
    h, f, m = 1 << (w - 1), 1 << w, 1 << 256
    se = m - f
    return f"""(set-logic QF_NIA)
(declare-const L Int)
(define-fun fs () Int (ite (< L {h}) L (- L {f})))
(define-fun n () Int (ite (= L {h}) L (mod (- 0 fs) {m})))
(define-fun yp () Int (mod n {f}))
(define-fun f2 () Int (ite (< yp {h}) yp (- yp {f})))
(define-fun n2 () Int (ite (= yp {h}) n (mod (- 0 f2) {m})))
(assert (and (<= 0 L) (< L {f})))
(assert (not (and
  (= (mod (+ n 1) {f}) (ite (<= L 1) (- 1 L) (- {f + 1} L)))
  (= n2 (ite (<= L {h}) L (+ L {se}))))))
(check-sat)
"""


def from_s64_zero_test(w: int) -> str:
    h, f = 1 << (w - 1), 1 << w
    return f"""(set-logic QF_NIA)
(declare-const y Int)
(define-fun fs () Int (ite (< y {h}) y (- y {f})))
(assert (and (<= 0 y) (< y {f})))
(assert (not (= (= fs 0) (= y 0))))
(check-sat)
"""


def neg_s64_double_carry(w: int) -> str:
    h, f, m = 1 << (w - 1), 1 << w, 1 << 256
    se = m - f
    return f"""(set-logic QF_NIA)
(declare-const x1 Int)
(declare-const g Int)
(assert (and (<= 0 x1) (< x1 {f})))
(assert (or (= g 0) (= g 1)))
(define-fun y1 () Int (mod x1 {f}))
(define-fun f1 () Int (ite (< y1 {h}) y1 (- y1 {f})))
(define-fun n1 () Int (ite (= y1 {h}) x1 (mod (- 0 f1) {m})))
(define-fun x2 () Int (mod (+ n1 g) {m}))
(define-fun y2 () Int (mod x2 {f}))
(define-fun f2 () Int (ite (< y2 {h}) y2 (- y2 {f})))
(define-fun r () Int (ite (= y2 {h}) x2 (mod (- 0 f2) {m})))
(define-fun z () Int (mod (- 0 y2) {f}))
(assert (not (= r (ite (<= z {h}) z (+ z {se})))))
(check-sat)
"""


def sign_ext_consumers(w: int) -> str:
    h, f, t255 = 1 << (w - 1), 1 << w, 1 << 255
    se = (1 << 256) - f
    c_low = f // 10100
    c_mid = f + 1
    f_minus_c_low = f - c_low
    return f"""(set-logic QF_NIA)
(declare-const z Int)
(declare-const y Int)
(assert (and (<= 0 z) (< z {f})))
(assert (and (<= 0 y) (< y {f})))
(define-fun v () Int (ite (<= z {h}) z (+ z {se})))
(define-fun wv () Int
  (ite (= y 0) 0
    (ite (>= y {h}) (- {f} y) (+ (- {f} y) {se}))))
(assert (not (and
  (= (>= v {t255}) (> z {h}))
  (= (<= v {c_low}) (<= z {c_low}))
  (= (<= v {c_mid}) (and (<= z {h}) (<= z {c_mid})))
  (= (>= v {c_mid}) (> z {h}))
  (= (>= wv {t255}) (and (< 0 y) (< y {h})))
  (= (<= wv {c_low}) (or (= y 0) (>= y {f_minus_c_low})))
  (= (<= wv {c_mid}) (or (= y 0) (>= y {h})))
  (= (= wv 5) (= y {f - 5})))))
(check-sat)
"""


def mod_div_pin() -> str:
    return """(set-logic QF_NIA)
(declare-const X Int)
(declare-const m Int)
(declare-const q Int)
(declare-const r Int)
(assert (> m 0))
(assert (and (<= 0 r) (< r m)))
(assert (not (= (and (= (mod X m) r) (= (div X m) q))
                (= X (+ (* q m) r)))))
(check-sat)
"""


def carry_chunk_cancel(w: int) -> str:
    f = 1 << w
    return f"""(set-logic QF_NIA)
(declare-const base Int)
(declare-const t Int)
(assert (and (<= 0 base) (< base {f})))
(assert (or (= t 0) (= t 1)))
(define-fun y2 () Int (mod (+ base t) {f}))
(define-fun pc () Int (ite (= y2 0) 0 (- {f} y2)))
(define-fun cc () Int (ite (<= y2 1) (- 1 y2) (- {f + 1} y2)))
(assert (not (= (ite (= t 0) pc cc)
                (ite (= base 0) 0 (- {f} base)))))
(check-sat)
"""


def borrow_sum_composed_double(w: int) -> str:
    h, f, m = 1 << (w - 1), 1 << w, 1 << 256
    se = m - f
    return f"""(set-logic QF_NIA)
(declare-const base Int)
(declare-const t Int)
(assert (and (<= 0 base) (< base {f})))
(assert (or (= t 0) (= t 1)))
(define-fun C () Int (+ base t))
(define-fun y2 () Int (mod C {f}))
(define-fun fs () Int (ite (< y2 {h}) y2 (- y2 {f})))
(define-fun n1 () Int (ite (= y2 {h}) C (mod (- 0 fs) {m})))
(define-fun xp () Int (mod (+ n1 t) {m}))
(define-fun yo () Int (mod xp {f}))
(define-fun fs2 () Int (ite (< yo {h}) yo (- yo {f})))
(define-fun r () Int (ite (= yo {h}) xp (mod (- 0 fs2) {m})))
(assert (not (= r (ite (<= base {h}) base (+ base {se})))))
(check-sat)
"""


def neg_s64_plus_one(w: int) -> str:
    """Both +1 lemmas (wrap-to-zero and the Le band) under one (not
    (or ...)). Two const probes; the MIN-arm probe is unreachable at
    w == 256 (needs c-1 >= 2^255 and c <= 2^256-2^255)."""
    h, f, m = 1 << (w - 1), 1 << w, 1 << 256
    cs = (10, f + 1) if w < 256 else (10, h)
    claims: list[str] = []
    for c in cs:
        k = max(h + 1, f + 1 - c)
        band = f"(or (<= y 1) (>= y {k})"
        if c - 1 >= h:
            band += f" (and (= y {h}) (<= x {c - 1}))"
        band += ")"
        claims.append("(not (= (= v 0) (= y 1)))")
        claims.append(f"(not (= (<= v {c}) {band}))")
    return f"""(set-logic QF_NIA)
(declare-const x Int)
(define-fun y () Int (mod x {f}))
(define-fun fs () Int (ite (< y {h}) y (- y {f})))
(define-fun g () Int (ite (= y {h}) x (mod (- 0 fs) {m})))
(define-fun v () Int (mod (+ g 1) {m}))
(assert (and (<= 0 x) (< x {m})))
(assert (or {' '.join(claims)}))
(check-sat)
"""


def neg_from_s_band(w: int) -> str:
    """The Int-domain negated-chunk band table (5 ops x const grid)."""
    h, f, m = 1 << (w - 1), 1 << w, 1 << 256

    def le_band(c: int) -> str:
        if c >= h:
            return "true"
        if c == 0:
            return f"(< y {h})"
        if c > 0:
            return f"(or (< y {h}) (>= y {f - c}))"
        if -c >= h:
            return "false"
        return f"(and (>= y {-c}) (< y {h}))"

    def ge_band(c: int) -> str:
        if c <= 0:
            if -c >= h - 1:
                return "true"
            first = "(= y 0)" if c == 0 else f"(<= y {-c})"
            return f"(or {first} (>= y {h}))"
        if f - c < h:
            return "false"
        return f"(and (>= y {h}) (<= y {f - c}))"

    def eq_band(c: int) -> str:
        if c == 0:
            return "(= y 0)"
        if 0 < c <= h:
            return f"(= y {f - c})"
        if -(h - 1) <= c < 0:
            return f"(= y {-c})"
        return "false"

    cs = [-f, -(h - 1), -(h - 2), -2, -1, 0, 1, 2, 10,
          h - 2, h - 1, h, h + 1, f - 1, f, f + 1]
    claims: list[str] = []
    for c in cs:
        claims.append(f"(= (<= v {c}) {le_band(c)})")
        claims.append(f"(= (< v {c}) {le_band(c - 1)})")
        claims.append(f"(= (>= v {c}) {ge_band(c)})")
        claims.append(f"(= (> v {c}) {ge_band(c + 1)})")
        claims.append(f"(= (= v {c}) {eq_band(c)})")
    return f"""(set-logic QF_NIA)
(declare-const x Int)
(define-fun y () Int (mod x {f}))
(define-fun fs () Int (ite (< y {h}) y (- y {f})))
(define-fun v () Int (- 0 fs))
(assert (and (<= 0 x) (< x {m})))
(assert (not (and {' '.join(claims)})))
(check-sat)
"""


def neg_chunk_band(w: int) -> str:
    """The materialized negation-chunk band table + the div-guard
    equivalence and the pre-R4 sign-test entry."""
    h, f, m = 1 << (w - 1), 1 << w, 1 << 256

    def le_band(c: int) -> str:
        if c < 0:
            return "false"
        if c >= f - 1:
            return "true"
        if c == 0:
            return "(= y 0)"
        return f"(or (= y 0) (>= y {f - c}))"

    def ge_band(c: int) -> str:
        if c <= 0:
            return "true"
        if c > f - 1:
            return "false"
        return f"(and (>= y 1) (<= y {f - c}))"

    cs = [-1, 0, 1, 2, 10, h - 1, h, h + 1, f - 2, f - 1, f, f + 1]
    claims = [f"(= (< x {f}) (= (div x {f}) 0))"]
    for c in cs:
        claims.append(f"(= (<= v {c}) {le_band(c)})")
        claims.append(f"(= (< v {c}) {le_band(c - 1)})")
        claims.append(f"(= (>= v {c}) {ge_band(c)})")
        claims.append(f"(= (> v {c}) {ge_band(c + 1)})")
    for k in (1, 10, h, f):
        claims.append(f"(= (= (div v {k}) 0) {le_band(k - 1)})")
    return f"""(set-logic QF_NIA)
(declare-const x Int)
(define-fun y () Int (mod x {f}))
(define-fun v () Int (ite (= y 0) 0 (- {f} y)))
(assert (and (<= 0 x) (< x {m})))
(assert (not (and {' '.join(claims)})))
(check-sat)
"""


def _vc(name: str, case: str, desc: str, smt2: str) -> ValidationCase:
    return ValidationCase(name=name, case=case, description=desc, smt2_text=smt2)


def _widths(builder, name: str, desc: str, widths: tuple[int, ...]) -> tuple[ValidationCase, ...]:
    return tuple(
        _vc(name, f"w{w}", f"{desc} (w={w}).", builder(w)) for w in widths
    )


_W3 = (64, 128, 256)
_W2 = (64, 128)

SIGN_EXTEND_CASES: tuple[ValidationCase, ...] = (
    _widths(neg_s64_zero_test, "NegS64ZeroTest",
            "Eq(gadget(x, y), 0) == Eq(y, 0), y = x mod 2^w", _W3)
    + (_vc("WrapCompareLift", "",
           "Cmp(wrap_256(v), c) lifts to the int-domain predicate on v "
           "for v in (c - 2^256, 2^256); Lt/Le/Gt/Ge/Eq at c=10.",
           wrap_compare_lift()),)
    + _widths(neg_s64_consumers, "NegS64LowChunk",
              "Mod(gadget, 2^w) == negchunk(y) and sign-test band, "
              "shared by NegS64LowChunk + NegS64SignTest", _W3)
    + _widths(neg_s64_carry_and_double, "NegS64Double",
              "carry chunk Mod(n+1, 2^w) form + gadget-of-gadget = "
              "w->256 sign extension (x == chunk regime)", _W2)
    + _widths(from_s64_zero_test, "FromS64ZeroTest",
              "Eq(from_s<w>(y), 0) == Eq(y, 0)", _W3)
    + _widths(neg_s64_double_carry, "NegS64Double",
              "double gadget over the un-borrow carry sum == "
              "signext((-y2) mod 2^w), carry in {0,1}", _W2)
    + _widths(sign_ext_consumers, "SignExtCmpLift",
              "sign-ext value band predicates over z (plain) and y "
              "(negchunk), shared by SignExtSignTest + SignExtCmpLift", _W2)
    + (_vc("ModDivPin", "",
           "(X mod m == r) and (X div m == q)  <=>  X == q*m + r, "
           "m > 0, 0 <= r < m (Euclidean bijection, no sign gate).",
           mod_div_pin()),)
    + _widths(carry_chunk_cancel, "CarryChunkCancel",
              "chunk of the borrow-sum (carry-select over t) == "
              "plain_chunk(base); borrow/un-borrow annihilate", _W2)
    + _widths(borrow_sum_composed_double, "NegS64Double",
              "borrow-sum composed double emit == signext(base)", _W2)
    + _widths(neg_s64_plus_one, "NegS64PlusOneZeroTest",
              "Eq(gadget+1, 0) == Eq(y, 1) and Le(gadget+1, c) band "
              "(shared by NegS64PlusOneZeroTest + NegS64PlusOneCmpLift)", _W3)
    + _widths(neg_from_s_band, "NegFromSCmpLift",
              "Cmp(-from_s<w>(y), c) band table (5 ops x const grid)", _W3)
    + _widths(neg_chunk_band, "NegChunkCmpLift",
              "Cmp(negchunk(y), c) band table + div-guard equivalence "
              "+ pre-R4 Eq(Div(negchunk, k), 0) sign-test", _W3)
    # Alias cases: rules whose lemma is bundled in a sibling's script
    # above get their own manifest entry (same script) so `missing`
    # doesn't falsely list them as unverified.
    + _widths(neg_s64_consumers, "NegS64SignTest",
              "sign-test band (shared script with NegS64LowChunk)", _W3)
    + _widths(sign_ext_consumers, "SignExtSignTest",
              "sign-ext sign-test band (shared with SignExtCmpLift)", _W2)
    + _widths(neg_s64_plus_one, "NegS64PlusOneCmpLift",
              "Le(gadget+1, c) band (shared with NegS64PlusOneZeroTest)", _W3)
)
