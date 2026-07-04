import Ttac
import TtacExamples.Diamond

/-!
# Golden reference: the diamond's VC passes `checkVC`

`vc` below is a hand transcription of the real `ttac vcgen` output for
`docs/vc/examples/safe_scalar_diamond.ttac` (bwd0 encoding), under the
`ttac vc-check` numbering: `blockOff = 2` (bool registers 0..1 are
program registers `c`, `ok`), block vars 2 = entry, 3 = pos, 4 = neg,
5 = join, 6 = BLK_EXIT.

This example pins the fold mirror in `Ttac.Vc` against the Python
encoder: if either side drifts, this file stops compiling. The Python
test suite pins the transpiler against the same lines.
-/

namespace TtacExamples.Diamond

open Ttac

def vcBlockOff : Nat := 2

def vc : List BExp := [
  -- (assert (= c (<= 0 x)))
  .eqB (.var 0) (.le (.lit 0) (.var 0)),
  -- (assert (=> BLK_pos (= y1 (+ x 1))))
  .imp (.var 3) (.eqI (.var 1) (.add (.var 0) (.lit 1))),
  -- (assert (=> BLK_neg (= y2 (- 0 x))))
  .imp (.var 4) (.eqI (.var 2) (.sub (.lit 0) (.var 0))),
  -- (assert (= y (ite BLK_pos y1 y2)))
  .eqI (.var 3) (.ite (.var 3) (.var 1) (.var 2)),
  -- (assert (or (not BLK_pos) (not BLK_neg)))
  .or (.not (.var 3)) (.not (.var 4)),
  -- (assert (=> BLK_join (= ok (<= 0 y))))
  .imp (.var 5) (.eqB (.var 1) (.le (.lit 0) (.var 3))),
  -- (assert (=> BLK_pos c))
  .imp (.var 3) (.var 0),
  -- (assert (=> BLK_neg (not c)))
  .imp (.var 4) (.not (.var 0)),
  -- (assert (=> BLK_join (or BLK_pos BLK_neg)))  [emitted twice]
  .imp (.var 5) (.or (.var 3) (.var 4)),
  .imp (.var 5) (.or (.var 3) (.var 4)),
  -- (assert (=> BLK_join (or (not BLK_pos) (not BLK_neg))))
  .imp (.var 5) (.or (.not (.var 3)) (.not (.var 4))),
  -- (assert (=> BLK_EXIT (and BLK_join (not ok))))
  .imp (.var 6) (.and (.var 5) (.not (.var 1))),
  -- (assert BLK_EXIT)
  .var 6]

theorem vc_ok : checkVC prog vcBlockOff vc = true := by native_decide

/-- The full verified chain: if the VC is unsatisfiable, the diamond is
safe under the small-step semantics. -/
theorem vc_implies_safe : Vc.Unsat vc → prog.Safe :=
  checkVC_safe vc_ok

/-- A tampered constraint (flipped comparison) must be rejected. -/
example :
    checkVC prog vcBlockOff
      [.imp (.var 5) (.eqB (.var 1) (.lt (.lit 0) (.var 3)))] = false := by
  native_decide

end TtacExamples.Diamond
