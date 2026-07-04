import Ttac
import TtacExamples.Diamond

/-!
# Golden reference: the diamond's VC passes `checkVC`

`vc` below is a hand transcription of the real `ttac vcgen` output for
`docs/vc/examples/safe_scalar_diamond.ttac` (bwd0 encoding), under the
`ttac vc-check` numbering: `BLK_<label>` becomes the guard atom
`.blk <block index>` (entry = 0, pos = 1, neg = 2, join = 3) and
`BLK_EXIT` becomes `.blk 4`.

This example pins the fold mirror in `Ttac.Vc` against the Python
encoder: if either side drifts, this file stops compiling. The Python
test suite pins the transpiler against the same lines.
-/

namespace TtacExamples.Diamond

open Ttac

def vc : List BExp := [
  -- (assert (= c (<= 0 x)))
  .eqB (.var 0) (.le (.lit 0) (.var 0)),
  -- (assert (=> BLK_pos (= y1 (+ x 1))))
  .imp (.blk 1) (.eqI (.var 1) (.add (.var 0) (.lit 1))),
  -- (assert (=> BLK_neg (= y2 (- 0 x))))
  .imp (.blk 2) (.eqI (.var 2) (.sub (.lit 0) (.var 0))),
  -- (assert (= y (ite BLK_pos y1 y2)))
  .eqI (.var 3) (.ite (.blk 1) (.var 1) (.var 2)),
  -- (assert (or (not BLK_pos) (not BLK_neg)))
  .or (.not (.blk 1)) (.not (.blk 2)),
  -- (assert (=> BLK_join (= ok (<= 0 y))))
  .imp (.blk 3) (.eqB (.var 1) (.le (.lit 0) (.var 3))),
  -- (assert (=> BLK_pos c))
  .imp (.blk 1) (.var 0),
  -- (assert (=> BLK_neg (not c)))
  .imp (.blk 2) (.not (.var 0)),
  -- (assert (=> BLK_join (or BLK_pos BLK_neg)))  [emitted twice]
  .imp (.blk 3) (.or (.blk 1) (.blk 2)),
  .imp (.blk 3) (.or (.blk 1) (.blk 2)),
  -- (assert (=> BLK_join (or (not BLK_pos) (not BLK_neg))))
  .imp (.blk 3) (.or (.not (.blk 1)) (.not (.blk 2))),
  -- (assert (=> BLK_EXIT (and BLK_join (not ok))))
  .imp (.blk 4) (.and (.blk 3) (.not (.var 1))),
  -- (assert BLK_EXIT)
  .blk 4]

theorem vc_ok : checkVC prog vc = true := by native_decide

/-- The full verified chain: if the VC is unsatisfiable, the diamond is
safe under the small-step semantics. -/
theorem vc_implies_safe : Vc.Unsat vc → prog.Safe :=
  checkVC_safe vc_ok

/-- A tampered constraint (flipped comparison) must be rejected. -/
example :
    checkVC prog
      [.imp (.blk 3) (.eqB (.var 1) (.lt (.lit 0) (.var 3)))] = false := by
  native_decide

end TtacExamples.Diamond
