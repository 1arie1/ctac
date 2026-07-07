import Ttac
import TtacExamples.Diamond

/-!
# Golden reference: the diamond's annotated VC passes `checkVCWAnn`

The annotated VC (`Vc.AnnVC`) for the scalar diamond, in the shape the
untrusted transpiler emits: per block, its CFG constraints and its
per-command constraints, plus the objective and the (empty) map
definitions. Here the buckets are the encoder's own generators, so
`checkVCWAnn` accepting it confirms the weakening checker is not
vacuously over-strict (it accepts a real four-block program) and
computes under `native_decide` at real scale. The independent content
pin against `ttac vcgen` is `DiamondVc` (the flat form); the untrusted
Python annotator pins the annotated form the same way.
-/

namespace TtacExamples.Diamond

open Ttac

def annvc : Vc.AnnVC where
  perBlock := prog.blocks.zipIdx.map fun (B, b) =>
    { cfg := Vc.cfgConstraintsFor prog b
      cmds := B.cmds.map (Vc.cmdConstraints prog b) }
  objective := match Vc.assertSites prog with
    | [(aB, _, okReg)] => Vc.objective prog aB okReg
    | _ => []
  mapDefs := Vc.expectedMapDefs prog

theorem annvc_ok : checkVCWAnn prog annvc = true := by native_decide

/-- The verified chain: if the annotated VC is unsatisfiable, the diamond
is safe under the small-step semantics (via `checkVCWAnn_safe`). -/
theorem annvc_implies_safe : Vc.AnnVC.Unsat annvc → prog.Safe :=
  checkVCWAnn_safe annvc_ok

/-- A tampered annotation (a bogus constraint that weakens from no
anchor) must be rejected. (Dropping constraints is sound and accepted.) -/
example : checkVCWAnn prog { annvc with objective := [.blk 42] } = false := by
  native_decide

/-! ## A weakened annotation -/

/-- A weakened annotated VC: block 3's command bucket carries an
or-introduced variant of the `ok` fact — not a generator member, but a
weakening of one; admission consults only block 3's own anchors. -/
def annvcWeak : Vc.AnnVC :=
  { annvc with
      perBlock := annvc.perBlock.take 3 ++
        [{ cfg := Vc.cfgConstraintsFor prog 3
           cmds := [[
             -- (or (=> BLK_join (= ok (<= 0 y))) BLK_pos) — or-introduction
             .or (.imp (.blk 3)
                 (.eqB (.var .bool 1) (.le (.litI 0) (.var .int 3)))) (.blk 1)]] }] }

theorem annvcWeak_ok : checkVCWAnn prog annvcWeak = true := by
  native_decide

theorem annvcWeak_implies_safe : Vc.AnnVC.Unsat annvcWeak → prog.Safe :=
  checkVCWAnn_safe annvcWeak_ok

end TtacExamples.Diamond
