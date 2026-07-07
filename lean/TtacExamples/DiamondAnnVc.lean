import Ttac
import TtacExamples.Diamond

/-!
# Golden reference: the diamond's annotated VC passes `checkVCAnn`

The annotated VC (`Vc.AnnVC`) for the scalar diamond, in the shape the
untrusted transpiler emits: per block, its CFG constraints and its
per-command constraints, plus the objective and the (empty) map
definitions. Here the buckets are the encoder's own generators, so
`checkVCAnn` accepting it confirms two things about the *forward* checker:
it is not vacuously over-strict (it accepts a real four-block program), and
it computes under `native_decide` at real scale. The independent
content pin against `ttac vcgen` is `DiamondVc` (the flat form); the
untrusted Python annotator will pin the annotated form the same way.
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

theorem annvc_ok : Vc.checkVCAnn prog annvc = true := by native_decide

/-- The forward verified chain: if the annotated VC is unsatisfiable, the
diamond is safe under the small-step semantics (via `checkVCAnn_safe`). -/
theorem annvc_implies_safe : Vc.AnnVC.Unsat annvc → prog.Safe :=
  checkVCAnn_safe annvc_ok

/-- A tampered annotation (a bogus constraint the encoder never emits) must be
rejected. (Dropping constraints is a sound subset and is accepted, as with the
flat `checkVC`.) -/
example : Vc.checkVCAnn prog { annvc with objective := [.blk 42] } = false := by
  native_decide

/-! ## The site-tagged weakening checker on the same golden -/

/-- `checkVCWAnn` accepts the untouched annotated golden (reflexivity). -/
theorem annvc_ok_weak : checkVCWAnn prog annvc = true := by native_decide

/-- A weakened annotated VC: block 3's command bucket carries an
or-introduced variant of the `ok` fact; `checkVCAnn`'s membership test
rejects it, the weakening table accepts it, with the same safety
conclusion — and admission consulted only block 3's own anchors. -/
def annvcWeak : Vc.AnnVC :=
  { annvc with
      perBlock := annvc.perBlock.take 3 ++
        [{ cfg := Vc.cfgConstraintsFor prog 3
           cmds := [[
             -- (or (=> BLK_join (= ok (<= 0 y))) BLK_pos) — or-introduction
             .or (.imp (.blk 3)
                 (.eqB (.var .bool 1) (.le (.litI 0) (.var .int 3)))) (.blk 1)]] }] }

example : Vc.checkVCAnn prog annvcWeak = false := by native_decide

theorem annvcWeak_ok : checkVCWAnn prog annvcWeak = true := by native_decide

theorem annvcWeak_implies_safe : Vc.AnnVC.Unsat annvcWeak → prog.Safe :=
  checkVCWAnn_safe annvcWeak_ok

end TtacExamples.Diamond
