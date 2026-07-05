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

/-- A tampered annotation (objective dropped) must be rejected. -/
example : Vc.checkVCAnn prog { annvc with objective := [] } = false := by
  native_decide

end TtacExamples.Diamond
