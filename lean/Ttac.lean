import Ttac.Ast
import Ttac.State
import Ttac.Eval
import Ttac.Vars
import Ttac.Semantics
import Ttac.Safety
import Ttac.Vc
import Ttac.VcCheck
import Ttac.VcLemmas
import Ttac.VcTrace
import Ttac.VcFacts
import Ttac.VcPrefix
import Ttac.VcCfgPath
import Ttac.VcDenot
import Ttac.VcWeaken
import Ttac.VcAdequacy
import Ttac.VcCoadequacy
import Ttac.Product

/-!
# Ttac: a verified checker development for `ttac` VCs

Reading order below is import order; each file's module docstring
carries its own map. The one-sentence architecture: the *denotational
semantics* (`denot`, a computable fold in which every block executes)
is the pivot — checkers prove VCs "weak enough" for it, adequacy ties
it to the operational semantics, and evaluation replays solver models
against it.

The headline theorems:

* `checkVCWAnn_safe` (`VcAdequacy`) — the production pipeline: a
  site-tagged annotated VC accepted by the weakening-table checker and
  UNSAT implies `Program.Safe`.
* `checkVC_safe_via_denot` (`VcAdequacy`) — the same for the flat
  membership checker `checkVC`.
* `not_safe_denot_of_seed` (`VcDenot`) — SAT certificates: a seed with
  `ReachesExit` (checked by `native_decide`) refutes `Safe_denot`.
* `unsafe_of_seed` (`VcCoadequacy`) — its operational upgrade: under
  `wellFormed` + `phiCoversOK` the seed exhibits a real failing
  execution, `P.Unsafe`.
* `safe_iff_safe_denot` (`VcCoadequacy`) — the complete picture: the
  operational and denotational safety notions coincide.
* `product_transfer` (`Product`) — rw-eq's certificate, verified: a
  safe idealized product program plus a safe rewrite implies the
  original is safe (`product_transfer_safe` is the operational form).

Layer map: `Ast`/`State`/`Eval`/`Vars` — the language and its
evaluation; `Semantics`/`Safety` — the operational small-step semantics
and `Program.Safe`; `Vc` — the VC syntax and the encoder's expected
constraints; `VcCheck` — the decidable checks (`wellFormed`, and the
`WellFormed` Prop bundle); `VcLemmas`/`VcTrace`/`VcFacts` — shared
bridges (`TakenPath`/`TraceFacts` live in `VcTrace`); `VcPrefix` — the
operational facts producer `forwardStructural`; `VcCfgPath` — the
dominance-free path lemmas; `VcDenot` — the denotational semantics,
`ReachesExit`, and Lemma B (`denot_sat`); `VcWeaken` — the
weakening/rewrite-table checkers (`checkVCW`, `checkVCWAnn`);
`VcAdequacy` — operational ⇒ denotational (the only dominance
consumer); `VcCoadequacy` — the converse, and the equivalence;
`Product` — the idealized rw-eq product and its safety transfer.
-/
