import Ttac.Eval

/-!
# Tiny TAC deep embedding: small-step operational semantics

`Step P` is an inductive predicate over configurations. The relation is
the language's definition — the effect tables (`Cmd.def?`/`Cmd.factB`)
are characterized *about* it by lemmas in `VcTrace`, never used to
define it (a fact-based step would diverge from the reference
interpreter on ill-formed programs).

Design notes:

* One rule per command *kind*, sort-generic: `assign`/`havoc`/`phi`
  each write through `State.upd t`.
* Havoc rules take the chosen value as a constructor argument — that is
  the (only) source of nondeterminism.
* `assume` has a rule only when the condition evaluates to `true`. An
  execution at a false assume is *stuck*: it is pruned, i.e. vacuously
  safe. Stuck is deliberately distinct from `done`.
* Stuck-by-malformedness (dangling block index, missing phi arm, phi
  with no predecessor) is likewise vacuously safe. Soundness of `Safe`
  as a statement about the *source* program therefore relies on the
  generator rejecting those shapes up front.
* Phis execute sequentially, reading sources from the current state —
  matching the reference interpreter (`run.py`), not LLVM's parallel
  reading. The generator rejects the one shape where they differ (a
  phi source that is an earlier phi target in the same block).
* Terminator rules pin `pc = B.cmds.length` in the source
  configuration; empty blocks work by construction (`0 = cmds.length`).
-/

namespace Ttac

inductive Config : Type where
  | running (blk : Nat) (pc : Nat) (prev : Option Nat) (s : State)
  | done (s : State)
  | failed (s : State)

/-- Resolve a phi arm list against the predecessor block index. -/
def lookupArm (arms : PhiArms) (p : Nat) : Option Nat :=
  (arms.lookup p : Option Nat)

inductive Step (P : Program) : Config → Config → Prop where
  | assign {b pc prev s B t x e} :
      P.block? b = some B → B.cmds[pc]? = some (.assign t x e) →
      Step P (.running b pc prev s)
        (.running b (pc + 1) prev (s.upd t x (e.eval s)))
  | havoc {b pc prev s B t x} (v : t.denote) :
      P.block? b = some B → B.cmds[pc]? = some (.havoc t x) →
      Step P (.running b pc prev s) (.running b (pc + 1) prev (s.upd t x v))
  | phi {b pc p s B t x arms src} :
      P.block? b = some B → B.cmds[pc]? = some (.phi t x arms) →
      lookupArm arms p = some src →
      Step P (.running b pc (some p) s)
        (.running b (pc + 1) (some p) (s.upd t x (s.regs t src)))
  | assume {b pc prev s B φ} :
      P.block? b = some B → B.cmds[pc]? = some (.assume φ) →
      φ.eval s = true →
      Step P (.running b pc prev s) (.running b (pc + 1) prev s)
  | assertTrue {b pc prev s B c} :
      P.block? b = some B → B.cmds[pc]? = some (.assert c) →
      s.regs .bool c = true →
      Step P (.running b pc prev s) (.running b (pc + 1) prev s)
  | assertFalse {b pc prev s B c} :
      P.block? b = some B → B.cmds[pc]? = some (.assert c) →
      s.regs .bool c = false →
      Step P (.running b pc prev s) (.failed s)
  | halt {b prev s B} :
      P.block? b = some B → B.term = .halt →
      Step P (.running b B.cmds.length prev s) (.done s)
  | goto {b prev s B b'} :
      P.block? b = some B → B.term = .goto b' →
      Step P (.running b B.cmds.length prev s) (.running b' 0 (some b) s)
  | ifTrue {b prev s B c t e} :
      P.block? b = some B → B.term = .ifGoto c t e → s.regs .bool c = true →
      Step P (.running b B.cmds.length prev s) (.running t 0 (some b) s)
  | ifFalse {b prev s B c t e} :
      P.block? b = some B → B.term = .ifGoto c t e → s.regs .bool c = false →
      Step P (.running b B.cmds.length prev s) (.running e 0 (some b) s)

end Ttac
