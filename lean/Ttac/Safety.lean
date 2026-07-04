import Mathlib.Logic.Relation
import Ttac.Semantics

/-!
# Tiny TAC deep embedding: reachability and safety

`Unsafe` mirrors the VC orientation used throughout `docs/vc/`:
`Unsafe P` is the Lean twin of "the VC is satisfiable" (a failure
execution exists), so `Safe P` corresponds to UNSAT.

The initial state is *arbitrary* (universally quantified inside the
`∃ s`): under SSA with no use-before-def, no register is read before
its defining write, so the junk is dead — this is exactly
havoc-at-entry.
-/

namespace Ttac

/-- Multi-step execution: reflexive-transitive closure of `Step`. -/
def Steps (P : Program) : Config → Config → Prop :=
  Relation.ReflTransGen (Step P)

/-- Initial configuration: entry block, first command, no predecessor. -/
def Config.init (P : Program) (s : State) : Config :=
  .running P.entry 0 none s

namespace Program

def Unsafe (P : Program) : Prop :=
  ∃ s s', Steps P (Config.init P s) (.failed s')

def Safe (P : Program) : Prop := ¬P.Unsafe

theorem Safe.not_failed {P : Program} (h : P.Safe) {s s'} :
    ¬Steps P (Config.init P s) (.failed s') :=
  fun hs => h ⟨s, s', hs⟩

end Program

end Ttac
