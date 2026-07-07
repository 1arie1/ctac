import Ttac.VcDenot

/-!
# The weakening table: admission by "weak enough", not byte-equality

`checkVC` admits a constraint only if it is byte-identical to a member
of `expected P` — so every constant fold the Python encoder performs
must be mirrored exactly in trusted Lean, and any vcgen simplification
drift breaks the checker. This module replaces that admission test with
a *table judgment*: a candidate constraint is admissible if some anchor
the program's steps justify **weakens to** it.

Two tables, two growth axes:

* **Anchor table** — the formulas each instruction's step directly
  justifies. This is the existing per-instruction machinery
  (`Cmd.factB` → `cmdConstraints`, `cfgConstraintsFor`, `objective`),
  whose truth at every failing denotational run is `denot_sat`.
  *Adding a command = a `factB` row + its `denot` case.*
* **Closure table** (`weakensFrom`) — command-independent syntactic
  weakening steps: reflexivity, the trivial constraint, or-introduction,
  hypothesis-introduction. The sole proof obligation per row is its
  case in `weakensFrom_sound`: *if a formula is accepted as a
  weakening, it is a weakening.* *Adding a vcgen simplification = a row
  here.* Complex simplifications that a single syntactic row cannot
  recognize will carry witnesses (rewrite chains, replayed row by row)
  in the VC syntax — a future extension of the same table.

Soundness is admission-agnostic: `checkVCW` accepts ⇒ every candidate
is a weakening of a true anchor ⇒ `DenotSound` ⇒
`safe_denot_of_denotSound`. `checkVCW` strictly generalizes `checkVC`
(membership is the reflexivity row).
-/

namespace Ttac

namespace Vc

/-- The closure table: `weakensFrom a c` accepts `c` as a syntactic
weakening of the anchor `a`. One Bool row per shape; each row's
obligation is its case in `weakensFrom_sound`. -/
def weakensFrom (a c : BExp) : Bool :=
  decide (c = a)
    || decide (c = .litB true)
    || (match c with
        | .bin .or l r => decide (l = a) || decide (r = a)
        | .bin .imp _ r => decide (r = a)
        | _ => false)

/-- The table's contract: an accepted formula is a weakening — true
whenever its anchor is. One case per row. -/
theorem weakensFrom_sound {a c : BExp} {w : State}
    (h : weakensFrom a c = true) (ha : a.eval w = true) :
    c.eval w = true := by
  unfold weakensFrom at h
  rw [Bool.or_eq_true, Bool.or_eq_true] at h
  rcases h with (h | h) | h
  · obtain rfl := of_decide_eq_true h
    exact ha
  · obtain rfl := of_decide_eq_true h
    rfl
  · split at h
    · rw [Bool.or_eq_true] at h
      rcases h with h | h
      · obtain rfl := of_decide_eq_true h
        simp [Exp.eval, BinOp.denote, ha]
      · obtain rfl := of_decide_eq_true h
        simp [Exp.eval, BinOp.denote, ha]
    · obtain rfl := of_decide_eq_true h
      simp [Exp.eval, BinOp.denote, ha]
    · cases h

end Vc

/-- The weakening-table checker: every constraint must weaken from some
anchor. Map definitions are definitional equalities (no boolean
weakening applies); they keep the membership test. -/
def checkVCW (P : Program) (vc : Vc.VC) : Bool :=
  wellFormed P
    && vc.constraints.all
        (fun c => (Vc.expected P).any (fun a => Vc.weakensFrom a c))
    && vc.mapDefs.all (fun md => decide (md ∈ Vc.expectedMapDefs P))

/-- An accepted VC is weak enough: each candidate weakens from an
anchor, and every anchor is true at every failing denotational run
(`denot_sat`). -/
theorem denotSound_of_checkVCW {P : Program} {vc : Vc.VC}
    (hchk : checkVCW P vc = true) : DenotSound P vc := by
  rw [checkVCW, Bool.and_eq_true, Bool.and_eq_true] at hchk
  obtain ⟨⟨hwf, hmem⟩, hmdefs⟩ := hchk
  rw [wellFormed] at hwf
  simp only [Bool.and_eq_true] at hwf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hone, hssa⟩, hfwd⟩, hphi⟩, hamo⟩, hentry⟩, hgf⟩, -⟩, huse⟩ := hwf
  intro s0 hexit
  have hsat := denot_sat hone hssa hfwd hphi hamo hentry hgf huse hexit
  refine ⟨fun c hc => ?_, fun md hmd => hsat.2 md
    (of_decide_eq_true (List.all_eq_true.mp hmdefs md hmd))⟩
  obtain ⟨a, hamem, haw⟩ :=
    List.any_eq_true.mp (List.all_eq_true.mp hmem c hc)
  exact Vc.weakensFrom_sound haw (hsat.1 a hamem)

/-- The weakening-table `checkVC_safe`. -/
theorem checkVCW_safe_denot {P : Program} {vc : Vc.VC}
    (hchk : checkVCW P vc = true) (hunsat : Vc.Unsat vc) : Safe_denot P :=
  safe_denot_of_denotSound (denotSound_of_checkVCW hchk) hunsat

end Ttac
