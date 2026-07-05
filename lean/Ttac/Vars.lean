import Ttac.Eval

/-!
# Variable inventories and congruence

One collector over `(sort, register)` pairs, a derived per-sort view
for the checker, the guard collector, and the congruence lemma:
evaluation depends only on an expression's variables. The operator
cases (`un`/`bin`/`tern`) are operator-independent — a new operator
never touches this file.
-/

namespace Ttac

namespace Exp

/-- Every register the expression reads, as `(sort, index)` pairs. -/
def vars : {t : Ty} → Exp t → List (Ty × Nat)
  | _, .litI _ | _, .litB _ | _, .blk _ => []
  | _, .var t x => [(t, x)]
  | _, .un _ e => e.vars
  | _, .bin _ l r => l.vars ++ r.vars
  | _, .tern _ e₁ e₂ e₃ => e₁.vars ++ e₂.vars ++ e₃.vars
  | _, .ite c th el => c.vars ++ th.vars ++ el.vars

/-- The registers of one sort the expression reads. -/
def varsAt (u : Ty) {t : Ty} (e : Exp t) : List Nat :=
  e.vars.filterMap fun p => if p.1 = u then some p.2 else none

/-- Block-guard atoms the expression reads (`blks` is a separate state
component, so guards get their own collector). -/
def blkVars : {t : Ty} → Exp t → List Nat
  | _, .blk b => [b]
  | _, .litI _ | _, .litB _ | _, .var _ _ => []
  | _, .un _ e => e.blkVars
  | _, .bin _ l r => l.blkVars ++ r.blkVars
  | _, .tern _ e₁ e₂ e₃ => e₁.blkVars ++ e₂.blkVars ++ e₃.blkVars
  | _, .ite c th el => c.blkVars ++ th.blkVars ++ el.blkVars

theorem mem_varsAt {u : Ty} {t : Ty} {e : Exp t} {x : Nat} :
    x ∈ e.varsAt u ↔ (u, x) ∈ e.vars := by
  simp only [varsAt, List.mem_filterMap]
  constructor
  · rintro ⟨⟨s, y⟩, hp, hif⟩
    by_cases h : s = u
    · subst h
      rw [if_pos rfl] at hif
      obtain rfl := Option.some.inj hif
      exact hp
    · rw [if_neg h] at hif
      cases hif
  · intro h
    exact ⟨(u, x), h, by rw [if_pos rfl]⟩

end Exp

/-! ## Congruence -/

theorem eval_congr {s s' : State} : {t : Ty} → (e : Exp t) →
    (∀ p ∈ e.vars, s.regs p.1 p.2 = s'.regs p.1 p.2) →
    (∀ q ∈ e.blkVars, s.blks q = s'.blks q) →
    e.eval s = e.eval s'
  | _, .litI _, _, _ => rfl
  | _, .litB _, _, _ => rfl
  | _, .var t x, hv, _ => hv (t, x) (by simp [Exp.vars])
  | _, .blk b, _, hk => hk b (by simp [Exp.blkVars])
  | _, .un op e, hv, hk => by
      simp only [Exp.eval]
      rw [eval_congr e (fun p hp => hv p (by simp [Exp.vars, hp]))
            (fun q hq => hk q (by simp [Exp.blkVars, hq]))]
  | _, .bin op l r, hv, hk => by
      simp only [Exp.eval]
      rw [eval_congr l (fun p hp => hv p (by simp [Exp.vars, hp]))
            (fun q hq => hk q (by simp [Exp.blkVars, hq])),
          eval_congr r (fun p hp => hv p (by simp [Exp.vars, hp]))
            (fun q hq => hk q (by simp [Exp.blkVars, hq]))]
  | _, .tern op e₁ e₂ e₃, hv, hk => by
      simp only [Exp.eval]
      rw [eval_congr e₁ (fun p hp => hv p (by simp [Exp.vars, hp]))
            (fun q hq => hk q (by simp [Exp.blkVars, hq])),
          eval_congr e₂ (fun p hp => hv p (by simp [Exp.vars, hp]))
            (fun q hq => hk q (by simp [Exp.blkVars, hq])),
          eval_congr e₃ (fun p hp => hv p (by simp [Exp.vars, hp]))
            (fun q hq => hk q (by simp [Exp.blkVars, hq]))]
  | _, .ite c th el, hv, hk => by
      simp only [Exp.eval]
      rw [eval_congr c (fun p hp => hv p (by simp [Exp.vars, hp]))
            (fun q hq => hk q (by simp [Exp.blkVars, hq])),
          eval_congr th (fun p hp => hv p (by simp [Exp.vars, hp]))
            (fun q hq => hk q (by simp [Exp.blkVars, hq])),
          eval_congr el (fun p hp => hv p (by simp [Exp.vars, hp]))
            (fun q hq => hk q (by simp [Exp.blkVars, hq]))]

end Ttac
