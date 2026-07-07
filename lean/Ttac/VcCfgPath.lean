import Ttac.VcPrefix

/-!
# CFG + guarded-fact constraints, satisfied by any path state

The bwd0 CFG constraints (`cfgConstraintsFor`) and the guarded command
facts (`factConstraints`) hold at **any** state `w` whose guard
component is the reachability valuation of a real forward path `V`
(`hblk : w.blks q = decide (q ∈ V)` for real blocks, edges taken at
`w`). The signatures take only the CFG side-conditions and the path
facts — no dominator table: against one concrete path state an edge
condition is simply true (`EdgeTaken.edge_cond`) and a command fact
simply holds (`CmdFact.factB_eval`); there is no quantified witness
class to freeze registers across. Both lemmas apply verbatim to the
denotational state `denot P s0` (`VcDenot`).
-/

namespace Ttac

open Vc

/-- **CFG constraints of one block, satisfied by any path state.**

Each constraint in `cfgConstraintsFor P S` holds at `w` when `w`'s
guards are the reachability valuation of a real forward path `V`
(`Chained (EdgeTaken P w) V`, entry head). No dominance. -/
theorem cfgConstraintsFor_sat {P : Program} {w : State} {V : List Nat}
    (hfwd : forwardOK P = true) (hamo : amoSideOK P = true)
    (hentryV : P.entry ∈ V) (hhead : V.head? = some P.entry)
    (hblk : ∀ q, q < P.blocks.length → w.blks q = decide (q ∈ V))
    (hedge : Chained (EdgeTaken P w) V)
    {S : Nat} (hSlt : S < P.blocks.length) :
    ∀ c ∈ cfgConstraintsFor P S, c.eval w = true := by
  intro c hc
  unfold cfgConstraintsFor at hc
  by_cases hSe : S = P.entry
  · rw [if_pos hSe] at hc; cases hc
  · rw [if_neg hSe] at hc
    have hStail : S ∈ V → S ∈ V.tail := by
      intro hSV
      cases V with
      | nil => cases hhead
      | cons v0 rest =>
          obtain rfl := Option.some.inj hhead
          rcases List.mem_cons.mp hSV with rfl | h
          · exact absurd rfl hSe
          · exact h
    rcases List.mem_cons.mp hc with rfl | hc1
    · -- edge feasibility: `guard S ⇒ ⋁ (guard p ∧ edge-cond)`
      simp only [eval_mkImp, guard_eval hentryV hblk hSlt, Bool.or_eq_true]
      by_cases hSV : S ∈ V
      · right
        rw [eval_mkOr]
        obtain ⟨p, hpV, hE, -⟩ := chained_pred hedge hedge (hStail hSV)
        obtain ⟨cond, hcondmem, hcondeval⟩ := hE.edge_cond
        have hplt : p < P.blocks.length :=
          Nat.lt_trans (pred_lt hfwd (mem_predsOf.mpr ⟨cond, hcondmem⟩)) hSlt
        apply List.any_eq_true.mpr
        refine ⟨mkAnd2 (guardOf P p) cond,
          List.mem_map.mpr ⟨(p, cond), hcondmem, rfl⟩, ?_⟩
        simp only [eval_mkAnd2, guard_eval hentryV hblk hplt, hcondeval,
          decide_eq_true hpV, Bool.and_true]
      · left; simp [hSV]
    · rcases List.mem_cons.mp hc1 with rfl | hc2
      · -- predecessor feasibility: `guard S ⇒ ⋁ guard p`
        simp only [eval_mkImp, guard_eval hentryV hblk hSlt, Bool.or_eq_true]
        by_cases hSV : S ∈ V
        · right
          rw [eval_mkOr]
          obtain ⟨p, hpV, hE, -⟩ := chained_pred hedge hedge (hStail hSV)
          obtain ⟨cond, hcondmem, -⟩ := hE.edge_cond
          have hplt : p < P.blocks.length :=
            Nat.lt_trans (pred_lt hfwd (mem_predsOf.mpr ⟨cond, hcondmem⟩)) hSlt
          apply List.any_eq_true.mpr
          exact ⟨guardOf P p, List.mem_map.mpr ⟨(p, cond), hcondmem, rfl⟩,
            by simp only [guard_eval hentryV hblk hplt, decide_eq_true hpV]⟩
        · left; simp [hSV]
      · -- at-most-one: `guard S ⇒ (¬guard q₁ ∨ ¬guard q₂)`, q₁ ≠ q₂
        rw [List.mem_map] at hc2
        obtain ⟨cl, hclmem, rfl⟩ := hc2
        simp only [eval_mkImp, guard_eval hentryV hblk hSlt, Bool.or_eq_true]
        by_cases hSV : S ∈ V
        · right
          obtain ⟨g1, g2, hmem1, hmem2, hne, rfl⟩ := mem_amoClauses hclmem
          rw [List.mem_map] at hmem1 hmem2
          obtain ⟨⟨q1, c1⟩, hq1e, rfl⟩ := hmem1
          obtain ⟨⟨q2, c2⟩, hq2e, rfl⟩ := hmem2
          have hq1p : q1 ∈ predsOf P S := mem_predsOf.mpr ⟨c1, hq1e⟩
          have hq2p : q2 ∈ predsOf P S := mem_predsOf.mpr ⟨c2, hq2e⟩
          have hq1lt : q1 < P.blocks.length := Nat.lt_trans (pred_lt hfwd hq1p) hSlt
          have hq2lt : q2 < P.blocks.length := Nat.lt_trans (pred_lt hfwd hq2p) hSlt
          have hq12 : q1 ≠ q2 := fun h => hne (by rw [h])
          simp only [Exp.eval, BinOp.denote, UnOp.denote,
            guard_eval hentryV hblk hq1lt, guard_eval hentryV hblk hq2lt,
            Bool.or_eq_true]
          by_cases h1 : q1 ∈ V
          · by_cases h2 : q2 ∈ V
            · exact absurd (visited_amo hfwd hamo hedge hSlt
                (two_mem_le_length hq1p hq2p hq12) h1 hq1p h2 hq2p) hq12
            · right; simp [h2]
          · left; simp [h1]
        · left; simp [hSV]

/-- **Every CFG constraint of `P`, satisfied by any path state.** -/
theorem cfgConstraints_sat {P : Program} {w : State} {V : List Nat}
    (hfwd : forwardOK P = true) (hamo : amoSideOK P = true)
    (hentryV : P.entry ∈ V) (hhead : V.head? = some P.entry)
    (hblk : ∀ q, q < P.blocks.length → w.blks q = decide (q ∈ V))
    (hedge : Chained (EdgeTaken P w) V) :
    ∀ c ∈ cfgConstraints P, c.eval w = true := by
  rw [cfgConstraints_eq]
  intro c hc
  rw [List.mem_flatten] at hc
  obtain ⟨l, hl, hcl⟩ := hc
  rw [List.mem_map] at hl
  obtain ⟨S, hSrange, rfl⟩ := hl
  exact cfgConstraintsFor_sat hfwd hamo hentryV hhead hblk hedge
    (List.mem_range.mp hSrange) c hcl

/-- **Guarded command facts, satisfied by any path state.**

`factConstraints P b cmd` (the guarded fact `guard b ⇒ lower(fact)` of a
non-phi command) holds at `w` given the command's `factB` fact at `w`
for active `b`. Unvisited `b` ⇒ vacuous. No dominance, and — evaluating
the fact at `w` directly — no `guardFreeOK` either. -/
theorem factConstraints_sat {P : Program} {w : State} {V : List Nat}
    (hentryV : P.entry ∈ V)
    {b : Nat} {cmd : Cmd} (hblt : b < P.blocks.length)
    (hblk : ∀ q, q < P.blocks.length → w.blks q = decide (q ∈ V))
    (hfact : b ∈ V → ∀ f, cmd.factB = some f → f.eval w = true) :
    ∀ c ∈ factConstraints P b cmd, c.eval w = true := by
  intro c hc
  obtain ⟨f, hfb, rfl⟩ := mem_factConstraints hc
  simp only [eval_mkImp, guard_eval hentryV hblk hblt, Bool.or_eq_true]
  by_cases hbV : b ∈ V
  · right
    rw [eval_lower]
    exact hfact hbV f hfb
  · left; simp [hbV]

end Ttac
