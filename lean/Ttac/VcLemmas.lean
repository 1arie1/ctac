import Ttac.Vc

/-!
# Evaluation lemmas for the VC infrastructure

Semantic characterizations of the fold helpers - after these, no proof
ever needs to look inside `mkImp`/`mkOr`/... again. (The congruence
lemma lives below, in `Ttac.Vars`.)
-/

namespace Ttac

namespace Vc

/-! ## Fold-evaluation characterizations -/

@[simp] theorem evalB_mkImp (s : State) (g φ : BExp) :
    evalB s (mkImp g φ) = (!evalB s g || evalB s φ) := by
  unfold mkImp
  split <;> simp [evalB]

@[simp] theorem evalB_mkNot (s : State) (a : BExp) :
    evalB s (mkNot a) = !evalB s a := by
  unfold mkNot
  split <;> simp [evalB]

@[simp] theorem evalB_mkAnd2 (s : State) (a b : BExp) :
    evalB s (mkAnd2 a b) = (evalB s a && evalB s b) := by
  unfold mkAnd2
  split
  · simp_all [evalB]
  · split
    · simp_all [evalB]
    · split
      · rename_i h
        rcases h with h | h <;> simp_all [evalB]
      · split
        · simp_all
        · simp [evalB]

@[simp] theorem evalB_mkOr2 (s : State) (a b : BExp) :
    evalB s (mkOr2 a b) = (evalB s a || evalB s b) := by
  unfold mkOr2
  split
  · simp_all [evalB]
  · split
    · simp_all [evalB]
    · split
      · rename_i h
        rcases h with h | h <;> simp_all [evalB]
      · split
        · simp_all
        · simp [evalB]

theorem evalB_orChain (s : State) (a : BExp) (l : List BExp) :
    evalB s (orChain a l) = (evalB s a || l.any (evalB s ·)) := by
  induction l generalizing a with
  | nil => simp [orChain]
  | cons b r ih => simp [orChain, evalB, ih]

theorem mem_dedup1 {a : BExp} {l : List BExp} : a ∈ dedup1 l ↔ a ∈ l := by
  induction l with
  | nil => simp [dedup1]
  | cons x xs ih =>
      simp only [dedup1, List.mem_cons, List.mem_filter]
      constructor
      · rintro (rfl | ⟨h, _⟩)
        · exact Or.inl rfl
        · exact Or.inr (ih.mp h)
      · rintro (rfl | h)
        · exact Or.inl rfl
        · by_cases hax : a = x
          · exact Or.inl hax
          · exact Or.inr ⟨ih.mpr h, by simpa using hax⟩

theorem any_dedup1 (p : BExp → Bool) (l : List BExp) :
    (dedup1 l).any p = l.any p := by
  cases hl : l.any p with
  | true =>
      obtain ⟨a, ha, hp⟩ := List.any_eq_true.mp hl
      exact List.any_eq_true.mpr ⟨a, mem_dedup1.mpr ha, hp⟩
  | false =>
      by_contra hne
      have := List.any_eq_true.mp (by simpa using hne)
      obtain ⟨a, ha, hp⟩ := this
      have := List.any_eq_true.mpr ⟨a, mem_dedup1.mp ha, hp⟩
      simp [hl] at this

theorem evalB_mkOr (s : State) (l : List BExp) :
    evalB s (mkOr l) = l.any (evalB s ·) := by
  simp only [mkOr]
  split
  · rename_i h
    have : (BExp.lit true) ∈ l := mem_dedup1.mp h
    simp only [evalB]
    symm
    simp only [List.any_eq_true]
    exact ⟨_, this, rfl⟩
  · rename_i hT
    have hfilter :
        ((dedup1 l).filter (· ≠ BExp.lit false)).any (evalB s ·)
          = l.any (evalB s ·) := by
      cases hl : l.any (evalB s ·) with
      | true =>
          obtain ⟨a, ha, hp⟩ := List.any_eq_true.mp hl
          refine List.any_eq_true.mpr
            ⟨a, List.mem_filter.mpr ⟨mem_dedup1.mpr ha, ?_⟩, hp⟩
          exact decide_eq_true fun h => by subst h; simp [evalB] at hp
      | false =>
          by_contra hne
          simp only [Bool.not_eq_false, List.any_eq_true, List.mem_filter,
            ne_eq, decide_not, Bool.not_eq_eq_eq_not, Bool.not_true,
            decide_eq_false_iff_not] at hne
          obtain ⟨a, ⟨ha, -⟩, hp⟩ := hne
          have := List.any_eq_true.mpr ⟨a, mem_dedup1.mp ha, hp⟩
          simp [hl] at this
    split
    · rename_i hnil
      rw [← hfilter, hnil]
      simp [evalB]
    · rename_i d hone
      rw [← hfilter, hone]
      simp [List.any]
    · rename_i d ds hcons
      rw [← hfilter, hcons, evalB_orChain]
      simp [List.any_cons]

theorem mem_pairsLt {p : BExp × BExp} {l : List BExp} :
    p ∈ pairsLt l → p.1 ∈ l ∧ p.2 ∈ l := by
  induction l with
  | nil => simp [pairsLt]
  | cons x xs ih =>
      simp only [pairsLt, List.mem_append, List.mem_map, List.mem_cons]
      rintro (⟨y, hy, rfl⟩ | h)
      · exact ⟨Or.inl rfl, Or.inr hy⟩
      · have := ih h
        exact ⟨Or.inr this.1, Or.inr this.2⟩

theorem dedup1_nodup : ∀ (l : List BExp), (dedup1 l).Nodup
  | [] => List.nodup_nil
  | x :: xs => by
      simp only [dedup1]
      refine List.nodup_cons.mpr
        ⟨?_, List.filter_sublist.nodup (dedup1_nodup xs)⟩
      intro hmem
      have := (List.mem_filter.mp hmem).2
      simp at this

theorem pairsLt_ne {l : List BExp} (hnd : l.Nodup) {p : BExp × BExp}
    (hp : p ∈ pairsLt l) : p.1 ≠ p.2 := by
  induction l with
  | nil => cases hp
  | cons x xs ih =>
      simp only [pairsLt, List.mem_append, List.mem_map] at hp
      obtain ⟨hx, hnd'⟩ := List.nodup_cons.mp hnd
      rcases hp with ⟨y, hy, rfl⟩ | hp'
      · intro h
        have h' : x = y := h
        exact hx (by rw [h']; exact hy)
      · exact ih hnd' hp'

theorem mem_amoClauses {cl : BExp} {l : List BExp} (h : cl ∈ amoClauses l) :
    ∃ a b, a ∈ l ∧ b ∈ l ∧ a ≠ b ∧ cl = .or (.not a) (.not b) := by
  simp only [amoClauses, List.mem_map] at h
  obtain ⟨⟨a, b⟩, hp, rfl⟩ := h
  have hne := pairsLt_ne (dedup1_nodup _) hp
  obtain ⟨h1, h2⟩ := mem_pairsLt hp
  exact ⟨a, b, (List.mem_filter.mp (mem_dedup1.mp h1)).1,
    (List.mem_filter.mp (mem_dedup1.mp h2)).1, hne, rfl⟩

@[simp] theorem evalI_mkIteI (s : State) (c : BExp) (t e : IExp) :
    evalI s (mkIteI c t e) = if evalB s c then evalI s t else evalI s e := by
  by_cases ht : t = e
  · subst ht; simp [mkIteI]
  · unfold mkIteI
    rw [if_neg ht]
    split
    · simp [evalB]
    · simp [evalB]
    · simp [evalI]

@[simp] theorem evalB_mkIteB (s : State) (c t e : BExp) :
    evalB s (mkIteB c t e) = if evalB s c then evalB s t else evalB s e := by
  by_cases ht : t = e
  · subst ht; simp [mkIteB]
  · unfold mkIteB
    rw [if_neg ht]
    split
    · simp [evalB]
    · simp [evalB]
    · simp only [evalB]
      cases hc : evalB s c <;> simp
    · simp only [evalB_mkNot, evalB]
      cases hc : evalB s c <;> simp
    · simp [evalB]

/-! ## The lowering mirror is semantics-preserving -/

mutual
  theorem evalI_lowerI (s : State) : (e : IExp) → evalI s (lowerI e) = evalI s e
    | .lit _ => rfl
    | .var _ => rfl
    | .add a b => by simp only [lowerI, evalI, evalI_lowerI s a, evalI_lowerI s b]
    | .sub a b => by simp only [lowerI, evalI, evalI_lowerI s a, evalI_lowerI s b]
    | .mul a b => by simp only [lowerI, evalI, evalI_lowerI s a, evalI_lowerI s b]
    | .div a b => by simp only [lowerI, evalI, evalI_lowerI s a, evalI_lowerI s b]
    | .ite c t e => by
        simp only [lowerI, evalI, evalI_mkIteI, evalB_lowerB s c,
          evalI_lowerI s t, evalI_lowerI s e]

  theorem evalB_lowerB (s : State) : (e : BExp) → evalB s (lowerB e) = evalB s e
    | .lit _ => rfl
    | .var _ => rfl
    | .le a b => by simp only [lowerB, evalB, evalI_lowerI s a, evalI_lowerI s b]
    | .lt a b => by simp only [lowerB, evalB, evalI_lowerI s a, evalI_lowerI s b]
    | .eqI a b => by simp only [lowerB, evalB, evalI_lowerI s a, evalI_lowerI s b]
    | .eqB a b => by simp only [lowerB, evalB, evalB_lowerB s a, evalB_lowerB s b]
    | .not a => by simp only [lowerB, evalB, evalB_mkNot, evalB_lowerB s a]
    | .and a b => by
        simp only [lowerB, evalB, evalB_mkAnd2, evalB_lowerB s a, evalB_lowerB s b]
    | .or a b => by
        simp only [lowerB, evalB, evalB_mkOr2, evalB_lowerB s a, evalB_lowerB s b]
    | .imp a b => by
        simp only [lowerB, evalB, evalB_mkImp, evalB_lowerB s a, evalB_lowerB s b]
    | .blk b => rfl
    | .ite c t e => by
        simp only [lowerB, evalB, evalB_mkIteB, evalB_lowerB s c,
          evalB_lowerB s t, evalB_lowerB s e]
end

end Vc

end Ttac
