import Ttac.Vc

/-!
# Evaluation lemmas for the VC infrastructure

Semantic characterizations of the fold helpers - after these, no proof
ever needs to look inside `mkImp`/`mkOr`/... again. One lemma per fold;
the operator-fold dispatchers (`unFold`/`binFold`) get one lemma each by
a `cases op` sweep, so a new operator costs one automatic case here.
-/

namespace Ttac

namespace Vc

/-! ## Fold-evaluation characterizations -/

@[simp] theorem eval_mkImp (s : State) (g φ : BExp) :
    (mkImp g φ).eval s = (!g.eval s || φ.eval s) := by
  unfold mkImp
  split <;> simp [Exp.eval, BinOp.denote]

@[simp] theorem eval_mkNot (s : State) (a : BExp) :
    (mkNot a).eval s = !a.eval s := by
  unfold mkNot
  split <;> simp [Exp.eval, UnOp.denote]

@[simp] theorem eval_mkAnd2 (s : State) (a b : BExp) :
    (mkAnd2 a b).eval s = (a.eval s && b.eval s) := by
  unfold mkAnd2
  split
  · simp_all [Exp.eval]
  · split
    · simp_all [Exp.eval]
    · split
      · rename_i h
        rcases h with h | h <;> simp_all [Exp.eval]
      · split
        · simp_all
        · simp [Exp.eval, BinOp.denote]

@[simp] theorem eval_mkOr2 (s : State) (a b : BExp) :
    (mkOr2 a b).eval s = (a.eval s || b.eval s) := by
  unfold mkOr2
  split
  · simp_all [Exp.eval]
  · split
    · simp_all [Exp.eval]
    · split
      · rename_i h
        rcases h with h | h <;> simp_all [Exp.eval]
      · split
        · simp_all
        · simp [Exp.eval, BinOp.denote]

theorem eval_orChain (s : State) (a : BExp) (l : List BExp) :
    (orChain a l).eval s = (a.eval s || l.any (Exp.eval s ·)) := by
  induction l generalizing a with
  | nil => simp [orChain]
  | cons b r ih => simp [orChain, Exp.eval, BinOp.denote, ih]

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

theorem eval_mkOr (s : State) (l : List BExp) :
    (mkOr l).eval s = l.any (Exp.eval s ·) := by
  simp only [mkOr]
  split
  · rename_i h
    have : (Exp.litB true) ∈ l := mem_dedup1.mp h
    simp only [Exp.eval]
    symm
    simp only [List.any_eq_true]
    exact ⟨_, this, rfl⟩
  · rename_i hT
    have hfilter :
        ((dedup1 l).filter (· ≠ Exp.litB false)).any (Exp.eval s ·)
          = l.any (Exp.eval s ·) := by
      cases hl : l.any (Exp.eval s ·) with
      | true =>
          obtain ⟨a, ha, hp⟩ := List.any_eq_true.mp hl
          refine List.any_eq_true.mpr
            ⟨a, List.mem_filter.mpr ⟨mem_dedup1.mpr ha, ?_⟩, hp⟩
          exact decide_eq_true fun h => by subst h; simp [Exp.eval] at hp
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
      simp [Exp.eval]
    · rename_i d hone
      rw [← hfilter, hone]
      simp [List.any]
    · rename_i d ds hcons
      rw [← hfilter, hcons, eval_orChain]
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
    ∃ a b, a ∈ l ∧ b ∈ l ∧ a ≠ b
      ∧ cl = .bin .or (.un .not a) (.un .not b) := by
  simp only [amoClauses, List.mem_map] at h
  obtain ⟨⟨a, b⟩, hp, rfl⟩ := h
  have hne := pairsLt_ne (dedup1_nodup _) hp
  obtain ⟨h1, h2⟩ := mem_pairsLt hp
  exact ⟨a, b, (List.mem_filter.mp (mem_dedup1.mp h1)).1,
    (List.mem_filter.mp (mem_dedup1.mp h2)).1, hne, rfl⟩

@[simp] theorem eval_mkIte (s : State) {t : Ty} (c : BExp) (th el : Exp t) :
    (mkIte c th el).eval s
      = if c.eval s then th.eval s else el.eval s := by
  by_cases hte : th = el
  · subst hte; simp [mkIte]
  · unfold mkIte
    rw [if_neg hte]
    split
    · simp [Exp.eval]
    · simp [Exp.eval]
    · simp only [Exp.eval]
      cases hc : c.eval s <;> simp
    · simp only [eval_mkNot, Exp.eval]
      cases hc : c.eval s <;> simp
    · simp [Exp.eval]

/-! ## The lowering mirror is semantics-preserving -/

@[simp] theorem eval_unFold (s : State) {a c : Ty} (op : UnOp a c)
    (e : Exp a) : (unFold op e).eval s = op.denote (e.eval s) := by
  cases op
  simp [unFold, UnOp.denote, eval_mkNot]

@[simp] theorem eval_binFold (s : State) {a b c : Ty} (op : BinOp a b c)
    (l : Exp a) (r : Exp b) :
    (binFold op l r).eval s = op.denote (l.eval s) (r.eval s) := by
  cases op <;>
    simp [binFold, BinOp.denote, Exp.eval, eval_mkAnd2, eval_mkOr2,
      eval_mkImp]

theorem eval_lower (s : State) : {t : Ty} → (e : Exp t) →
    (lower e).eval s = e.eval s
  | _, .litI _ => rfl
  | _, .litB _ => rfl
  | _, .var _ _ => rfl
  | _, .blk _ => rfl
  | _, .un op e => by
      simp only [lower, eval_unFold, eval_lower s e, Exp.eval]
  | _, .bin op l r => by
      simp only [lower, eval_binFold, eval_lower s l, eval_lower s r,
        Exp.eval]
  | _, .tern op e₁ e₂ e₃ => by
      simp only [lower, Exp.eval, eval_lower s e₁, eval_lower s e₂,
        eval_lower s e₃]
  | _, .ite c th el => by
      simp only [lower, eval_mkIte, eval_lower s c, eval_lower s th,
        eval_lower s el, Exp.eval]

end Vc

end Ttac
