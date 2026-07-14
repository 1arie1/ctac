import Ttac.VcTrace

/-!
# Shared VC characterization lemmas

Bridges from the Bool well-formedness checks to their `Prop` content,
shape characterizations of the constraint generators, and the variable
inventories of the fold constructors and phi right-hand sides. These
are the encoding-generic facts every proof of the checker consumes;
the denotational chain (`VcCfgPath`/`VcDenot`/`VcWeaken`/`VcAdequacy`)
is their only remaining client.
-/

namespace Ttac

/-! ## Small bridges -/

theorem useOK_dom {P : Program} {tx : Ty × Nat} {b i : Nat}
    (h : useOK (domTable P) (defPositions P tx) b i = true) :
    ∀ d j, IsDefAt P tx d j → d = b ∨ d ∈ domOf P b := by
  intro d j hd
  have := List.all_eq_true.mp h (d, j) (mem_defPositions.mpr hd)
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this
  rcases this with ⟨hdb, _⟩ | ⟨_, hcont⟩
  · exact Or.inl hdb
  · exact Or.inr (List.contains_iff_mem.mp hcont)

theorem armUseOK_dom {P : Program} {tx : Ty × Nat} {p : Nat}
    (h : armUseOK (domTable P) (defPositions P tx) p = true) :
    ∀ d j, IsDefAt P tx d j → d ∈ domOf P p := by
  intro d j hd
  have := List.all_eq_true.mp h (d, j) (mem_defPositions.mpr hd)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact List.contains_iff_mem.mp this.2

/-- Program expressions are guard-free (W8 bridge). -/
theorem guardFree_at {P : Program} (hgf : guardFreeOK P = true)
    {B : Block} (hB : B ∈ P.blocks) {c : Cmd} (hc : c ∈ B.cmds) :
    cmdGuardFree c = true :=
  List.all_eq_true.mp (List.all_eq_true.mp hgf B hB) c hc

/-- Guard evaluation in any state that reads guards by visitedness. -/
theorem guard_eval {P : Program} {V : List Nat} (hentryV : P.entry ∈ V)
    {w : State}
    (hblk : ∀ q, q < P.blocks.length → w.blks q = decide (q ∈ V))
    {q : Nat} (hq : q < P.blocks.length) :
    (Vc.guardOf P q).eval w = decide (q ∈ V) := by
  unfold Vc.guardOf
  split
  · rename_i h
    rw [h]
    simp [Exp.eval, hentryV]
  · simpa [Exp.eval] using hblk q hq

/-- Predecessor extraction for a tail element of a doubly-chained list. -/
theorem chained_pred {R S : Nat → Nat → Prop} :
    ∀ {V : List Nat}, Chained R V → Chained S V → ∀ {v}, v ∈ V.tail →
      ∃ p, p ∈ V ∧ R p v ∧ S p v := by
  intro V
  induction V with
  | nil => intro _ _ v hv; cases hv
  | cons x rest ih =>
      intro hR hS v hv
      cases rest with
      | nil => cases hv
      | cons y rest' =>
          obtain ⟨hRxy, hRch⟩ := chained_destruct hR
          obtain ⟨hSxy, hSch⟩ := chained_destruct hS
          rcases List.mem_cons.mp hv with rfl | hv'
          · exact ⟨x, List.mem_cons_self .., hRxy, hSxy⟩
          · obtain ⟨p, hp, hr, hs⟩ := ih hRch hSch hv'
            exact ⟨p, List.mem_cons_of_mem _ hp, hr, hs⟩

theorem two_mem_le_length {l : List Nat} {a b : Nat} (ha : a ∈ l) (hb : b ∈ l)
    (hne : a ≠ b) : 2 ≤ l.length := by
  match l, ha, hb with
  | [x], ha, hb =>
      obtain rfl := List.mem_singleton.mp ha
      obtain rfl := List.mem_singleton.mp hb
      exact absurd rfl hne
  | x :: y :: rest, _, _ => simp [List.length_cons]

/-- Each phi arm's predecessor really is a CFG predecessor. -/
theorem phiArm_pred {P : Program} {b : Nat} {arms : PhiArms}
    (h : phiArmsOK P b arms = true) {p src : Nat} (hp : (p, src) ∈ arms) :
    p ∈ predsOf P b := by
  simp only [phiArmsOK, Bool.and_eq_true] at h
  have := List.all_eq_true.mp h.2 (p, src) hp
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true] at this
  obtain ⟨-, ⟨q, cond⟩, hmem, hq⟩ := this
  obtain rfl : q = p := by simpa using hq
  exact mem_predsOf.mpr ⟨cond, hmem⟩

/-- An edge condition reads no guard atom, and its variables are
exactly the source block's branch register. -/
theorem edge_cond_vars {P : Program} {S p : Nat} {cond : BExp}
    (h : (p, cond) ∈ Vc.edgesTo P S) :
    cond.blkVars = []
      ∧ ∀ q ∈ cond.vars, ∃ r B t e, q = (Ty.bool, r)
          ∧ P.block? p = some B ∧ B.term = .ifGoto r t e := by
  obtain ⟨B, hB, hout⟩ := mem_allEdges_elim (mem_edgesTo.mp h)
  unfold Vc.outEdges at hout
  split at hout
  · cases hout
  · obtain rfl : cond = .litB true := by
      simp only [List.mem_singleton, Prod.mk.injEq] at hout
      exact hout.2.2
    exact ⟨rfl, fun q hq => by cases hq⟩
  · rename_i creg t e hterm
    simp only [List.mem_cons, Prod.mk.injEq,
      List.not_mem_nil, or_false] at hout
    rcases hout with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
    · refine ⟨rfl, fun q hq => ?_⟩
      obtain rfl : q = (Ty.bool, creg) := by simpa [Exp.vars] using hq
      exact ⟨creg, B, t, e, rfl, hB, hterm⟩
    · refine ⟨rfl, fun q hq => ?_⟩
      obtain rfl : q = (Ty.bool, creg) := by simpa [Exp.vars] using hq
      exact ⟨creg, B, t, e, rfl, hB, hterm⟩

/-! ## Constraint-shape characterizations -/

theorem mem_factConstraints {P : Program} {b : Nat} {cmd : Cmd} {c : BExp}
    (h : c ∈ Vc.factConstraints P b cmd) :
    ∃ f, cmd.factB = some f
      ∧ c = Vc.mkImp (Vc.guardOf P b) (Vc.lower f) := by
  unfold Vc.factConstraints at h
  split at h
  · rename_i f hf
    obtain rfl := List.mem_singleton.mp h
    exact ⟨f, hf, rfl⟩
  · cases h

theorem mem_expectedMapDefs {P : Program} {md : Nat × MExp}
    (h : md ∈ Vc.expectedMapDefs P) :
    ∃ (b : Nat) (B : Block) (i : Nat) (c : Cmd),
      P.block? b = some B ∧ B.cmds[i]? = some c
        ∧ Vc.cmdMapDef? P c = some md := by
  simp only [Vc.expectedMapDefs, List.mem_flatten, List.mem_map] at h
  obtain ⟨L, ⟨B, hBmem, rfl⟩, hin⟩ := h
  rw [List.mem_filterMap] at hin
  obtain ⟨c, hc, hcd⟩ := hin
  obtain ⟨b, hb⟩ := List.mem_iff_getElem?.mp hBmem
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hc
  exact ⟨b, B, i, c, hb, hi, hcd⟩

theorem cmdMapDef?_eq_some {P : Program} {c : Cmd} {x : Nat} {rhs : MExp}
    (h : Vc.cmdMapDef? P c = some (x, rhs)) :
    (∃ e, c = .assign .map x e ∧ rhs = Vc.lower e)
      ∨ (∃ arms, c = .phi .map x arms ∧ rhs = Vc.phiRhs P .map arms) := by
  cases c with
  | assign t y e =>
      cases t with
      | map =>
          obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp (Option.some.inj h)
          exact Or.inl ⟨e, rfl, rfl⟩
      | int => cases h
      | bool => cases h
  | phi t y arms =>
      cases t with
      | map =>
          obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp (Option.some.inj h)
          exact Or.inr ⟨arms, rfl, rfl⟩
      | int => cases h
      | bool => cases h
  | havoc t y => cases h
  | assume φ => cases h
  | assert r => cases h

theorem mem_cmdConstraints {P : Program} {b : Nat} {cmd : Cmd} {c : BExp}
    (h : c ∈ Vc.cmdConstraints P b cmd) :
    c ∈ Vc.factConstraints P b cmd
      ∨ ∃ t x arms, cmd = .phi t x arms
          ∧ (eqConstraint? t x (Vc.phiRhs P t arms) = some c
             ∨ (2 ≤ arms.length
                ∧ c ∈ Vc.amoClauses
                    (arms.map fun (p, _) => Vc.guardOf P p))) := by
  cases cmd with
  | phi t x arms =>
      refine Or.inr ⟨t, x, arms, rfl, ?_⟩
      simp only [Vc.cmdConstraints, List.mem_append] at h
      rcases h with h | h
      · rcases heq : eqConstraint? t x (Vc.phiRhs P t arms) with - | eq
        · rw [heq] at h; cases h
        · rw [heq] at h
          obtain rfl := List.mem_singleton.mp h
          exact Or.inl rfl
      · split at h
        · exact Or.inr ⟨by assumption, h⟩
        · cases h
  | assign t x e => exact Or.inl h
  | havoc t x => exact Or.inl h
  | assume φ => exact Or.inl h
  | assert r => exact Or.inl h

/-! ## Variable inventories of the fold constructors

Folds never invent variables: everything the folded term reads, the
inputs read. Needed because the witness reasons about the *lowered*
right-hand sides of map definitions. -/

theorem guardOf_vars (P : Program) (q : Nat) :
    (Vc.guardOf P q).vars = [] := by
  unfold Vc.guardOf; split <;> rfl

theorem mkNot_vars {a : BExp} :
    ∀ p ∈ (Vc.mkNot a).vars, p ∈ a.vars := by
  unfold Vc.mkNot
  split <;> intro p hp <;> simp_all [Exp.vars]

theorem mkIte_vars {t : Ty} {c : BExp} {th el : Exp t} :
    ∀ p ∈ (Vc.mkIte c th el).vars,
      p ∈ c.vars ∨ p ∈ th.vars ∨ p ∈ el.vars := by
  intro p hp
  unfold Vc.mkIte at hp
  split at hp
  · exact Or.inr (Or.inl hp)
  · split at hp
    · exact Or.inr (Or.inl hp)
    · exact Or.inr (Or.inr hp)
    · exact Or.inl hp
    · exact Or.inl (mkNot_vars _ hp)
    · simp only [Exp.vars, List.mem_append] at hp
      tauto

theorem mkNot_blkVars {a : BExp} :
    ∀ q ∈ (Vc.mkNot a).blkVars, q ∈ a.blkVars := by
  unfold Vc.mkNot
  split <;> intro q hq <;> simp_all [Exp.blkVars]

theorem mkIte_blkVars {t : Ty} {c : BExp} {th el : Exp t} :
    ∀ q ∈ (Vc.mkIte c th el).blkVars,
      q ∈ c.blkVars ∨ q ∈ th.blkVars ∨ q ∈ el.blkVars := by
  intro q hq
  unfold Vc.mkIte at hq
  split at hq
  · exact Or.inr (Or.inl hq)
  · split at hq
    · exact Or.inr (Or.inl hq)
    · exact Or.inr (Or.inr hq)
    · exact Or.inl hq
    · exact Or.inl (mkNot_blkVars _ hq)
    · simp only [Exp.blkVars, List.mem_append] at hq
      tauto

/-! ## Phi right-hand-side inventory -/

theorem phiChain_vars {P : Program} {t : Ty} :
    ∀ (a : Nat × Nat) (rest : List (Nat × Nat)),
      ∀ p ∈ (Vc.phiChain P t a rest).vars,
        ∃ q s, (q, s) ∈ a :: rest ∧ p = (t, s)
  | (q0, s0), [], p, hp => by
      simp only [Vc.phiChain, Exp.vars] at hp
      obtain rfl := List.mem_singleton.mp hp
      exact ⟨q0, s0, List.mem_cons_self .., rfl⟩
  | (q0, s0), a' :: rest', p, hp => by
      rcases mkIte_vars p hp with hg | hs | ht
      · rw [guardOf_vars] at hg; cases hg
      · simp only [Exp.vars] at hs
        obtain rfl := List.mem_singleton.mp hs
        exact ⟨q0, s0, List.mem_cons_self .., rfl⟩
      · obtain ⟨q, s, hq, rfl⟩ := phiChain_vars a' rest' p ht
        exact ⟨q, s, List.mem_cons_of_mem _ hq, rfl⟩

/-! ## The phi-arm rule, in dependence form

Every variable a phi right-hand side reads is defined strictly below
the phi's block: the checker's arm-use rule gives `d ≤ p` and the phi
shape gives `p < b` (and its nonemptiness discharges the placeholder
case of `phiRhs`). -/

theorem phi_src_lt {P : Program}
    (huse : usesOK P = true) (hphi : phiOK P = true)
    {b : Nat} {B : Block} {i : Nat} {t : Ty} {x : Nat} {arms : PhiArms}
    (hB : P.block? b = some B) (hc : B.cmds[i]? = some (.phi t x arms)) :
    ∀ p ∈ (Vc.phiRhs P t arms).vars,
      ∀ d j, IsDefAt P p d j → d < b := by
  have harms : phiArmsOK P b arms = true :=
    phiOK_at hphi hB (List.mem_of_getElem? hc)
  have hu := usesOK_cmd huse hB hc
  simp only [cmdUsesOK] at hu
  intro p hp d j hd
  cases arms with
  | nil => simp [phiArmsOK] at harms
  | cons a rest =>
      obtain ⟨q, s, hq, rfl⟩ := phiChain_vars a rest p hp
      have hle := armUseOK_le (List.all_eq_true.mp hu (q, s) hq) d j hd
      have := phiArm_lt harms hq
      omega


end Ttac
