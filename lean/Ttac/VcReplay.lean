import Batteries.Data.List.Pairwise
import Ttac.DefExt
import Ttac.VcTrace

/-!
# The witness as a definitional extension

A failing execution's final state σ, with the guard component set from
the visited-block list, satisfies every expected constraint except the
*unguarded equations of unvisited blocks*: phi equations (any sort) and
map definitions (the encoder emits stores/aliases/map-phis as global
`define-fun`s, never block-guarded). Those are exactly a definition
list in the sense of `Ttac.DefExt` - extracted by `Vc.unguardedDef?`,
in program order, by `witnessDefs` - and this file discharges the
generic lemma's two obligations for it:

- **ordering** (`orderedDefs_witnessDefs`): SSA gives pairwise-distinct
  targets, and dominated uses pin every right-hand-side variable's
  definition lexicographically before the defining position (for phis
  the arm rule `d ≤ p < b` even gives a strictly earlier block);
  program order refines both to the list order.
- **target inventory** (`target_defAt`/`not_target_of_visited`): a
  target is precisely a register with an unguarded definition in an
  unvisited block, which is what the robustness instances in `VcSound`
  reason against.

Everything is sort-generic: one extraction, one ordering proof, one
chain-selection lemma - phis and map definitions of any sort go
through the same machinery.

The witness itself is just `applyDefs` over the extracted list
(`witness`). Guards live in their own `State.blks` component, written
once by `setBlockVars` and never touched by the extension (definitions
only write program registers).

The chain-selection lemmas at the bottom (`phiRhs_select`) are the
semantic content of the phi constraint for *visited* joins - which ITE
arm survives under the guard assignment - and are consumed by the
robustness instances for visited phi equations and map-phi
definitions.
-/

namespace Ttac

/-! ## Guard initialization -/

/-- Visited blocks true, the synthetic exit guard (index
`P.blocks.length`) true, everything else false. -/
def setBlockVars (P : Program) (V : List Nat) (σ : State) : State :=
  { σ with blks := fun q => decide (q ∈ V ∨ q = P.blocks.length) }

@[simp] theorem setBlockVars_regs (P : Program) (V : List Nat) (σ : State) :
    (setBlockVars P V σ).regs = σ.regs := rfl

theorem setBlockVars_blk (P : Program) (V : List Nat) (σ : State)
    {q : Nat} (hq : q < P.blocks.length) :
    (setBlockVars P V σ).blks q = decide (q ∈ V) := by
  simp only [setBlockVars]
  by_cases h : q ∈ V <;> (simp [h]; try omega)

theorem setBlockVars_exit (P : Program) (V : List Nat) (σ : State) :
    (setBlockVars P V σ).blks P.blocks.length = true := by
  simp [setBlockVars]

/-! ## Variable inventories of folds and the lowering mirror

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

theorem mkImp_vars {g φ : BExp} :
    ∀ p ∈ (Vc.mkImp g φ).vars, p ∈ g.vars ∨ p ∈ φ.vars := by
  unfold Vc.mkImp
  split <;> intro p hp
  · exact Or.inr hp
  · simp_all [Exp.vars]
  · simp only [Exp.vars, List.mem_append] at hp
    tauto

theorem mkAnd2_vars {a b : BExp} :
    ∀ p ∈ (Vc.mkAnd2 a b).vars, p ∈ a.vars ∨ p ∈ b.vars := by
  unfold Vc.mkAnd2
  intro p hp
  split at hp
  · exact Or.inr hp
  · split at hp
    · exact Or.inl hp
    · split at hp
      · simp [Exp.vars] at hp
      · split at hp
        · exact Or.inl hp
        · simp only [Exp.vars, List.mem_append] at hp
          tauto

theorem mkOr2_vars {a b : BExp} :
    ∀ p ∈ (Vc.mkOr2 a b).vars, p ∈ a.vars ∨ p ∈ b.vars := by
  unfold Vc.mkOr2
  intro p hp
  split at hp
  · exact Or.inr hp
  · split at hp
    · exact Or.inl hp
    · split at hp
      · simp [Exp.vars] at hp
      · split at hp
        · exact Or.inl hp
        · simp only [Exp.vars, List.mem_append] at hp
          tauto

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

theorem unFold_vars {a c : Ty} (op : UnOp a c) (e : Exp a) :
    ∀ p ∈ (Vc.unFold op e).vars, p ∈ e.vars := by
  cases op
  exact mkNot_vars

theorem binFold_vars {a b c : Ty} (op : BinOp a b c) (l : Exp a) (r : Exp b) :
    ∀ p ∈ (Vc.binFold op l r).vars, p ∈ l.vars ∨ p ∈ r.vars := by
  cases op <;>
    first
      | exact mkAnd2_vars
      | exact mkOr2_vars
      | exact mkImp_vars
      | (intro p hp
         simp only [Vc.binFold, Exp.vars, List.mem_append] at hp
         tauto)

theorem lower_vars : {t : Ty} → (e : Exp t) →
    ∀ p ∈ (Vc.lower e).vars, p ∈ e.vars
  | _, .litI _, p, hp => hp
  | _, .litB _, p, hp => hp
  | _, .var _ _, p, hp => hp
  | _, .blk _, p, hp => hp
  | _, .un op e, p, hp => by
      simp only [Exp.vars]
      exact lower_vars e p (unFold_vars op _ p hp)
  | _, .bin op l r, p, hp => by
      simp only [Exp.vars, List.mem_append]
      rcases binFold_vars op _ _ p hp with h | h
      · exact Or.inl (lower_vars l p h)
      · exact Or.inr (lower_vars r p h)
  | _, .tern op e₁ e₂ e₃, p, hp => by
      simp only [Vc.lower, Exp.vars, List.mem_append] at hp ⊢
      rcases hp with (h | h) | h
      · exact Or.inl (Or.inl (lower_vars e₁ p h))
      · exact Or.inl (Or.inr (lower_vars e₂ p h))
      · exact Or.inr (lower_vars e₃ p h)
  | _, .ite c th el, p, hp => by
      simp only [Exp.vars, List.mem_append]
      rcases mkIte_vars p hp with h | h | h
      · exact Or.inl (Or.inl (lower_vars c p h))
      · exact Or.inl (Or.inr (lower_vars th p h))
      · exact Or.inr (lower_vars el p h)

theorem mkNot_blkVars {a : BExp} :
    ∀ q ∈ (Vc.mkNot a).blkVars, q ∈ a.blkVars := by
  unfold Vc.mkNot
  split <;> intro q hq <;> simp_all [Exp.blkVars]

theorem mkImp_blkVars {g φ : BExp} :
    ∀ q ∈ (Vc.mkImp g φ).blkVars, q ∈ g.blkVars ∨ q ∈ φ.blkVars := by
  unfold Vc.mkImp
  split <;> intro q hq
  · exact Or.inr hq
  · simp_all [Exp.blkVars]
  · simp only [Exp.blkVars, List.mem_append] at hq
    tauto

theorem mkAnd2_blkVars {a b : BExp} :
    ∀ q ∈ (Vc.mkAnd2 a b).blkVars, q ∈ a.blkVars ∨ q ∈ b.blkVars := by
  unfold Vc.mkAnd2
  intro q hq
  split at hq
  · exact Or.inr hq
  · split at hq
    · exact Or.inl hq
    · split at hq
      · simp [Exp.blkVars] at hq
      · split at hq
        · exact Or.inl hq
        · simp only [Exp.blkVars, List.mem_append] at hq
          tauto

theorem mkOr2_blkVars {a b : BExp} :
    ∀ q ∈ (Vc.mkOr2 a b).blkVars, q ∈ a.blkVars ∨ q ∈ b.blkVars := by
  unfold Vc.mkOr2
  intro q hq
  split at hq
  · exact Or.inr hq
  · split at hq
    · exact Or.inl hq
    · split at hq
      · simp [Exp.blkVars] at hq
      · split at hq
        · exact Or.inl hq
        · simp only [Exp.blkVars, List.mem_append] at hq
          tauto

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

theorem unFold_blkVars {a c : Ty} (op : UnOp a c) (e : Exp a) :
    ∀ q ∈ (Vc.unFold op e).blkVars, q ∈ e.blkVars := by
  cases op
  exact mkNot_blkVars

theorem binFold_blkVars {a b c : Ty} (op : BinOp a b c)
    (l : Exp a) (r : Exp b) :
    ∀ q ∈ (Vc.binFold op l r).blkVars, q ∈ l.blkVars ∨ q ∈ r.blkVars := by
  cases op <;>
    first
      | exact mkAnd2_blkVars
      | exact mkOr2_blkVars
      | exact mkImp_blkVars
      | (intro q hq
         simp only [Vc.binFold, Exp.blkVars, List.mem_append] at hq
         tauto)

theorem lower_blkVars : {t : Ty} → (e : Exp t) →
    ∀ q ∈ (Vc.lower e).blkVars, q ∈ e.blkVars
  | _, .litI _, q, hq => hq
  | _, .litB _, q, hq => hq
  | _, .var _ _, q, hq => hq
  | _, .blk _, q, hq => hq
  | _, .un op e, q, hq => by
      simp only [Exp.blkVars]
      exact lower_blkVars e q (unFold_blkVars op _ q hq)
  | _, .bin op l r, q, hq => by
      simp only [Exp.blkVars, List.mem_append]
      rcases binFold_blkVars op _ _ q hq with h | h
      · exact Or.inl (lower_blkVars l q h)
      · exact Or.inr (lower_blkVars r q h)
  | _, .tern op e₁ e₂ e₃, q, hq => by
      simp only [Vc.lower, Exp.blkVars, List.mem_append] at hq ⊢
      rcases hq with (h | h) | h
      · exact Or.inl (Or.inl (lower_blkVars e₁ q h))
      · exact Or.inl (Or.inr (lower_blkVars e₂ q h))
      · exact Or.inr (lower_blkVars e₃ q h)
  | _, .ite c th el, q, hq => by
      simp only [Exp.blkVars, List.mem_append]
      rcases mkIte_blkVars q hq with h | h | h
      · exact Or.inl (Or.inl (lower_blkVars c q h))
      · exact Or.inl (Or.inr (lower_blkVars th q h))
      · exact Or.inr (lower_blkVars el q h)

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

/-! ## The unvisited-definition list -/

def cmdDefs (P : Program) (cs : List Cmd) : List DefExt.Def :=
  cs.filterMap (Vc.unguardedDef? P)

def unvisitedDefs (P : Program) (V : List Nat) :
    Nat → List Block → List DefExt.Def
  | _, [] => []
  | b, B :: Bs =>
      (if b ∈ V then [] else cmdDefs P B.cmds)
        ++ unvisitedDefs P V (b + 1) Bs

/-- The unguarded definitions of unvisited blocks, in program order. -/
def witnessDefs (P : Program) (V : List Nat) : List DefExt.Def :=
  unvisitedDefs P V 0 P.blocks

/-- The satisfying assignment built from a failing execution: σ, guards
from the visited list, then the definitional extension over the
unvisited definitions. -/
def witness (P : Program) (V : List Nat) (σ : State) : State :=
  DefExt.applyDefs (witnessDefs P V) (setBlockVars P V σ)

/-! ## Positions of extracted definitions -/

/-- `d` is the definition extracted from the command at `(b, i)`. -/
def WitnessDefAt (P : Program) (d : DefExt.Def) (b i : Nat) : Prop :=
  ∃ B c, P.block? b = some B ∧ B.cmds[i]? = some c
    ∧ Vc.unguardedDef? P c = some d

theorem unguardedDef?_eq_some {P : Program} {c : Cmd} {d : DefExt.Def}
    (h : Vc.unguardedDef? P c = some d) :
    (∃ t x arms, c = .phi t x arms ∧ d = ⟨t, x, Vc.phiRhs P t arms⟩)
      ∨ (∃ x e, c = .assign .map x e ∧ d = ⟨.map, x, Vc.lower e⟩) := by
  cases c with
  | phi t x arms => exact Or.inl ⟨t, x, arms, rfl, (Option.some.inj h).symm⟩
  | assign t x e =>
      cases t with
      | map => exact Or.inr ⟨x, e, rfl, (Option.some.inj h).symm⟩
      | int => cases h
      | bool => cases h
  | havoc t x => cases h
  | assume φ => cases h
  | assert r => cases h

theorem WitnessDefAt.target_defAt {P : Program} {d : DefExt.Def}
    {b i : Nat} (h : WitnessDefAt P d b i) : IsDefAt P d.target b i := by
  obtain ⟨B, c, hB, hc, hd⟩ := h
  rcases unguardedDef?_eq_some hd with ⟨t, x, arms, rfl, rfl⟩ | ⟨x, e, rfl, rfl⟩
  · exact ⟨B, _, hB, hc, rfl⟩
  · exact ⟨B, _, hB, hc, rfl⟩

/-- Every variable a definition's right-hand side reads is defined
lexicographically before the defining position: for phis by the arm
rule (a strictly earlier block), for map assignments by dominated uses
(same block earlier, or a dominator block). -/
theorem WitnessDefAt.rhsVars_before {P : Program}
    (huse : usesOK P = true) (hphi : phiOK P = true)
    {d : DefExt.Def} {b i : Nat} (h : WitnessDefAt P d b i) :
    ∀ p ∈ d.rhs.vars, ∀ e j, IsDefAt P p e j →
      posLt (e, j) (b, i) = true := by
  obtain ⟨B, c, hB, hc, hd⟩ := h
  rcases unguardedDef?_eq_some hd with ⟨t, x, arms, rfl, rfl⟩ | ⟨x, e0, rfl, rfl⟩
  · intro p hp e j hdef
    have := phi_src_lt huse hphi hB hc p hp e j hdef
    simp only [posLt, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    omega
  · intro p hp e j hdef
    have hu := usesOK_cmd huse hB hc
    simp only [cmdUsesOK] at hu
    exact useOK_before
      (List.all_eq_true.mp hu p (lower_vars e0 p hp)) e j hdef

/-- No definition reads its own target. -/
theorem WitnessDefAt.selfOK {P : Program}
    (huse : usesOK P = true) (hphi : phiOK P = true)
    {d : DefExt.Def} {b i : Nat} (h : WitnessDefAt P d b i) :
    DefExt.SelfOK d := by
  intro hmem
  have := h.rhsVars_before huse hphi d.target hmem b i h.target_defAt
  rw [posLt_irrefl] at this
  cases this

/-- Two definitions at lexicographically ordered positions satisfy the
generic no-later-write condition: SSA makes the targets distinct, and
`rhsVars_before` pins every right-hand-side variable strictly before
the earlier position - where the later definition cannot write. -/
theorem untouched_of_positions {P : Program}
    (hssa : ssaOK P = true) (huse : usesOK P = true) (hphi : phiOK P = true)
    {d d' : DefExt.Def} {b i b' i' : Nat}
    (hlex : posLt (b, i) (b', i') = true)
    (hd : WitnessDefAt P d b i) (hd' : WitnessDefAt P d' b' i') :
    DefExt.Untouched d d' := by
  have hdef' : IsDefAt P d'.target b' i' := hd'.target_defAt
  constructor
  · intro heq
    rw [heq] at hdef'
    obtain ⟨hb, hi⟩ := ssa_unique hssa hd.target_defAt hdef'
    subst hb
    subst hi
    rw [posLt_irrefl] at hlex
    cases hlex
  · intro hmem
    have hbefore := hd.rhsVars_before huse hphi d'.target hmem b' i' hdef'
    simp only [posLt, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq] at hlex hbefore
    omega

/-! ## Membership in the definition list -/

theorem cmdDefs_defAt {P : Program} {b : Nat} {B : Block}
    (hB : P.block? b = some B) {d : DefExt.Def}
    (hd : d ∈ cmdDefs P B.cmds) : ∃ i, WitnessDefAt P d b i := by
  rw [cmdDefs, List.mem_filterMap] at hd
  obtain ⟨c, hc, hcd⟩ := hd
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hc
  exact ⟨i, B, c, hB, hi, hcd⟩

theorem unvisitedDefs_defAt {P : Program} {V : List Nat} {d : DefExt.Def} :
    ∀ {k : Nat} {Bs : List Block}, (∀ m, Bs[m]? = P.blocks[k + m]?) →
      d ∈ unvisitedDefs P V k Bs →
      ∃ b, k ≤ b ∧ b ∉ V ∧ ∃ i, WitnessDefAt P d b i
  | _, [], _, hd => (List.not_mem_nil hd).elim
  | k, B :: Bs', hBs, hd => by
      rw [unvisitedDefs, List.mem_append] at hd
      rcases hd with hd | hd
      · have hB : P.block? k = some B := by
          have h0 := hBs 0
          rw [List.getElem?_cons_zero] at h0
          exact h0.symm
        split at hd
        · exact (List.not_mem_nil hd).elim
        · rename_i hkV
          obtain ⟨i, hAt⟩ := cmdDefs_defAt hB hd
          exact ⟨k, Nat.le_refl k, hkV, i, hAt⟩
      · have hBs' : ∀ m, Bs'[m]? = P.blocks[(k + 1) + m]? := fun m => by
          have h := hBs (m + 1)
          rwa [List.getElem?_cons_succ,
            show k + (m + 1) = (k + 1) + m by omega] at h
        obtain ⟨b, hkb, hbV, hex⟩ := unvisitedDefs_defAt hBs' hd
        exact ⟨b, by omega, hbV, hex⟩

theorem witnessDefAt_mem_unvisited {P : Program} {V : List Nat}
    {d : DefExt.Def} {b i : Nat}
    (hAt : WitnessDefAt P d b i) (hbV : b ∉ V) :
    ∀ {k : Nat} {Bs : List Block}, (∀ m, Bs[m]? = P.blocks[k + m]?) →
      k ≤ b → d ∈ unvisitedDefs P V k Bs
  | k, [], hBs, hkb => by
      obtain ⟨B, c, hB, -, -⟩ := hAt
      have hB' : P.blocks[b]? = some B := hB
      have h := hBs (b - k)
      rw [List.getElem?_nil, show k + (b - k) = b by omega, hB'] at h
      cases h
  | k, B' :: Bs', hBs, hkb => by
      rw [unvisitedDefs, List.mem_append]
      by_cases hbk : b = k
      · left
        subst hbk
        rw [if_neg hbV]
        obtain ⟨B, c, hB, hc, hcd⟩ := hAt
        have hB0 : P.block? b = some B' := by
          have h0 := hBs 0
          rw [List.getElem?_cons_zero] at h0
          exact h0.symm
        obtain rfl : B = B' := Option.some.inj (hB.symm.trans hB0)
        rw [cmdDefs, List.mem_filterMap]
        exact ⟨c, List.mem_of_getElem? hc, hcd⟩
      · right
        have hBs' : ∀ m, Bs'[m]? = P.blocks[(k + 1) + m]? := fun m => by
          have h := hBs (m + 1)
          rwa [List.getElem?_cons_succ,
            show k + (m + 1) = (k + 1) + m by omega] at h
        exact witnessDefAt_mem_unvisited hAt hbV hBs' (by omega)

private theorem blocks_shift (P : Program) :
    ∀ m, P.blocks[m]? = P.blocks[0 + m]? :=
  fun m => by rw [Nat.zero_add]

theorem witnessDefs_defAt {P : Program} {V : List Nat} {d : DefExt.Def}
    (hd : d ∈ witnessDefs P V) :
    ∃ b, b ∉ V ∧ ∃ i, WitnessDefAt P d b i := by
  obtain ⟨b, -, hbV, hex⟩ := unvisitedDefs_defAt (blocks_shift P) hd
  exact ⟨b, hbV, hex⟩

theorem witnessDefAt_mem_witnessDefs {P : Program} {V : List Nat}
    {d : DefExt.Def} {b i : Nat}
    (hAt : WitnessDefAt P d b i) (hbV : b ∉ V) : d ∈ witnessDefs P V :=
  witnessDefAt_mem_unvisited hAt hbV (blocks_shift P) (Nat.zero_le b)

/-! ## The ordering obligation -/

theorem pairwise_cmdDefs {P : Program}
    (hssa : ssaOK P = true) (huse : usesOK P = true) (hphi : phiOK P = true)
    {b : Nat} {B : Block} (hB : P.block? b = some B) :
    (cmdDefs P B.cmds).Pairwise DefExt.Untouched := by
  rw [cmdDefs, List.pairwise_filterMap, List.pairwise_iff_get]
  intro i j hij d hd d' hd'
  have hci : B.cmds[i.1]? = some (B.cmds.get i) :=
    List.getElem?_eq_getElem i.isLt
  have hcj : B.cmds[j.1]? = some (B.cmds.get j) :=
    List.getElem?_eq_getElem j.isLt
  have hAt : WitnessDefAt P d b i.1 := ⟨B, _, hB, hci, hd⟩
  have hAt' : WitnessDefAt P d' b j.1 := ⟨B, _, hB, hcj, hd'⟩
  have hij' : i.1 < j.1 := hij
  refine untouched_of_positions hssa huse hphi ?_ hAt hAt'
  simp [posLt, hij']

theorem pairwise_unvisitedDefs {P : Program} {V : List Nat}
    (hssa : ssaOK P = true) (huse : usesOK P = true) (hphi : phiOK P = true) :
    ∀ {k : Nat} {Bs : List Block}, (∀ m, Bs[m]? = P.blocks[k + m]?) →
      (unvisitedDefs P V k Bs).Pairwise DefExt.Untouched
  | _, [], _ => List.Pairwise.nil
  | k, B :: Bs', hBs => by
      have hB : P.block? k = some B := by
        have h0 := hBs 0
        rw [List.getElem?_cons_zero] at h0
        exact h0.symm
      have hBs' : ∀ m, Bs'[m]? = P.blocks[(k + 1) + m]? := fun m => by
        have h := hBs (m + 1)
        rwa [List.getElem?_cons_succ,
          show k + (m + 1) = (k + 1) + m by omega] at h
      rw [unvisitedDefs, List.pairwise_append]
      refine ⟨?_, pairwise_unvisitedDefs hssa huse hphi hBs', ?_⟩
      · split
        · exact List.Pairwise.nil
        · exact pairwise_cmdDefs hssa huse hphi hB
      · intro d hd d' hd'
        obtain ⟨b', hkb', -, i', hAt'⟩ := unvisitedDefs_defAt hBs' hd'
        split at hd
        · exact (List.not_mem_nil hd).elim
        · obtain ⟨i, hAt⟩ := cmdDefs_defAt hB hd
          refine untouched_of_positions hssa huse hphi ?_ hAt hAt'
          have hkb : k < b' := by omega
          simp [posLt, hkb]

/-- The unvisited definitions form an ordered definition list ("acyclic
with distinct left-hand sides"). -/
theorem orderedDefs_witnessDefs {P : Program} {V : List Nat}
    (hssa : ssaOK P = true) (huse : usesOK P = true)
    (hphi : phiOK P = true) :
    DefExt.OrderedDefs (witnessDefs P V) := by
  refine ⟨?_, pairwise_unvisitedDefs hssa huse hphi (blocks_shift P)⟩
  intro d hd
  obtain ⟨b, -, i, hAt⟩ := witnessDefs_defAt hd
  exact hAt.selfOK huse hphi

/-! ## The target inventory

The extension's write set `W`, characterized: exactly the registers
with an unguarded definition in an unvisited block. The negative form
is what the robustness instances use - a register whose every
definition is in a visited block is outside `W`. -/

theorem target_defAt {P : Program} {V : List Nat} {tx : Ty × Nat}
    (hx : tx ∈ DefExt.targets (witnessDefs P V)) :
    ∃ b, b ∉ V ∧ ∃ i, IsDefAt P tx b i := by
  obtain ⟨d, hd, rfl⟩ := DefExt.mem_targets.mp hx
  obtain ⟨b, hbV, i, hAt⟩ := witnessDefs_defAt hd
  exact ⟨b, hbV, i, hAt.target_defAt⟩

theorem not_target_of_visited {P : Program} {V : List Nat} {tx : Ty × Nat}
    (h : ∀ b i, IsDefAt P tx b i → b ∈ V) :
    tx ∉ DefExt.targets (witnessDefs P V) := fun hx => by
  obtain ⟨b, hbV, i, hdef⟩ := target_defAt hx
  exact hbV (h b i hdef)

/-! ## Chain selection for visited phis -/

theorem lookupArm_cons {q s' p : Nat} {rest : List (Nat × Nat)} :
    lookupArm ((q, s') :: rest) p
      = if p = q then some s' else lookupArm rest p := by
  by_cases h : p = q
  · simp [lookupArm, List.lookup, h]
  · simp only [lookupArm, List.lookup, if_neg h]
    rw [show (p == q) = false from beq_eq_false_iff_ne.mpr h]

theorem phiChain_select {P : Program} {V : List Nat} {w : State}
    (hblk : ∀ q, q < P.blocks.length → w.blks q = decide (q ∈ V))
    (hentryV : P.entry ∈ V) {t : Ty} :
    ∀ (a : Nat × Nat) (rest : List (Nat × Nat)) {p src : Nat},
      lookupArm (a :: rest) p = some src → p ∈ V →
      (∀ x ∈ a :: rest, x.1 < P.blocks.length) →
      (∀ x ∈ a :: rest, x.1 ∈ V → x.1 = p) →
      (Vc.phiChain P t a rest).eval w = w.regs t src := by
  intro a rest
  induction rest generalizing a with
  | nil =>
      obtain ⟨q, s'⟩ := a
      intro p src harm hpV hlt huniq
      rw [lookupArm_cons] at harm
      by_cases hpq : p = q
      · rw [if_pos hpq] at harm
        obtain rfl := Option.some.inj harm
        simp [Vc.phiChain, Exp.eval]
      · rw [if_neg hpq] at harm
        simp [lookupArm, List.lookup] at harm
  | cons a' rest' ih =>
      obtain ⟨q, s'⟩ := a
      intro p src harm hpV hlt huniq
      have hguard : (Vc.guardOf P q).eval w = decide (q ∈ V) := by
        unfold Vc.guardOf
        split
        · rename_i hq
          rw [hq]
          simp [Exp.eval, hentryV]
        · simpa [Exp.eval] using hblk q (hlt (q, s') (List.mem_cons_self ..))
      rw [lookupArm_cons] at harm
      simp only [Vc.phiChain, Vc.eval_mkIte, hguard]
      by_cases hpq : p = q
      · rw [if_pos hpq] at harm
        obtain rfl := Option.some.inj harm
        have hqV : q ∈ V := hpq ▸ hpV
        simp [hqV, Exp.eval]
      · rw [if_neg hpq] at harm
        have hqV : q ∉ V := fun hq =>
          hpq ((huniq (q, s') (List.mem_cons_self ..) hq).symm)
        simp only [hqV, decide_false, Bool.false_eq_true, if_false]
        exact ih a' harm hpV
          (fun x hx => hlt x (List.mem_cons_of_mem _ hx))
          (fun x hx => huniq x (List.mem_cons_of_mem _ hx))

theorem phiRhs_select {P : Program} {V : List Nat} {w : State}
    (hblk : ∀ q, q < P.blocks.length → w.blks q = decide (q ∈ V))
    (hentryV : P.entry ∈ V) {t : Ty} {arms : PhiArms} {p src : Nat}
    (harm : lookupArm arms p = some src) (hpV : p ∈ V)
    (hlt : ∀ x ∈ arms, x.1 < P.blocks.length)
    (huniq : ∀ x ∈ arms, x.1 ∈ V → x.1 = p) :
    (Vc.phiRhs P t arms).eval w = w.regs t src := by
  cases arms with
  | nil => simp [lookupArm, List.lookup] at harm
  | cons a rest =>
      exact phiChain_select hblk hentryV a rest harm hpV hlt huniq

end Ttac
