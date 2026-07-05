import Batteries.Data.List.Pairwise
import Ttac.DefExt
import Ttac.VcTrace

/-!
# The witness as a definitional extension

A failing execution's final state σ, with the guard component set from
the visited-block list, satisfies every expected constraint except the
*unguarded phi equations of unvisited joins* (their targets hold junk).
Those equations are exactly a definition list in the sense of
`Ttac.DefExt`: `witnessDefs` extracts them in program order, and this
file discharges the generic lemma's two obligations for it -

- **ordering** (`orderedDefs_witnessDefs`): SSA gives pairwise-distinct
  targets, and the phi-arm rule (every arm source is defined in a
  strictly earlier block, `d ≤ p < b`) gives the no-later-read
  condition; program order refines both to the list order.
- **target inventory** (`intTarget_defAt`/`boolTarget_defAt`): a target
  is precisely a register phi-defined in an unvisited block, which is
  what the robustness instances in `VcSound` reason against.

The witness itself is then just `applyDefs` over this list
(`witness`); no bespoke replay machinery remains. Guards live in their
own `State.blks` component, written once by `setBlockVars` and never
touched by the extension (definitions only write program registers).

The chain-selection lemmas at the bottom (`phiRhsI_select`/
`phiRhsB_select`) are the semantic content of the phi constraint for
*visited* joins - which ITE arm survives under the guard assignment -
and are consumed by the robustness instance for visited phi equations.
-/

namespace Ttac

/-! ## Guard initialization -/

/-- Visited blocks true, the synthetic exit guard (index
`P.blocks.length`) true, everything else false. -/
def setBlockVars (P : Program) (V : List Nat) (σ : State) : State :=
  { σ with blks := fun q => decide (q ∈ V ∨ q = P.blocks.length) }

@[simp] theorem setBlockVars_ints (P : Program) (V : List Nat) (σ : State) :
    (setBlockVars P V σ).ints = σ.ints := rfl

@[simp] theorem setBlockVars_bools (P : Program) (V : List Nat) (σ : State) :
    (setBlockVars P V σ).bools = σ.bools := rfl

theorem setBlockVars_blk (P : Program) (V : List Nat) (σ : State)
    {q : Nat} (hq : q < P.blocks.length) :
    (setBlockVars P V σ).blks q = decide (q ∈ V) := by
  simp only [setBlockVars]
  by_cases h : q ∈ V <;> (simp [h]; try omega)

theorem setBlockVars_exit (P : Program) (V : List Nat) (σ : State) :
    (setBlockVars P V σ).blks P.blocks.length = true := by
  simp [setBlockVars]

/-! ## Variable inventories of phi right-hand sides -/

theorem guardOf_intVars (P : Program) (q : Nat) :
    (Vc.guardOf P q).intVars = [] := by
  unfold Vc.guardOf; split <;> rfl

theorem guardOf_boolVars (P : Program) (q : Nat) :
    (Vc.guardOf P q).boolVars = [] := by
  unfold Vc.guardOf; split <;> rfl

theorem mkIteI_intVars {c : BExp} {t e : IExp} :
    ∀ r ∈ (Vc.mkIteI c t e).intVars,
      r ∈ c.intVars ∨ r ∈ t.intVars ∨ r ∈ e.intVars := by
  intro r hr
  unfold Vc.mkIteI at hr
  split at hr
  · exact Or.inr (Or.inl hr)
  · split at hr
    · exact Or.inr (Or.inl hr)
    · exact Or.inr (Or.inr hr)
    · simp only [IExp.intVars, List.mem_append] at hr
      tauto

theorem mkIteI_boolVars {c : BExp} {t e : IExp} :
    ∀ r ∈ (Vc.mkIteI c t e).boolVars,
      r ∈ c.boolVars ∨ r ∈ t.boolVars ∨ r ∈ e.boolVars := by
  intro r hr
  unfold Vc.mkIteI at hr
  split at hr
  · exact Or.inr (Or.inl hr)
  · split at hr
    · exact Or.inr (Or.inl hr)
    · exact Or.inr (Or.inr hr)
    · simp only [IExp.boolVars, List.mem_append] at hr
      tauto

theorem mkNot_boolVars {a : BExp} :
    ∀ r ∈ (Vc.mkNot a).boolVars, r ∈ a.boolVars := by
  unfold Vc.mkNot
  split <;> intro r hr <;> simp_all [BExp.boolVars]

theorem mkIteB_intVars {c t e : BExp} :
    ∀ r ∈ (Vc.mkIteB c t e).intVars,
      r ∈ c.intVars ∨ r ∈ t.intVars ∨ r ∈ e.intVars := by
  intro r hr
  unfold Vc.mkIteB at hr
  split at hr
  · exact Or.inr (Or.inl hr)
  · split at hr
    · exact Or.inr (Or.inl hr)
    · exact Or.inr (Or.inr hr)
    · exact Or.inl hr
    · unfold Vc.mkNot at hr
      split at hr <;> simp_all [BExp.intVars]
    · simp only [BExp.intVars, List.mem_append] at hr
      tauto

theorem mkIteB_boolVars {c t e : BExp} :
    ∀ r ∈ (Vc.mkIteB c t e).boolVars,
      r ∈ c.boolVars ∨ r ∈ t.boolVars ∨ r ∈ e.boolVars := by
  intro r hr
  unfold Vc.mkIteB at hr
  split at hr
  · exact Or.inr (Or.inl hr)
  · split at hr
    · exact Or.inr (Or.inl hr)
    · exact Or.inr (Or.inr hr)
    · exact Or.inl hr
    · exact Or.inl (mkNot_boolVars _ hr)
    · simp only [BExp.boolVars, List.mem_append] at hr
      tauto

theorem phiChainI_intVars {P : Program} :
    ∀ (a : Nat × Nat) (rest : List (Nat × Nat)),
      ∀ r ∈ (Vc.phiChainI P a rest).intVars, ∃ q, (q, r) ∈ a :: rest
  | (q0, s0), [], r, hr => by
      simp only [Vc.phiChainI, IExp.intVars] at hr
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨q0, List.mem_cons_self ..⟩
  | (q0, s0), a' :: rest', r, hr => by
      rcases mkIteI_intVars r hr with hg | hs | ht
      · rw [guardOf_intVars] at hg; cases hg
      · simp only [IExp.intVars] at hs
        obtain rfl := List.mem_singleton.mp hs
        exact ⟨q0, List.mem_cons_self ..⟩
      · obtain ⟨q, hq⟩ := phiChainI_intVars a' rest' r ht
        exact ⟨q, List.mem_cons_of_mem _ hq⟩

theorem phiChainI_boolVars {P : Program} :
    ∀ (a : Nat × Nat) (rest : List (Nat × Nat)),
      ∀ r ∈ (Vc.phiChainI P a rest).boolVars, False
  | (q0, s0), [], r, hr => by
      simp only [Vc.phiChainI, IExp.boolVars] at hr
      cases hr
  | (q0, s0), a' :: rest', r, hr => by
      rcases mkIteI_boolVars r hr with hg | hs | ht
      · rw [guardOf_boolVars] at hg; cases hg
      · simp only [IExp.boolVars] at hs; cases hs
      · exact phiChainI_boolVars a' rest' r ht

theorem phiRhsI_intVars {P : Program} {arms : PhiArms} :
    ∀ r ∈ (Vc.phiRhsI P arms).intVars, ∃ q, (q, r) ∈ arms := by
  cases arms with
  | nil => intro r hr; cases hr
  | cons a rest => exact phiChainI_intVars a rest

theorem phiRhsI_boolVars {P : Program} {arms : PhiArms} :
    ∀ r ∈ (Vc.phiRhsI P arms).boolVars, False := by
  cases arms with
  | nil => intro r hr; cases hr
  | cons a rest => exact phiChainI_boolVars a rest

theorem phiChainB_intVars {P : Program} :
    ∀ (a : Nat × Nat) (rest : List (Nat × Nat)),
      ∀ r ∈ (Vc.phiChainB P a rest).intVars, False
  | (q0, s0), [], r, hr => by
      simp only [Vc.phiChainB, BExp.intVars] at hr
      cases hr
  | (q0, s0), a' :: rest', r, hr => by
      rcases mkIteB_intVars r hr with hg | hs | ht
      · rw [show (Vc.guardOf P q0).intVars = [] from by
          unfold Vc.guardOf; split <;> rfl] at hg
        cases hg
      · simp only [BExp.intVars] at hs; cases hs
      · exact phiChainB_intVars a' rest' r ht

theorem phiChainB_boolVars {P : Program} :
    ∀ (a : Nat × Nat) (rest : List (Nat × Nat)),
      ∀ r ∈ (Vc.phiChainB P a rest).boolVars, ∃ q, (q, r) ∈ a :: rest
  | (q0, s0), [], r, hr => by
      simp only [Vc.phiChainB, BExp.boolVars] at hr
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨q0, List.mem_cons_self ..⟩
  | (q0, s0), a' :: rest', r, hr => by
      rcases mkIteB_boolVars r hr with hg | hs | ht
      · rw [guardOf_boolVars] at hg; cases hg
      · simp only [BExp.boolVars] at hs
        obtain rfl := List.mem_singleton.mp hs
        exact ⟨q0, List.mem_cons_self ..⟩
      · obtain ⟨q, hq⟩ := phiChainB_boolVars a' rest' r ht
        exact ⟨q, List.mem_cons_of_mem _ hq⟩

theorem phiRhsB_intVars {P : Program} {arms : PhiArms} :
    ∀ r ∈ (Vc.phiRhsB P arms).intVars, False := by
  cases arms with
  | nil => intro r hr; cases hr
  | cons a rest => exact phiChainB_intVars a rest

theorem phiRhsB_boolVars {P : Program} {arms : PhiArms} :
    ∀ r ∈ (Vc.phiRhsB P arms).boolVars, ∃ q, (q, r) ∈ arms := by
  cases arms with
  | nil => intro r hr; cases hr
  | cons a rest => exact phiChainB_boolVars a rest

/-! ## The phi-arm rule, in dependence form

Every variable a phi right-hand side reads is defined strictly below
the phi's block: the checker's arm-use rule gives `d ≤ p` and the phi
shape gives `p < b`. This single fact drives both ordering obligations
below. -/

theorem phi_srcI_lt {P : Program}
    (huse : usesOK P = true) (hphi : phiOK P = true)
    {b : Nat} {B : Block} {i y : Nat} {arms : PhiArms}
    (hB : P.block? b = some B) (hc : B.cmds[i]? = some (.phiI y arms)) :
    ∀ r ∈ (Vc.phiRhsI P arms).intVars,
      ∀ d j, IsDefAt P cmdIntDef r d j → d < b := by
  have harms : phiArmsOK P b arms = true :=
    (phiOK_at hphi hB (List.mem_of_getElem? hc)).1 y arms rfl
  have hu := usesOK_cmd huse hB hc
  simp only [cmdUsesOK] at hu
  intro r hr d j hd
  obtain ⟨q, hq⟩ := phiRhsI_intVars r hr
  have hle := armUseOK_le (List.all_eq_true.mp hu (q, r) hq) d j hd
  have := phiArm_lt harms hq
  omega

theorem phi_srcB_lt {P : Program}
    (huse : usesOK P = true) (hphi : phiOK P = true)
    {b : Nat} {B : Block} {i y : Nat} {arms : PhiArms}
    (hB : P.block? b = some B) (hc : B.cmds[i]? = some (.phiB y arms)) :
    ∀ r ∈ (Vc.phiRhsB P arms).boolVars,
      ∀ d j, IsDefAt P cmdBoolDef r d j → d < b := by
  have harms : phiArmsOK P b arms = true :=
    (phiOK_at hphi hB (List.mem_of_getElem? hc)).2 y arms rfl
  have hu := usesOK_cmd huse hB hc
  simp only [cmdUsesOK] at hu
  intro r hr d j hd
  obtain ⟨q, hq⟩ := phiRhsB_boolVars r hr
  have hle := armUseOK_le (List.all_eq_true.mp hu (q, r) hq) d j hd
  have := phiArm_lt harms hq
  omega

/-! ## The unvisited-phi definition list -/

/-- The definition a phi command contributes; `none` for anything else.
The right-hand side is the *same* `phiRhsI`/`phiRhsB` term the expected
phi constraint uses, so a definition's `toConstraint` is literally the
constraint - `sat_extend`'s second disjunct needs no reasoning. -/
def phiDef? (P : Program) : Cmd → Option DefExt.Def
  | .phiI x arms => some (.defI x (Vc.phiRhsI P arms))
  | .phiB x arms => some (.defB x (Vc.phiRhsB P arms))
  | _ => none

def phiDefs (P : Program) (cs : List Cmd) : List DefExt.Def :=
  cs.filterMap (phiDef? P)

def unvisitedPhiDefs (P : Program) (V : List Nat) :
    Nat → List Block → List DefExt.Def
  | _, [] => []
  | b, B :: Bs =>
      (if b ∈ V then [] else phiDefs P B.cmds)
        ++ unvisitedPhiDefs P V (b + 1) Bs

/-- The phi definitions of unvisited blocks, in program order. -/
def witnessDefs (P : Program) (V : List Nat) : List DefExt.Def :=
  unvisitedPhiDefs P V 0 P.blocks

/-- The satisfying assignment built from a failing execution: σ, guards
from the visited list, then the definitional extension over the
unvisited phis. -/
def witness (P : Program) (V : List Nat) (σ : State) : State :=
  DefExt.applyDefs (witnessDefs P V) (setBlockVars P V σ)

/-! ## Positions of extracted definitions -/

/-- `d` is the definition extracted from the phi command at `(b, i)`. -/
def PhiDefAt (P : Program) (d : DefExt.Def) (b i : Nat) : Prop :=
  ∃ B c, P.block? b = some B ∧ B.cmds[i]? = some c ∧ phiDef? P c = some d

theorem phiDef?_eq_some {P : Program} {c : Cmd} {d : DefExt.Def}
    (h : phiDef? P c = some d) :
    (∃ x arms, c = .phiI x arms ∧ d = .defI x (Vc.phiRhsI P arms))
      ∨ (∃ x arms, c = .phiB x arms ∧ d = .defB x (Vc.phiRhsB P arms)) := by
  cases c <;> simp only [phiDef?, Option.some.injEq, reduceCtorEq] at h
  case phiI x arms => exact Or.inl ⟨x, arms, rfl, h.symm⟩
  case phiB x arms => exact Or.inr ⟨x, arms, rfl, h.symm⟩

theorem PhiDefAt.intTarget_defAt {P : Program} {d : DefExt.Def} {b i : Nat}
    (h : PhiDefAt P d b i) {x : Nat} (hx : d.intTarget? = some x) :
    IsDefAt P cmdIntDef x b i := by
  obtain ⟨B, c, hB, hc, hd⟩ := h
  rcases phiDef?_eq_some hd with ⟨y, arms, rfl, rfl⟩ | ⟨y, arms, rfl, rfl⟩
  · obtain rfl : y = x := Option.some.inj hx
    exact ⟨B, _, hB, hc, rfl⟩
  · cases hx

theorem PhiDefAt.boolTarget_defAt {P : Program} {d : DefExt.Def} {b i : Nat}
    (h : PhiDefAt P d b i) {x : Nat} (hx : d.boolTarget? = some x) :
    IsDefAt P cmdBoolDef x b i := by
  obtain ⟨B, c, hB, hc, hd⟩ := h
  rcases phiDef?_eq_some hd with ⟨y, arms, rfl, rfl⟩ | ⟨y, arms, rfl, rfl⟩
  · cases hx
  · obtain rfl : y = x := Option.some.inj hx
    exact ⟨B, _, hB, hc, rfl⟩

theorem PhiDefAt.rhsIntVars_lt {P : Program}
    (huse : usesOK P = true) (hphi : phiOK P = true)
    {d : DefExt.Def} {b i : Nat} (h : PhiDefAt P d b i) :
    ∀ r ∈ d.rhsIntVars, ∀ e j, IsDefAt P cmdIntDef r e j → e < b := by
  obtain ⟨B, c, hB, hc, hd⟩ := h
  rcases phiDef?_eq_some hd with ⟨y, arms, rfl, rfl⟩ | ⟨y, arms, rfl, rfl⟩
  · exact phi_srcI_lt huse hphi hB hc
  · intro r hr
    exact (phiRhsB_intVars r hr).elim

theorem PhiDefAt.rhsBoolVars_lt {P : Program}
    (huse : usesOK P = true) (hphi : phiOK P = true)
    {d : DefExt.Def} {b i : Nat} (h : PhiDefAt P d b i) :
    ∀ r ∈ d.rhsBoolVars, ∀ e j, IsDefAt P cmdBoolDef r e j → e < b := by
  obtain ⟨B, c, hB, hc, hd⟩ := h
  rcases phiDef?_eq_some hd with ⟨y, arms, rfl, rfl⟩ | ⟨y, arms, rfl, rfl⟩
  · intro r hr
    exact (phiRhsI_boolVars r hr).elim
  · exact phi_srcB_lt huse hphi hB hc

/-- No phi reads its own target: the right-hand side's variables are
defined strictly below the phi's block, the target at it. -/
theorem PhiDefAt.selfOK {P : Program}
    (huse : usesOK P = true) (hphi : phiOK P = true)
    {d : DefExt.Def} {b i : Nat} (h : PhiDefAt P d b i) :
    DefExt.SelfOK d := by
  constructor
  · intro x hx hxin
    have := h.rhsIntVars_lt huse hphi x hxin b i (h.intTarget_defAt hx)
    omega
  · intro x hx hxin
    have := h.rhsBoolVars_lt huse hphi x hxin b i (h.boolTarget_defAt hx)
    omega

/-- Two phi definitions at lexicographically ordered positions satisfy
the generic no-later-write condition: SSA makes the targets distinct,
and the arm rule pins every right-hand-side variable strictly below the
earlier position's block - where the later definition cannot write. -/
theorem untouched_of_positions {P : Program}
    (hssa : ssaOK P = true) (huse : usesOK P = true) (hphi : phiOK P = true)
    {d d' : DefExt.Def} {b i b' i' : Nat}
    (hlex : b < b' ∨ (b = b' ∧ i < i'))
    (hd : PhiDefAt P d b i) (hd' : PhiDefAt P d' b' i') :
    DefExt.Untouched d d' := by
  constructor
  · intro x hx'
    have hdef' : IsDefAt P cmdIntDef x b' i' := hd'.intTarget_defAt hx'
    constructor
    · intro hx
      obtain ⟨hb, hi⟩ := ssa_unique_int hssa (hd.intTarget_defAt hx) hdef'
      omega
    · intro hr
      have := hd.rhsIntVars_lt huse hphi x hr b' i' hdef'
      omega
  · intro x hx'
    have hdef' : IsDefAt P cmdBoolDef x b' i' := hd'.boolTarget_defAt hx'
    constructor
    · intro hx
      obtain ⟨hb, hi⟩ := ssa_unique_bool hssa (hd.boolTarget_defAt hx) hdef'
      omega
    · intro hr
      have := hd.rhsBoolVars_lt huse hphi x hr b' i' hdef'
      omega

/-! ## Membership in the definition list -/

theorem phiDefs_defAt {P : Program} {b : Nat} {B : Block}
    (hB : P.block? b = some B) {d : DefExt.Def}
    (hd : d ∈ phiDefs P B.cmds) : ∃ i, PhiDefAt P d b i := by
  rw [phiDefs, List.mem_filterMap] at hd
  obtain ⟨c, hc, hcd⟩ := hd
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hc
  exact ⟨i, B, c, hB, hi, hcd⟩

theorem unvisitedPhiDefs_defAt {P : Program} {V : List Nat} {d : DefExt.Def} :
    ∀ {k : Nat} {Bs : List Block}, (∀ m, Bs[m]? = P.blocks[k + m]?) →
      d ∈ unvisitedPhiDefs P V k Bs →
      ∃ b, k ≤ b ∧ b ∉ V ∧ ∃ i, PhiDefAt P d b i
  | _, [], _, hd => (List.not_mem_nil hd).elim
  | k, B :: Bs', hBs, hd => by
      rw [unvisitedPhiDefs, List.mem_append] at hd
      rcases hd with hd | hd
      · have hB : P.block? k = some B := by
          have h0 := hBs 0
          rw [List.getElem?_cons_zero] at h0
          exact h0.symm
        split at hd
        · exact (List.not_mem_nil hd).elim
        · rename_i hkV
          obtain ⟨i, hAt⟩ := phiDefs_defAt hB hd
          exact ⟨k, Nat.le_refl k, hkV, i, hAt⟩
      · have hBs' : ∀ m, Bs'[m]? = P.blocks[(k + 1) + m]? := fun m => by
          have h := hBs (m + 1)
          rwa [List.getElem?_cons_succ,
            show k + (m + 1) = (k + 1) + m by omega] at h
        obtain ⟨b, hkb, hbV, hex⟩ := unvisitedPhiDefs_defAt hBs' hd
        exact ⟨b, by omega, hbV, hex⟩

theorem phiDefAt_mem_unvisited {P : Program} {V : List Nat}
    {d : DefExt.Def} {b i : Nat}
    (hAt : PhiDefAt P d b i) (hbV : b ∉ V) :
    ∀ {k : Nat} {Bs : List Block}, (∀ m, Bs[m]? = P.blocks[k + m]?) →
      k ≤ b → d ∈ unvisitedPhiDefs P V k Bs
  | k, [], hBs, hkb => by
      obtain ⟨B, c, hB, -, -⟩ := hAt
      have hB' : P.blocks[b]? = some B := hB
      have h := hBs (b - k)
      rw [List.getElem?_nil, show k + (b - k) = b by omega, hB'] at h
      cases h
  | k, B' :: Bs', hBs, hkb => by
      rw [unvisitedPhiDefs, List.mem_append]
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
        rw [phiDefs, List.mem_filterMap]
        exact ⟨c, List.mem_of_getElem? hc, hcd⟩
      · right
        have hBs' : ∀ m, Bs'[m]? = P.blocks[(k + 1) + m]? := fun m => by
          have h := hBs (m + 1)
          rwa [List.getElem?_cons_succ,
            show k + (m + 1) = (k + 1) + m by omega] at h
        exact phiDefAt_mem_unvisited hAt hbV hBs' (by omega)

private theorem blocks_shift (P : Program) :
    ∀ m, P.blocks[m]? = P.blocks[0 + m]? :=
  fun m => by rw [Nat.zero_add]

theorem witnessDefs_defAt {P : Program} {V : List Nat} {d : DefExt.Def}
    (hd : d ∈ witnessDefs P V) : ∃ b, b ∉ V ∧ ∃ i, PhiDefAt P d b i := by
  obtain ⟨b, -, hbV, hex⟩ := unvisitedPhiDefs_defAt (blocks_shift P) hd
  exact ⟨b, hbV, hex⟩

theorem phiDefAt_mem_witnessDefs {P : Program} {V : List Nat}
    {d : DefExt.Def} {b i : Nat}
    (hAt : PhiDefAt P d b i) (hbV : b ∉ V) : d ∈ witnessDefs P V :=
  phiDefAt_mem_unvisited hAt hbV (blocks_shift P) (Nat.zero_le b)

/-! ## The ordering obligation -/

theorem pairwise_phiDefs {P : Program}
    (hssa : ssaOK P = true) (huse : usesOK P = true) (hphi : phiOK P = true)
    {b : Nat} {B : Block} (hB : P.block? b = some B) :
    (phiDefs P B.cmds).Pairwise DefExt.Untouched := by
  rw [phiDefs, List.pairwise_filterMap, List.pairwise_iff_get]
  intro i j hij d hd d' hd'
  have hci : B.cmds[i.1]? = some (B.cmds.get i) :=
    List.getElem?_eq_getElem i.isLt
  have hcj : B.cmds[j.1]? = some (B.cmds.get j) :=
    List.getElem?_eq_getElem j.isLt
  have hAt : PhiDefAt P d b i.1 := ⟨B, _, hB, hci, hd⟩
  have hAt' : PhiDefAt P d' b j.1 := ⟨B, _, hB, hcj, hd'⟩
  exact untouched_of_positions hssa huse hphi (Or.inr ⟨rfl, hij⟩) hAt hAt'

theorem pairwise_unvisitedPhiDefs {P : Program} {V : List Nat}
    (hssa : ssaOK P = true) (huse : usesOK P = true) (hphi : phiOK P = true) :
    ∀ {k : Nat} {Bs : List Block}, (∀ m, Bs[m]? = P.blocks[k + m]?) →
      (unvisitedPhiDefs P V k Bs).Pairwise DefExt.Untouched
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
      rw [unvisitedPhiDefs, List.pairwise_append]
      refine ⟨?_, pairwise_unvisitedPhiDefs hssa huse hphi hBs', ?_⟩
      · split
        · exact List.Pairwise.nil
        · exact pairwise_phiDefs hssa huse hphi hB
      · intro d hd d' hd'
        obtain ⟨b', hkb', -, i', hAt'⟩ := unvisitedPhiDefs_defAt hBs' hd'
        split at hd
        · exact (List.not_mem_nil hd).elim
        · obtain ⟨i, hAt⟩ := phiDefs_defAt hB hd
          exact untouched_of_positions hssa huse hphi
            (Or.inl (by omega)) hAt hAt'

/-- The unvisited phis form an ordered definition list: what your
one-paragraph proof calls "acyclic with distinct left-hand sides". -/
theorem orderedDefs_witnessDefs {P : Program} {V : List Nat}
    (hssa : ssaOK P = true) (huse : usesOK P = true)
    (hphi : phiOK P = true) :
    DefExt.OrderedDefs (witnessDefs P V) := by
  refine ⟨?_, pairwise_unvisitedPhiDefs hssa huse hphi (blocks_shift P)⟩
  intro d hd
  obtain ⟨b, -, i, hAt⟩ := witnessDefs_defAt hd
  exact hAt.selfOK huse hphi

/-! ## The target inventory

The extension's write set `W`, characterized: exactly the registers
phi-defined in unvisited blocks. The negative form is what the
robustness instances use - a register whose every definition is in a
visited block is outside `W`. -/

theorem intTarget_defAt {P : Program} {V : List Nat} {x : Nat}
    (hx : x ∈ DefExt.intTargets (witnessDefs P V)) :
    ∃ b, b ∉ V ∧ ∃ i, IsDefAt P cmdIntDef x b i := by
  obtain ⟨d, hd, htgt⟩ := DefExt.mem_intTargets.mp hx
  obtain ⟨b, hbV, i, hAt⟩ := witnessDefs_defAt hd
  exact ⟨b, hbV, i, hAt.intTarget_defAt htgt⟩

theorem boolTarget_defAt {P : Program} {V : List Nat} {x : Nat}
    (hx : x ∈ DefExt.boolTargets (witnessDefs P V)) :
    ∃ b, b ∉ V ∧ ∃ i, IsDefAt P cmdBoolDef x b i := by
  obtain ⟨d, hd, htgt⟩ := DefExt.mem_boolTargets.mp hx
  obtain ⟨b, hbV, i, hAt⟩ := witnessDefs_defAt hd
  exact ⟨b, hbV, i, hAt.boolTarget_defAt htgt⟩

theorem not_intTarget_of_visited {P : Program} {V : List Nat} {x : Nat}
    (h : ∀ b i, IsDefAt P cmdIntDef x b i → b ∈ V) :
    x ∉ DefExt.intTargets (witnessDefs P V) := fun hx => by
  obtain ⟨b, hbV, i, hdef⟩ := intTarget_defAt hx
  exact hbV (h b i hdef)

theorem not_boolTarget_of_visited {P : Program} {V : List Nat} {x : Nat}
    (h : ∀ b i, IsDefAt P cmdBoolDef x b i → b ∈ V) :
    x ∉ DefExt.boolTargets (witnessDefs P V) := fun hx => by
  obtain ⟨b, hbV, i, hdef⟩ := boolTarget_defAt hx
  exact hbV (h b i hdef)

/-! ## Chain selection for visited phis -/

theorem lookupArm_cons {q s' p : Nat} {rest : List (Nat × Nat)} :
    lookupArm ((q, s') :: rest) p
      = if p = q then some s' else lookupArm rest p := by
  by_cases h : p = q
  · simp [lookupArm, List.lookup, h]
  · simp only [lookupArm, List.lookup, if_neg h]
    rw [show (p == q) = false from beq_eq_false_iff_ne.mpr h]

theorem phiChainI_select {P : Program} {V : List Nat} {w : State}
    (hblk : ∀ q, q < P.blocks.length → w.blks q = decide (q ∈ V))
    (hentryV : P.entry ∈ V) :
    ∀ (a : Nat × Nat) (rest : List (Nat × Nat)) {p src : Nat},
      lookupArm (a :: rest) p = some src → p ∈ V →
      (∀ x ∈ a :: rest, x.1 < P.blocks.length) →
      (∀ x ∈ a :: rest, x.1 ∈ V → x.1 = p) →
      evalI w (Vc.phiChainI P a rest) = w.ints src := by
  intro a rest
  induction rest generalizing a with
  | nil =>
      obtain ⟨q, s'⟩ := a
      intro p src harm hpV hlt huniq
      rw [lookupArm_cons] at harm
      by_cases hpq : p = q
      · rw [if_pos hpq] at harm
        obtain rfl := Option.some.inj harm
        simp [Vc.phiChainI, evalI]
      · rw [if_neg hpq] at harm
        simp [lookupArm, List.lookup] at harm
  | cons a' rest' ih =>
      obtain ⟨q, s'⟩ := a
      intro p src harm hpV hlt huniq
      have hguard : evalB w (Vc.guardOf P q) = decide (q ∈ V) := by
        unfold Vc.guardOf
        split
        · rename_i hq
          rw [hq]
          simp [evalB, hentryV]
        · simpa [evalB] using hblk q (hlt (q, s') (List.mem_cons_self ..))
      rw [lookupArm_cons] at harm
      simp only [Vc.phiChainI, Vc.evalI_mkIteI, hguard]
      by_cases hpq : p = q
      · rw [if_pos hpq] at harm
        obtain rfl := Option.some.inj harm
        have hqV : q ∈ V := hpq ▸ hpV
        simp [hqV, evalI]
      · rw [if_neg hpq] at harm
        have hqV : q ∉ V := fun hq =>
          hpq ((huniq (q, s') (List.mem_cons_self ..) hq).symm)
        simp only [hqV, decide_false, Bool.false_eq_true, if_false]
        exact ih a' harm hpV
          (fun x hx => hlt x (List.mem_cons_of_mem _ hx))
          (fun x hx => huniq x (List.mem_cons_of_mem _ hx))

theorem phiChainB_select {P : Program} {V : List Nat} {w : State}
    (hblk : ∀ q, q < P.blocks.length → w.blks q = decide (q ∈ V))
    (hentryV : P.entry ∈ V) :
    ∀ (a : Nat × Nat) (rest : List (Nat × Nat)) {p src : Nat},
      lookupArm (a :: rest) p = some src → p ∈ V →
      (∀ x ∈ a :: rest, x.1 < P.blocks.length) →
      (∀ x ∈ a :: rest, x.1 ∈ V → x.1 = p) →
      evalB w (Vc.phiChainB P a rest) = w.bools src := by
  intro a rest
  induction rest generalizing a with
  | nil =>
      obtain ⟨q, s'⟩ := a
      intro p src harm hpV hlt huniq
      rw [lookupArm_cons] at harm
      by_cases hpq : p = q
      · rw [if_pos hpq] at harm
        obtain rfl := Option.some.inj harm
        simp [Vc.phiChainB, evalB]
      · rw [if_neg hpq] at harm
        simp [lookupArm, List.lookup] at harm
  | cons a' rest' ih =>
      obtain ⟨q, s'⟩ := a
      intro p src harm hpV hlt huniq
      have hguard : evalB w (Vc.guardOf P q) = decide (q ∈ V) := by
        unfold Vc.guardOf
        split
        · rename_i hq
          rw [hq]
          simp [evalB, hentryV]
        · simpa [evalB] using hblk q (hlt (q, s') (List.mem_cons_self ..))
      rw [lookupArm_cons] at harm
      simp only [Vc.phiChainB, Vc.evalB_mkIteB, hguard]
      by_cases hpq : p = q
      · rw [if_pos hpq] at harm
        obtain rfl := Option.some.inj harm
        have hqV : q ∈ V := hpq ▸ hpV
        simp [hqV, evalB]
      · rw [if_neg hpq] at harm
        have hqV : q ∉ V := fun hq =>
          hpq ((huniq (q, s') (List.mem_cons_self ..) hq).symm)
        simp only [hqV, decide_false, Bool.false_eq_true, if_false]
        exact ih a' harm hpV
          (fun x hx => hlt x (List.mem_cons_of_mem _ hx))
          (fun x hx => huniq x (List.mem_cons_of_mem _ hx))

theorem phiRhsI_select {P : Program} {V : List Nat} {w : State}
    (hblk : ∀ q, q < P.blocks.length → w.blks q = decide (q ∈ V))
    (hentryV : P.entry ∈ V) {arms : PhiArms} {p src : Nat}
    (harm : lookupArm arms p = some src) (hpV : p ∈ V)
    (hlt : ∀ x ∈ arms, x.1 < P.blocks.length)
    (huniq : ∀ x ∈ arms, x.1 ∈ V → x.1 = p) :
    evalI w (Vc.phiRhsI P arms) = w.ints src := by
  cases arms with
  | nil => simp [lookupArm, List.lookup] at harm
  | cons a rest =>
      exact phiChainI_select hblk hentryV a rest harm hpV hlt huniq

theorem phiRhsB_select {P : Program} {V : List Nat} {w : State}
    (hblk : ∀ q, q < P.blocks.length → w.blks q = decide (q ∈ V))
    (hentryV : P.entry ∈ V) {arms : PhiArms} {p src : Nat}
    (harm : lookupArm arms p = some src) (hpV : p ∈ V)
    (hlt : ∀ x ∈ arms, x.1 < P.blocks.length)
    (huniq : ∀ x ∈ arms, x.1 ∈ V → x.1 = p) :
    evalB w (Vc.phiRhsB P arms) = w.bools src := by
  cases arms with
  | nil => simp [lookupArm, List.lookup] at harm
  | cons a rest =>
      exact phiChainB_select hblk hentryV a rest harm hpV hlt huniq

end Ttac
