import Ttac.VcTrace

/-!
# The witness state

A failing execution's final state σ, with the guard component set from
the visited-block list, satisfies every expected constraint except the
*unguarded phi equations of unvisited joins* (their targets hold junk).
The witness repairs exactly those: walk the blocks in program order and
re-execute the phis of unvisited blocks against the accumulating state.

Guards live in their own `State.blks` component, written once by
`setBlockVars` and never touched by repair (which only writes program
registers) - so no disjointness side conditions are needed. SSA does
the rest: repair writes only registers whose unique definition sits in
an unvisited block, so every register with all defs in visited blocks
keeps its σ value (`witness_agree_*`), and a repaired phi's right-hand
side is never overwritten afterwards (`witness_phiI`/`witness_phiB`).
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

/-! ## Phi repair -/

def repairCmd (P : Program) (s : State) : Cmd → State
  | .phiI x arms => s.updI x (evalI s (Vc.phiRhsI P arms))
  | .phiB c arms => s.updB c (evalB s (Vc.phiRhsB P arms))
  | _ => s

def repairCmds (P : Program) : List Cmd → State → State
  | [], s => s
  | c :: cs, s => repairCmds P cs (repairCmd P s c)

def repairBlocks (P : Program) (V : List Nat) :
    Nat → List Block → State → State
  | _, [], s => s
  | b, B :: Bs, s =>
      repairBlocks P V (b + 1) Bs
        (if b ∈ V then s else repairCmds P B.cmds s)

def witness (P : Program) (V : List Nat) (σ : State) : State :=
  repairBlocks P V 0 P.blocks (setBlockVars P V σ)

/-! ## What repair leaves untouched -/

theorem repairCmd_ints_ne {P : Program} {s : State} {c : Cmd}
    {x : Nat} (h : cmdIntDef c ≠ some x) :
    (repairCmd P s c).ints x = s.ints x := by
  cases c <;> simp only [repairCmd, cmdIntDef] at h ⊢ <;>
    first
      | rfl
      | exact State.updI_ints_of_ne s (fun heq => h (by rw [heq])) _

theorem repairCmd_bools_ne {P : Program} {s : State} {c : Cmd}
    {x : Nat} (h : cmdBoolDef c ≠ some x) :
    (repairCmd P s c).bools x = s.bools x := by
  cases c <;> simp only [repairCmd, cmdBoolDef] at h ⊢ <;>
    first
      | rfl
      | exact State.updB_bools_of_ne s (fun heq => h (by rw [heq])) _

theorem repairCmd_blks {P : Program} {s : State} {c : Cmd} :
    (repairCmd P s c).blks = s.blks := by
  cases c <;> rfl

theorem repairCmds_ints_nodef {P : Program} {x : Nat} :
    ∀ {cs : List Cmd} {s : State}, (∀ c ∈ cs, cmdIntDef c ≠ some x) →
      (repairCmds P cs s).ints x = s.ints x
  | [], _, _ => rfl
  | c :: cs, s, h => by
      rw [repairCmds, repairCmds_ints_nodef
        (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))]
      exact repairCmd_ints_ne (h c (List.mem_cons_self ..))

theorem repairCmds_bools_nodef {P : Program} {x : Nat} :
    ∀ {cs : List Cmd} {s : State}, (∀ c ∈ cs, cmdBoolDef c ≠ some x) →
      (repairCmds P cs s).bools x = s.bools x
  | [], _, _ => rfl
  | c :: cs, s, h => by
      rw [repairCmds, repairCmds_bools_nodef
        (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))]
      exact repairCmd_bools_ne (h c (List.mem_cons_self ..))

theorem repairCmds_blks {P : Program} :
    ∀ {cs : List Cmd} {s : State}, (repairCmds P cs s).blks = s.blks
  | [], _ => rfl
  | c :: cs, s => by
      rw [repairCmds, repairCmds_blks, repairCmd_blks]

theorem repairBlocks_ints_nodef {P : Program} {V : List Nat} {x : Nat} :
    ∀ {Bs : List Block} {k : Nat} {s : State},
      (∀ B ∈ Bs, ∀ c ∈ B.cmds, cmdIntDef c ≠ some x) →
      (repairBlocks P V k Bs s).ints x = s.ints x
  | [], _, _, _ => rfl
  | B :: Bs, k, s, h => by
      rw [repairBlocks, repairBlocks_ints_nodef
        (fun B' hB' => h B' (List.mem_cons_of_mem _ hB'))]
      split
      · rfl
      · exact repairCmds_ints_nodef (h B (List.mem_cons_self ..))

theorem repairBlocks_bools_nodef {P : Program} {V : List Nat} {x : Nat} :
    ∀ {Bs : List Block} {k : Nat} {s : State},
      (∀ B ∈ Bs, ∀ c ∈ B.cmds, cmdBoolDef c ≠ some x) →
      (repairBlocks P V k Bs s).bools x = s.bools x
  | [], _, _, _ => rfl
  | B :: Bs, k, s, h => by
      rw [repairBlocks, repairBlocks_bools_nodef
        (fun B' hB' => h B' (List.mem_cons_of_mem _ hB'))]
      split
      · rfl
      · exact repairCmds_bools_nodef (h B (List.mem_cons_self ..))

theorem repairBlocks_blks {P : Program} {V : List Nat} :
    ∀ {Bs : List Block} {k : Nat} {s : State},
      (repairBlocks P V k Bs s).blks = s.blks
  | [], _, _ => rfl
  | B :: Bs, k, s => by
      rw [repairBlocks, repairBlocks_blks]
      split
      · rfl
      · exact repairCmds_blks

/-! ## Witness guard values -/

theorem witness_blks {P : Program} {V : List Nat} {σ : State} :
    (witness P V σ).blks = (setBlockVars P V σ).blks :=
  repairBlocks_blks

theorem witness_blk {P : Program} {V : List Nat} {σ : State}
    {q : Nat} (hq : q < P.blocks.length) :
    (witness P V σ).blks q = decide (q ∈ V) := by
  rw [witness_blks, setBlockVars_blk _ _ _ hq]

theorem witness_exit {P : Program} {V : List Nat} {σ : State} :
    (witness P V σ).blks P.blocks.length = true := by
  rw [witness_blks, setBlockVars_exit]

/-! ## Agreement with σ -/

/-- Visited-aware preservation: repair skips visited blocks, so a
register with no int def in any *unvisited* block of the segment is
untouched. Block list indices are program indices shifted by `k`. -/
theorem repairBlocks_ints_visited {P : Program} {V : List Nat} {x : Nat} :
    ∀ {Bs : List Block} {k : Nat} {s : State},
      (∀ m B', Bs[m]? = some B' → (k + m) ∉ V →
        ∀ c ∈ B'.cmds, cmdIntDef c ≠ some x) →
      (repairBlocks P V k Bs s).ints x = s.ints x
  | [], _, _, _ => rfl
  | B :: Bs, k, s, h => by
      rw [repairBlocks, repairBlocks_ints_visited (fun m B' hm hnv =>
        h (m + 1) B' (by simpa using hm) (by
          have : k + (m + 1) = k + 1 + m := by omega
          rwa [this]))]
      split
      · rfl
      · rename_i hkV
        exact repairCmds_ints_nodef
          (h 0 B rfl (by simpa using hkV))

theorem repairBlocks_bools_visited {P : Program} {V : List Nat} {x : Nat} :
    ∀ {Bs : List Block} {k : Nat} {s : State},
      (∀ m B', Bs[m]? = some B' → (k + m) ∉ V →
        ∀ c ∈ B'.cmds, cmdBoolDef c ≠ some x) →
      (repairBlocks P V k Bs s).bools x = s.bools x
  | [], _, _, _ => rfl
  | B :: Bs, k, s, h => by
      rw [repairBlocks, repairBlocks_bools_visited (fun m B' hm hnv =>
        h (m + 1) B' (by simpa using hm) (by
          have : k + (m + 1) = k + 1 + m := by omega
          rwa [this]))]
      split
      · rfl
      · rename_i hkV
        exact repairCmds_bools_nodef
          (h 0 B rfl (by simpa using hkV))

/-- A register whose every definition sits in a visited block keeps its
σ value (registers with no definition at all included). -/
theorem witness_agree_int {P : Program} {V : List Nat} {σ : State}
    {x : Nat} (hdefs : ∀ d j, IsDefAt P cmdIntDef x d j → d ∈ V) :
    (witness P V σ).ints x = σ.ints x := by
  rw [witness, repairBlocks_ints_visited, setBlockVars_ints]
  intro m B' hm hnv c hc hdef
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hc
  exact hnv (by simpa using hdefs m j ⟨B', c, hm, hj, hdef⟩)

theorem witness_agree_bool {P : Program} {V : List Nat} {σ : State}
    {x : Nat} (hdefs : ∀ d j, IsDefAt P cmdBoolDef x d j → d ∈ V) :
    (witness P V σ).bools x = σ.bools x := by
  rw [witness, repairBlocks_bools_visited, setBlockVars_bools]
  intro m B' hm hnv c hc hdef
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hc
  exact hnv (by simpa using hdefs m j ⟨B', c, hm, hj, hdef⟩)

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

/-! ## Value of a repaired phi -/

theorem repairCmds_phiI {P : Program} {y : Nat} {arms : PhiArms} :
    ∀ {cs : List Cmd} {i : Nat} {s : State}, cs[i]? = some (.phiI y arms) →
      (∀ j c', cs[j]? = some c' → cmdIntDef c' = some y → j = i) →
      (∀ c' ∈ cs, ∀ r, cmdIntDef c' = some r →
        r ∉ (Vc.phiRhsI P arms).intVars) →
      (repairCmds P cs s).ints y
        = evalI (repairCmds P cs s) (Vc.phiRhsI P arms)
  | [], i, s, hget, _, _ => by simp at hget
  | c :: cs, i, s, hget, huniq, hint => by
      cases i with
      | zero =>
          obtain rfl : c = .phiI y arms := by simpa using hget
          have hy_nodef : ∀ c' ∈ cs, cmdIntDef c' ≠ some y := by
            intro c' hc' hdef
            obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hc'
            have := huniq (j + 1) c' (by simpa using hj) hdef
            omega
          have hint_pres : ∀ r ∈ (Vc.phiRhsI P arms).intVars,
              (repairCmds P cs (repairCmd P s (.phiI y arms))).ints r
                = (repairCmd P s (.phiI y arms)).ints r := fun r hr =>
            repairCmds_ints_nodef fun c' hc' hdef =>
              hint c' (List.mem_cons_of_mem _ hc') r hdef hr
          have hy_not : y ∉ (Vc.phiRhsI P arms).intVars :=
            hint (.phiI y arms) (List.mem_cons_self ..) y (by simp [cmdIntDef])
          have hrhs_upd : ∀ r ∈ (Vc.phiRhsI P arms).intVars,
              (repairCmd P s (.phiI y arms)).ints r = s.ints r := by
            intro r hr
            simp only [repairCmd]
            exact State.updI_ints_of_ne s
              (fun h => hy_not (by rw [← h]; exact hr)) _
          have hyval :
              (repairCmds P cs (repairCmd P s (.phiI y arms))).ints y
                = evalI s (Vc.phiRhsI P arms) := by
            rw [repairCmds_ints_nodef hy_nodef]
            simp [repairCmd]
          rw [repairCmds, hyval]
          refine (evalI_congr _ ?_ ?_ ?_).symm
          · intro r hr
            rw [hint_pres r hr, hrhs_upd r hr]
          · intro r hr
            exact absurd hr (by intro h; exact phiRhsI_boolVars r h)
          · intro q _
            rw [repairCmds_blks, repairCmd_blks]
      | succ i' =>
          rw [repairCmds]
          exact repairCmds_phiI (by simpa using hget)
            (fun j c' hj hdef => by
              have := huniq (j + 1) c' (by simpa using hj) hdef
              omega)
            (fun c' hc' => hint c' (List.mem_cons_of_mem _ hc'))

theorem repairCmds_phiB {P : Program} {y : Nat} {arms : PhiArms} :
    ∀ {cs : List Cmd} {i : Nat} {s : State}, cs[i]? = some (.phiB y arms) →
      (∀ j c', cs[j]? = some c' → cmdBoolDef c' = some y → j = i) →
      (∀ c' ∈ cs, ∀ r, cmdBoolDef c' = some r →
        r ∉ (Vc.phiRhsB P arms).boolVars) →
      (repairCmds P cs s).bools y
        = evalB (repairCmds P cs s) (Vc.phiRhsB P arms)
  | [], i, s, hget, _, _ => by simp at hget
  | c :: cs, i, s, hget, huniq, hbool => by
      cases i with
      | zero =>
          obtain rfl : c = .phiB y arms := by simpa using hget
          have hy_nodef : ∀ c' ∈ cs, cmdBoolDef c' ≠ some y := by
            intro c' hc' hdef
            obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hc'
            have := huniq (j + 1) c' (by simpa using hj) hdef
            omega
          have hbool_pres : ∀ r ∈ (Vc.phiRhsB P arms).boolVars,
              (repairCmds P cs (repairCmd P s (.phiB y arms))).bools r
                = (repairCmd P s (.phiB y arms)).bools r := fun r hr =>
            repairCmds_bools_nodef fun c' hc' hdef =>
              hbool c' (List.mem_cons_of_mem _ hc') r hdef hr
          have hy_not : y ∉ (Vc.phiRhsB P arms).boolVars :=
            hbool (.phiB y arms) (List.mem_cons_self ..) y (by simp [cmdBoolDef])
          have hrhs_upd : ∀ r ∈ (Vc.phiRhsB P arms).boolVars,
              (repairCmd P s (.phiB y arms)).bools r = s.bools r := by
            intro r hr
            simp only [repairCmd]
            exact State.updB_bools_of_ne s
              (fun h => hy_not (by rw [← h]; exact hr)) _
          have hyval :
              (repairCmds P cs (repairCmd P s (.phiB y arms))).bools y
                = evalB s (Vc.phiRhsB P arms) := by
            rw [repairCmds_bools_nodef hy_nodef]
            simp [repairCmd]
          rw [repairCmds, hyval]
          refine (evalB_congr _ ?_ ?_ ?_).symm
          · intro r hr
            exact absurd hr (by intro h; exact phiRhsB_intVars r h)
          · intro r hr
            rw [hbool_pres r hr, hrhs_upd r hr]
          · intro q _
            rw [repairCmds_blks, repairCmd_blks]
      | succ i' =>
          rw [repairCmds]
          exact repairCmds_phiB (by simpa using hget)
            (fun j c' hj hdef => by
              have := huniq (j + 1) c' (by simpa using hj) hdef
              omega)
            (fun c' hc' => hbool c' (List.mem_cons_of_mem _ hc'))

/-! ## Splitting the repair at a block -/

theorem repairBlocks_append {P : Program} {V : List Nat} :
    ∀ (l1 l2 : List Block) (k : Nat) (s : State),
      repairBlocks P V k (l1 ++ l2) s
        = repairBlocks P V (k + l1.length) l2 (repairBlocks P V k l1 s)
  | [], l2, k, s => by simp [repairBlocks]
  | B :: l1, l2, k, s => by
      simp only [List.cons_append, repairBlocks]
      rw [repairBlocks_append l1 l2 (k + 1)]
      have hidx : k + (B :: l1).length = k + 1 + l1.length := by
        simp [List.length_cons]
        omega
      rw [hidx]

theorem list_split_getElem? {α : Type _} {l : List α} {i : Nat} {a : α}
    (h : l[i]? = some a) : l = l.take i ++ a :: l.drop (i + 1) := by
  obtain ⟨hi, hget⟩ := List.getElem?_eq_some_iff.mp h
  conv_lhs => rw [← List.take_append_drop i l]
  congr 1
  rw [List.drop_eq_getElem_cons hi, hget]

/-- The value of a phi in an *unvisited* block: the repair wrote it, and
nothing after position `(b, i)` touches the target or the right-hand
side's variables. -/
theorem witness_phiI {P : Program} {V : List Nat} {σ : State}
    (hssa : ssaOK P = true) (huse : usesOK P = true) (hphi : phiOK P = true)
    {b : Nat} {B : Block} {i y : Nat}
    {arms : PhiArms} (hB : P.block? b = some B)
    (hc : B.cmds[i]? = some (.phiI y arms)) (hbV : b ∉ V) :
    (witness P V σ).ints y
      = evalI (witness P V σ) (Vc.phiRhsI P arms) := by
  have harms : phiArmsOK P b arms = true :=
    (phiOK_at hphi hB (List.mem_of_getElem? hc)).1 y arms rfl
  have hu := usesOK_cmd huse hB hc
  simp only [cmdUsesOK] at hu
  have hsrc_lt : ∀ r ∈ (Vc.phiRhsI P arms).intVars,
      ∀ d j, IsDefAt P cmdIntDef r d j → d < b := by
    intro r hr d j hd
    obtain ⟨q, hq⟩ := phiRhsI_intVars r hr
    have hle := armUseOK_le (List.all_eq_true.mp hu (q, r) hq) d j hd
    have := phiArm_lt harms hq
    omega
  have hy_def : IsDefAt P cmdIntDef y b i :=
    ⟨B, _, hB, hc, by simp [cmdIntDef]⟩
  have hw : witness P V σ
      = repairBlocks P V (b + 1) (P.blocks.drop (b + 1))
          (repairCmds P B.cmds
            (repairBlocks P V 0 (P.blocks.take b)
              (setBlockVars P V σ))) := by
    have hblen :=
      (List.getElem?_eq_some_iff.mp (show P.blocks[b]? = some B from hB)).1
    have htake : (P.blocks.take b).length = b := by
      rw [List.length_take]; omega
    rw [witness]
    conv_lhs => rw [list_split_getElem? (show P.blocks[b]? = some B from hB)]
    rw [repairBlocks_append, htake, Nat.zero_add, repairBlocks, if_neg hbV]
  set sm := repairCmds P B.cmds
    (repairBlocks P V 0 (P.blocks.take b) (setBlockVars P V σ))
    with hsm
  have hrest_int : ∀ r, (∀ d j, IsDefAt P cmdIntDef r d j → d ≤ b) →
      (repairBlocks P V (b + 1) (P.blocks.drop (b + 1)) sm).ints r
        = sm.ints r := by
    intro r hle
    refine repairBlocks_ints_nodef ?_
    intro B' hB' c' hc' hdef
    obtain ⟨m, hm⟩ := List.mem_iff_getElem?.mp hB'
    rw [List.getElem?_drop] at hm
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hc'
    have := hle _ _ ⟨B', c', hm, hj, hdef⟩
    omega
  have hmid : sm.ints y = evalI sm (Vc.phiRhsI P arms) := by
    refine repairCmds_phiI hc ?_ ?_
    · intro j c' hj hdef
      exact (ssa_unique_int hssa hy_def ⟨B, c', hB, hj, hdef⟩).2
    · intro c' hc' r hdef hr
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hc'
      have := hsrc_lt r hr b j ⟨B, c', hB, hj, hdef⟩
      omega
  rw [hw, hrest_int y (fun d j hd => by
      have := (ssa_unique_int hssa hy_def hd).1
      omega), hmid]
  refine evalI_congr _
    (fun r hr => (hrest_int r
      (fun d j hd => Nat.le_of_lt (hsrc_lt r hr d j hd))).symm)
    (fun r hr => absurd hr (by intro h; exact phiRhsI_boolVars r h))
    (fun q _ => (congrFun repairBlocks_blks q).symm)

theorem witness_phiB {P : Program} {V : List Nat} {σ : State}
    (hssa : ssaOK P = true) (huse : usesOK P = true) (hphi : phiOK P = true)
    {b : Nat} {B : Block} {i y : Nat}
    {arms : PhiArms} (hB : P.block? b = some B)
    (hc : B.cmds[i]? = some (.phiB y arms)) (hbV : b ∉ V) :
    (witness P V σ).bools y
      = evalB (witness P V σ) (Vc.phiRhsB P arms) := by
  have harms : phiArmsOK P b arms = true :=
    (phiOK_at hphi hB (List.mem_of_getElem? hc)).2 y arms rfl
  have hu := usesOK_cmd huse hB hc
  simp only [cmdUsesOK] at hu
  have hsrc_lt : ∀ r ∈ (Vc.phiRhsB P arms).boolVars,
      ∀ d j, IsDefAt P cmdBoolDef r d j → d < b := by
    intro r hr d j hd
    obtain ⟨q, hq⟩ := phiRhsB_boolVars r hr
    have hle := armUseOK_le (List.all_eq_true.mp hu (q, r) hq) d j hd
    have := phiArm_lt harms hq
    omega
  have hy_def : IsDefAt P cmdBoolDef y b i :=
    ⟨B, _, hB, hc, by simp [cmdBoolDef]⟩
  have hw : witness P V σ
      = repairBlocks P V (b + 1) (P.blocks.drop (b + 1))
          (repairCmds P B.cmds
            (repairBlocks P V 0 (P.blocks.take b)
              (setBlockVars P V σ))) := by
    have hblen :=
      (List.getElem?_eq_some_iff.mp (show P.blocks[b]? = some B from hB)).1
    have htake : (P.blocks.take b).length = b := by
      rw [List.length_take]; omega
    rw [witness]
    conv_lhs => rw [list_split_getElem? (show P.blocks[b]? = some B from hB)]
    rw [repairBlocks_append, htake, Nat.zero_add, repairBlocks, if_neg hbV]
  set sm := repairCmds P B.cmds
    (repairBlocks P V 0 (P.blocks.take b) (setBlockVars P V σ))
    with hsm
  have hrest_bool : ∀ r, (∀ d j, IsDefAt P cmdBoolDef r d j → d ≤ b) →
      (repairBlocks P V (b + 1) (P.blocks.drop (b + 1)) sm).bools r
        = sm.bools r := by
    intro r hle
    refine repairBlocks_bools_nodef ?_
    intro B' hB' c' hc' hdef
    obtain ⟨m, hm⟩ := List.mem_iff_getElem?.mp hB'
    rw [List.getElem?_drop] at hm
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hc'
    have := hle _ _ ⟨B', c', hm, hj, hdef⟩
    omega
  have hmid : sm.bools y = evalB sm (Vc.phiRhsB P arms) := by
    refine repairCmds_phiB hc ?_ ?_
    · intro j c' hj hdef
      exact (ssa_unique_bool hssa hy_def ⟨B, c', hB, hj, hdef⟩).2
    · intro c' hc' r hdef hr
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hc'
      have := hsrc_lt r hr b j ⟨B, c', hB, hj, hdef⟩
      omega
  rw [hw, hrest_bool y (fun d j hd => by
      have := (ssa_unique_bool hssa hy_def hd).1
      omega), hmid]
  refine evalB_congr _
    (fun r hr => absurd hr (by intro h; exact phiRhsB_intVars r h))
    (fun r hr => (hrest_bool r
      (fun d j hd => Nat.le_of_lt (hsrc_lt r hr d j hd))).symm)
    (fun q _ => (congrFun repairBlocks_blks q).symm)

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
