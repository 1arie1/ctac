import Ttac.VcTrace

/-!
# The witness state

A failing execution's final state σ, extended with the block-visit
booleans, satisfies every expected constraint except the *unguarded phi
equations of unvisited joins* (their targets hold junk). The witness
repairs exactly those: walk the blocks in program order and re-execute
the phis of unvisited blocks against the accumulating state.

SSA does the heavy lifting: repair writes only registers whose unique
definition sits in an unvisited block, so every register with all defs
in visited blocks keeps its σ value (`witness_agree_*`), and a repaired
phi's right-hand side is never overwritten afterwards
(`witness_phiI`/`witness_phiB`).
-/

namespace Ttac

/-! ## Block-variable initialization -/

def setBlockVars (P : Program) (off : Nat) (V : List Nat) (σ : State) : State :=
  ((List.range P.blocks.length).foldl
      (fun s b => s.updB (off + b) (decide (b ∈ V))) σ).updB
    (off + P.blocks.length) true

section FoldUpd

variable {off : Nat} {f : Nat → Bool}

private theorem foldl_updB_ints (l : List Nat) (s : State) :
    (l.foldl (fun s b => s.updB (off + b) (f b)) s).ints = s.ints := by
  induction l generalizing s with
  | nil => rfl
  | cons x xs ih => rw [List.foldl_cons, ih, State.updB_ints]

private theorem foldl_updB_lt (l : List Nat) (s : State) {c : Nat}
    (hc : c < off) :
    (l.foldl (fun s b => s.updB (off + b) (f b)) s).bools c = s.bools c := by
  induction l generalizing s with
  | nil => rfl
  | cons x xs ih =>
      rw [List.foldl_cons, ih]
      exact State.updB_bools_of_ne s (by omega) _

private theorem foldl_updB_notmem (l : List Nat) (s : State) {j : Nat}
    (hj : j ∉ l) :
    (l.foldl (fun s b => s.updB (off + b) (f b)) s).bools (off + j)
      = s.bools (off + j) := by
  induction l generalizing s with
  | nil => rfl
  | cons x xs ih =>
      have hjx : j ≠ x := fun h => hj (h ▸ List.mem_cons_self ..)
      rw [List.foldl_cons,
        ih (s.updB (off + x) (f x)) (fun h => hj (List.mem_cons_of_mem _ h))]
      exact State.updB_bools_of_ne s (by omega) _

private theorem foldl_updB_get (l : List Nat) (s : State) {i : Nat}
    (hi : i ∈ l) (hnd : l.Nodup) :
    (l.foldl (fun s b => s.updB (off + b) (f b)) s).bools (off + i) = f i := by
  induction l generalizing s with
  | nil => cases hi
  | cons x xs ih =>
      obtain ⟨hx, hnd'⟩ := List.nodup_cons.mp hnd
      rcases List.mem_cons.mp hi with rfl | hi'
      · rw [List.foldl_cons, foldl_updB_notmem xs _ hx]
        exact State.updB_bools_self ..
      · rw [List.foldl_cons]
        exact ih _ hi' hnd'

end FoldUpd

theorem setBlockVars_ints (P : Program) (off : Nat) (V : List Nat) (σ : State) :
    (setBlockVars P off V σ).ints = σ.ints := by
  rw [setBlockVars, State.updB_ints, foldl_updB_ints]

theorem setBlockVars_lt (P : Program) (off : Nat) (V : List Nat) (σ : State)
    {c : Nat} (hc : c < off) :
    (setBlockVars P off V σ).bools c = σ.bools c := by
  rw [setBlockVars, State.updB_bools_of_ne _ (by omega), foldl_updB_lt _ _ hc]

theorem setBlockVars_blk (P : Program) (off : Nat) (V : List Nat) (σ : State)
    {i : Nat} (hi : i < P.blocks.length) :
    (setBlockVars P off V σ).bools (off + i) = decide (i ∈ V) := by
  rw [setBlockVars, State.updB_bools_of_ne _ (by omega),
    foldl_updB_get _ _ (List.mem_range.mpr hi) List.nodup_range]

theorem setBlockVars_exit (P : Program) (off : Nat) (V : List Nat) (σ : State) :
    (setBlockVars P off V σ).bools (off + P.blocks.length) = true := by
  rw [setBlockVars]
  exact State.updB_bools_self ..

/-! ## Phi repair -/

def repairCmd (P : Program) (off : Nat) (s : State) : Cmd → State
  | .phiI x arms => s.updI x (evalI s (Vc.phiRhsI P off arms))
  | .phiB c arms => s.updB c (evalB s (Vc.phiRhsB P off arms))
  | _ => s

def repairCmds (P : Program) (off : Nat) : List Cmd → State → State
  | [], s => s
  | c :: cs, s => repairCmds P off cs (repairCmd P off s c)

def repairBlocks (P : Program) (off : Nat) (V : List Nat) :
    Nat → List Block → State → State
  | _, [], s => s
  | b, B :: Bs, s =>
      repairBlocks P off V (b + 1) Bs
        (if b ∈ V then s else repairCmds P off B.cmds s)

def witness (P : Program) (off : Nat) (V : List Nat) (σ : State) : State :=
  repairBlocks P off V 0 P.blocks (setBlockVars P off V σ)

/-! ## What repair leaves untouched -/

theorem repairCmd_ints_ne {P : Program} {off : Nat} {s : State} {c : Cmd}
    {x : Nat} (h : cmdIntDef c ≠ some x) :
    (repairCmd P off s c).ints x = s.ints x := by
  cases c <;> simp only [repairCmd, cmdIntDef] at h ⊢ <;>
    first
      | rfl
      | exact State.updI_ints_of_ne s (fun heq => h (by rw [heq])) _

theorem repairCmd_bools_ne {P : Program} {off : Nat} {s : State} {c : Cmd}
    {x : Nat} (h : cmdBoolDef c ≠ some x) :
    (repairCmd P off s c).bools x = s.bools x := by
  cases c <;> simp only [repairCmd, cmdBoolDef] at h ⊢ <;>
    first
      | rfl
      | exact State.updB_bools_of_ne s (fun heq => h (by rw [heq])) _

theorem repairCmds_ints_nodef {P : Program} {off : Nat} {x : Nat} :
    ∀ {cs : List Cmd} {s : State}, (∀ c ∈ cs, cmdIntDef c ≠ some x) →
      (repairCmds P off cs s).ints x = s.ints x
  | [], _, _ => rfl
  | c :: cs, s, h => by
      rw [repairCmds, repairCmds_ints_nodef
        (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))]
      exact repairCmd_ints_ne (h c (List.mem_cons_self ..))

theorem repairCmds_bools_nodef {P : Program} {off : Nat} {x : Nat} :
    ∀ {cs : List Cmd} {s : State}, (∀ c ∈ cs, cmdBoolDef c ≠ some x) →
      (repairCmds P off cs s).bools x = s.bools x
  | [], _, _ => rfl
  | c :: cs, s, h => by
      rw [repairCmds, repairCmds_bools_nodef
        (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))]
      exact repairCmd_bools_ne (h c (List.mem_cons_self ..))

theorem repairBlocks_ints_nodef {P : Program} {off : Nat} {V : List Nat}
    {x : Nat} :
    ∀ {Bs : List Block} {k : Nat} {s : State},
      (∀ B ∈ Bs, ∀ c ∈ B.cmds, cmdIntDef c ≠ some x) →
      (repairBlocks P off V k Bs s).ints x = s.ints x
  | [], _, _, _ => rfl
  | B :: Bs, k, s, h => by
      rw [repairBlocks, repairBlocks_ints_nodef
        (fun B' hB' => h B' (List.mem_cons_of_mem _ hB'))]
      split
      · rfl
      · exact repairCmds_ints_nodef (h B (List.mem_cons_self ..))

theorem repairBlocks_bools_nodef {P : Program} {off : Nat} {V : List Nat}
    {x : Nat} :
    ∀ {Bs : List Block} {k : Nat} {s : State},
      (∀ B ∈ Bs, ∀ c ∈ B.cmds, cmdBoolDef c ≠ some x) →
      (repairBlocks P off V k Bs s).bools x = s.bools x
  | [], _, _, _ => rfl
  | B :: Bs, k, s, h => by
      rw [repairBlocks, repairBlocks_bools_nodef
        (fun B' hB' => h B' (List.mem_cons_of_mem _ hB'))]
      split
      · rfl
      · exact repairCmds_bools_nodef (h B (List.mem_cons_self ..))

/-! ## Bridges to the well-formedness checks -/

theorem boolDef_lt_off {P : Program} {off : Nat} (hoff : offOK P off = true)
    {B : Block} (hB : B ∈ P.blocks) {c : Cmd}
    (hc : c ∈ B.cmds) {t : Nat} (ht : cmdBoolDef c = some t) : t < off := by
  have hmem : t ∈ boolRegsOf P := by
    simp only [boolRegsOf, List.mem_flatten, List.mem_map]
    refine ⟨_, ⟨B, hB, rfl⟩, List.mem_append_left _ ?_⟩
    simp only [List.mem_flatten, List.mem_map]
    refine ⟨_, ⟨c, hc, rfl⟩, ?_⟩
    cases c <;> simp_all [cmdBoolDef, cmdBoolRegs]
  exact of_decide_eq_true (List.all_eq_true.mp hoff t hmem)

/-- Repair never writes bool registers at or above `off` (block
variables and the exit variable). -/
theorem witness_bools_ge {P : Program} {off : Nat} {V : List Nat} {σ : State}
    (hoff : offOK P off = true) {q : Nat} (hq : off ≤ q) :
    (witness P off V σ).bools q = (setBlockVars P off V σ).bools q := by
  refine repairBlocks_bools_nodef ?_
  intro B hB c hc ht
  have := boolDef_lt_off hoff hB hc ht
  omega

theorem witness_blk {P : Program} {off : Nat} {V : List Nat} {σ : State}
    (hoff : offOK P off = true) {i : Nat} (hi : i < P.blocks.length) :
    (witness P off V σ).bools (off + i) = decide (i ∈ V) := by
  rw [witness_bools_ge hoff (by omega), setBlockVars_blk _ _ _ _ hi]

theorem witness_exit {P : Program} {off : Nat} {V : List Nat} {σ : State}
    (hoff : offOK P off = true) :
    (witness P off V σ).bools (off + P.blocks.length) = true := by
  rw [witness_bools_ge hoff (by omega), setBlockVars_exit]

/-- Visited-aware preservation: repair skips visited blocks, so a
register with no int def in any *unvisited* block of the segment is
untouched. Block list indices are program indices shifted by `k`. -/
theorem repairBlocks_ints_visited {P : Program} {off : Nat} {V : List Nat}
    {x : Nat} :
    ∀ {Bs : List Block} {k : Nat} {s : State},
      (∀ m B', Bs[m]? = some B' → (k + m) ∉ V →
        ∀ c ∈ B'.cmds, cmdIntDef c ≠ some x) →
      (repairBlocks P off V k Bs s).ints x = s.ints x
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

theorem repairBlocks_bools_visited {P : Program} {off : Nat} {V : List Nat}
    {x : Nat} :
    ∀ {Bs : List Block} {k : Nat} {s : State},
      (∀ m B', Bs[m]? = some B' → (k + m) ∉ V →
        ∀ c ∈ B'.cmds, cmdBoolDef c ≠ some x) →
      (repairBlocks P off V k Bs s).bools x = s.bools x
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
theorem witness_agree_int {P : Program} {off : Nat} {V : List Nat} {σ : State}
    {x : Nat} (hdefs : ∀ d j, IsDefAt P cmdIntDef x d j → d ∈ V) :
    (witness P off V σ).ints x = σ.ints x := by
  rw [witness, repairBlocks_ints_visited, setBlockVars_ints]
  intro m B' hm hnv c hc hdef
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hc
  exact hnv (by simpa using hdefs m j ⟨B', c, hm, hj, hdef⟩)

theorem witness_agree_bool {P : Program} {off : Nat} {V : List Nat} {σ : State}
    {x : Nat} (hx : x < off)
    (hdefs : ∀ d j, IsDefAt P cmdBoolDef x d j → d ∈ V) :
    (witness P off V σ).bools x = σ.bools x := by
  rw [witness, repairBlocks_bools_visited, setBlockVars_lt _ _ _ _ hx]
  intro m B' hm hnv c hc hdef
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hc
  exact hnv (by simpa using hdefs m j ⟨B', c, hm, hj, hdef⟩)

/-! ## Variable inventories of phi right-hand sides -/

theorem guardOf_intVars (P : Program) (off q : Nat) :
    (Vc.guardOf P off q).intVars = [] := by
  unfold Vc.guardOf; split <;> rfl

theorem guardOf_boolVars (P : Program) (off q : Nat) :
    ∀ r ∈ (Vc.guardOf P off q).boolVars, r = off + q := by
  unfold Vc.guardOf
  split
  · intro r hr; cases hr
  · intro r hr
    simpa [BExp.boolVars] using hr

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

theorem phiChainI_intVars {P : Program} {off : Nat} :
    ∀ (a : Nat × Nat) (rest : List (Nat × Nat)),
      ∀ r ∈ (Vc.phiChainI P off a rest).intVars, ∃ q, (q, r) ∈ a :: rest
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

theorem phiChainI_boolVars {P : Program} {off : Nat} :
    ∀ (a : Nat × Nat) (rest : List (Nat × Nat)),
      ∀ r ∈ (Vc.phiChainI P off a rest).boolVars,
        ∃ q s, (q, s) ∈ a :: rest ∧ r = off + q
  | (q0, s0), [], r, hr => by
      simp only [Vc.phiChainI, IExp.boolVars] at hr
      cases hr
  | (q0, s0), a' :: rest', r, hr => by
      rcases mkIteI_boolVars r hr with hg | hs | ht
      · exact ⟨q0, s0, List.mem_cons_self .., guardOf_boolVars P off q0 r hg⟩
      · simp only [IExp.boolVars] at hs; cases hs
      · obtain ⟨q, s, hq, hrq⟩ := phiChainI_boolVars a' rest' r ht
        exact ⟨q, s, List.mem_cons_of_mem _ hq, hrq⟩

theorem phiRhsI_intVars {P : Program} {off : Nat} {arms : PhiArms} :
    ∀ r ∈ (Vc.phiRhsI P off arms).intVars, ∃ q, (q, r) ∈ arms := by
  cases arms with
  | nil => intro r hr; cases hr
  | cons a rest => exact phiChainI_intVars a rest

theorem phiRhsI_boolVars {P : Program} {off : Nat} {arms : PhiArms} :
    ∀ r ∈ (Vc.phiRhsI P off arms).boolVars,
      ∃ q s, (q, s) ∈ arms ∧ r = off + q := by
  cases arms with
  | nil => intro r hr; cases hr
  | cons a rest => exact phiChainI_boolVars a rest

theorem phiChainB_intVars {P : Program} {off : Nat} :
    ∀ (a : Nat × Nat) (rest : List (Nat × Nat)),
      ∀ r ∈ (Vc.phiChainB P off a rest).intVars, False
  | (q0, s0), [], r, hr => by
      simp only [Vc.phiChainB, BExp.intVars] at hr
      cases hr
  | (q0, s0), a' :: rest', r, hr => by
      rcases mkIteB_intVars r hr with hg | hs | ht
      · rw [show (Vc.guardOf P off q0).intVars = [] from by
          unfold Vc.guardOf; split <;> rfl] at hg
        cases hg
      · simp only [BExp.intVars] at hs; cases hs
      · exact phiChainB_intVars a' rest' r ht

theorem phiChainB_boolVars {P : Program} {off : Nat} :
    ∀ (a : Nat × Nat) (rest : List (Nat × Nat)),
      ∀ r ∈ (Vc.phiChainB P off a rest).boolVars,
        (∃ q, (q, r) ∈ a :: rest) ∨ (∃ q s, (q, s) ∈ a :: rest ∧ r = off + q)
  | (q0, s0), [], r, hr => by
      simp only [Vc.phiChainB, BExp.boolVars] at hr
      obtain rfl := List.mem_singleton.mp hr
      exact Or.inl ⟨q0, List.mem_cons_self ..⟩
  | (q0, s0), a' :: rest', r, hr => by
      rcases mkIteB_boolVars r hr with hg | hs | ht
      · exact Or.inr ⟨q0, s0, List.mem_cons_self ..,
          guardOf_boolVars P off q0 r hg⟩
      · simp only [BExp.boolVars] at hs
        obtain rfl := List.mem_singleton.mp hs
        exact Or.inl ⟨q0, List.mem_cons_self ..⟩
      · rcases phiChainB_boolVars a' rest' r ht with ⟨q, hq⟩ | ⟨q, s, hq, hrq⟩
        · exact Or.inl ⟨q, List.mem_cons_of_mem _ hq⟩
        · exact Or.inr ⟨q, s, List.mem_cons_of_mem _ hq, hrq⟩

theorem phiRhsB_intVars {P : Program} {off : Nat} {arms : PhiArms} :
    ∀ r ∈ (Vc.phiRhsB P off arms).intVars, False := by
  cases arms with
  | nil => intro r hr; cases hr
  | cons a rest => exact phiChainB_intVars a rest

theorem phiRhsB_boolVars {P : Program} {off : Nat} {arms : PhiArms} :
    ∀ r ∈ (Vc.phiRhsB P off arms).boolVars,
      (∃ q, (q, r) ∈ arms) ∨ (∃ q s, (q, s) ∈ arms ∧ r = off + q) := by
  cases arms with
  | nil => intro r hr; cases hr
  | cons a rest => exact phiChainB_boolVars a rest

/-! ## Value of a repaired phi -/

theorem repairCmds_phiI {P : Program} {off : Nat} {y : Nat} {arms : PhiArms} :
    ∀ {cs : List Cmd} {i : Nat} {s : State}, cs[i]? = some (.phiI y arms) →
      (∀ j c', cs[j]? = some c' → cmdIntDef c' = some y → j = i) →
      (∀ c' ∈ cs, ∀ r, cmdIntDef c' = some r →
        r ∉ (Vc.phiRhsI P off arms).intVars) →
      (∀ c' ∈ cs, ∀ r, cmdBoolDef c' = some r →
        r ∉ (Vc.phiRhsI P off arms).boolVars) →
      (repairCmds P off cs s).ints y
        = evalI (repairCmds P off cs s) (Vc.phiRhsI P off arms)
  | [], i, s, hget, _, _, _ => by simp at hget
  | c :: cs, i, s, hget, huniq, hint, hbool => by
      cases i with
      | zero =>
          obtain rfl : c = .phiI y arms := by simpa using hget
          have hy_nodef : ∀ c' ∈ cs, cmdIntDef c' ≠ some y := by
            intro c' hc' hdef
            obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hc'
            have := huniq (j + 1) c' (by simpa using hj) hdef
            omega
          have hint_pres : ∀ r ∈ (Vc.phiRhsI P off arms).intVars,
              (repairCmds P off cs (repairCmd P off s (.phiI y arms))).ints r
                = (repairCmd P off s (.phiI y arms)).ints r := fun r hr =>
            repairCmds_ints_nodef fun c' hc' hdef =>
              hint c' (List.mem_cons_of_mem _ hc') r hdef hr
          have hbool_pres : ∀ r ∈ (Vc.phiRhsI P off arms).boolVars,
              (repairCmds P off cs (repairCmd P off s (.phiI y arms))).bools r
                = (repairCmd P off s (.phiI y arms)).bools r := fun r hr =>
            repairCmds_bools_nodef fun c' hc' hdef =>
              hbool c' (List.mem_cons_of_mem _ hc') r hdef hr
          have hy_not : y ∉ (Vc.phiRhsI P off arms).intVars :=
            hint (.phiI y arms) (List.mem_cons_self ..) y (by simp [cmdIntDef])
          have hrhs_upd : ∀ r ∈ (Vc.phiRhsI P off arms).intVars,
              (repairCmd P off s (.phiI y arms)).ints r = s.ints r := by
            intro r hr
            simp only [repairCmd]
            exact State.updI_ints_of_ne s (fun h => hy_not (by rw [← h]; exact hr)) _
          have hyval :
              (repairCmds P off cs (repairCmd P off s (.phiI y arms))).ints y
                = evalI s (Vc.phiRhsI P off arms) := by
            rw [repairCmds_ints_nodef hy_nodef]
            simp [repairCmd]
          rw [repairCmds, hyval]
          refine (evalI_congr _ ?_ ?_).symm
          · intro r hr
            rw [hint_pres r hr, hrhs_upd r hr]
          · intro r hr
            rw [hbool_pres r hr]
            simp [repairCmd]
      | succ i' =>
          rw [repairCmds]
          exact repairCmds_phiI (by simpa using hget)
            (fun j c' hj hdef => by
              have := huniq (j + 1) c' (by simpa using hj) hdef
              omega)
            (fun c' hc' => hint c' (List.mem_cons_of_mem _ hc'))
            (fun c' hc' => hbool c' (List.mem_cons_of_mem _ hc'))

theorem repairCmds_phiB {P : Program} {off : Nat} {y : Nat} {arms : PhiArms} :
    ∀ {cs : List Cmd} {i : Nat} {s : State}, cs[i]? = some (.phiB y arms) →
      (∀ j c', cs[j]? = some c' → cmdBoolDef c' = some y → j = i) →
      (∀ c' ∈ cs, ∀ r, cmdIntDef c' = some r →
        r ∉ (Vc.phiRhsB P off arms).intVars) →
      (∀ c' ∈ cs, ∀ r, cmdBoolDef c' = some r →
        r ∉ (Vc.phiRhsB P off arms).boolVars) →
      (repairCmds P off cs s).bools y
        = evalB (repairCmds P off cs s) (Vc.phiRhsB P off arms)
  | [], i, s, hget, _, _, _ => by simp at hget
  | c :: cs, i, s, hget, huniq, hint, hbool => by
      cases i with
      | zero =>
          obtain rfl : c = .phiB y arms := by simpa using hget
          have hy_nodef : ∀ c' ∈ cs, cmdBoolDef c' ≠ some y := by
            intro c' hc' hdef
            obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hc'
            have := huniq (j + 1) c' (by simpa using hj) hdef
            omega
          have hint_pres : ∀ r ∈ (Vc.phiRhsB P off arms).intVars,
              (repairCmds P off cs (repairCmd P off s (.phiB y arms))).ints r
                = (repairCmd P off s (.phiB y arms)).ints r := fun r hr =>
            repairCmds_ints_nodef fun c' hc' hdef =>
              hint c' (List.mem_cons_of_mem _ hc') r hdef hr
          have hbool_pres : ∀ r ∈ (Vc.phiRhsB P off arms).boolVars,
              (repairCmds P off cs (repairCmd P off s (.phiB y arms))).bools r
                = (repairCmd P off s (.phiB y arms)).bools r := fun r hr =>
            repairCmds_bools_nodef fun c' hc' hdef =>
              hbool c' (List.mem_cons_of_mem _ hc') r hdef hr
          have hy_not : y ∉ (Vc.phiRhsB P off arms).boolVars :=
            hbool (.phiB y arms) (List.mem_cons_self ..) y (by simp [cmdBoolDef])
          have hrhs_upd : ∀ r ∈ (Vc.phiRhsB P off arms).boolVars,
              (repairCmd P off s (.phiB y arms)).bools r = s.bools r := by
            intro r hr
            simp only [repairCmd]
            exact State.updB_bools_of_ne s (fun h => hy_not (by rw [← h]; exact hr)) _
          have hyval :
              (repairCmds P off cs (repairCmd P off s (.phiB y arms))).bools y
                = evalB s (Vc.phiRhsB P off arms) := by
            rw [repairCmds_bools_nodef hy_nodef]
            simp [repairCmd]
          rw [repairCmds, hyval]
          refine (evalB_congr _ ?_ ?_).symm
          · intro r hr
            rw [hint_pres r hr]
            simp [repairCmd]
          · intro r hr
            rw [hbool_pres r hr, hrhs_upd r hr]
      | succ i' =>
          rw [repairCmds]
          exact repairCmds_phiB (by simpa using hget)
            (fun j c' hj hdef => by
              have := huniq (j + 1) c' (by simpa using hj) hdef
              omega)
            (fun c' hc' => hint c' (List.mem_cons_of_mem _ hc'))
            (fun c' hc' => hbool c' (List.mem_cons_of_mem _ hc'))

/-! ## Splitting the repair at a block -/

theorem repairBlocks_append {P : Program} {off : Nat} {V : List Nat} :
    ∀ (l1 l2 : List Block) (k : Nat) (s : State),
      repairBlocks P off V k (l1 ++ l2) s
        = repairBlocks P off V (k + l1.length) l2 (repairBlocks P off V k l1 s)
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
theorem witness_phiI {P : Program} {off : Nat} {V : List Nat} {σ : State}
    (hssa : ssaOK P = true) (huse : usesOK P = true) (hphi : phiOK P = true)
    (hoff : offOK P off = true) {b : Nat} {B : Block} {i y : Nat}
    {arms : PhiArms} (hB : P.block? b = some B)
    (hc : B.cmds[i]? = some (.phiI y arms)) (hbV : b ∉ V) :
    (witness P off V σ).ints y
      = evalI (witness P off V σ) (Vc.phiRhsI P off arms) := by
  have harms : phiArmsOK P b arms = true :=
    (phiOK_at hphi hB (List.mem_of_getElem? hc)).1 y arms rfl
  have hu := usesOK_cmd huse hB hc
  simp only [cmdUsesOK] at hu
  have hsrc_lt : ∀ r ∈ (Vc.phiRhsI P off arms).intVars,
      ∀ d j, IsDefAt P cmdIntDef r d j → d < b := by
    intro r hr d j hd
    obtain ⟨q, hq⟩ := phiRhsI_intVars r hr
    have hle := armUseOK_le (List.all_eq_true.mp hu (q, r) hq) d j hd
    have := phiArm_lt harms hq
    omega
  have hguard_ge : ∀ r ∈ (Vc.phiRhsI P off arms).boolVars, off ≤ r := by
    intro r hr
    obtain ⟨q, s', hq, rfl⟩ := phiRhsI_boolVars r hr
    omega
  have hy_def : IsDefAt P cmdIntDef y b i :=
    ⟨B, _, hB, hc, by simp [cmdIntDef]⟩
  have hw : witness P off V σ
      = repairBlocks P off V (b + 1) (P.blocks.drop (b + 1))
          (repairCmds P off B.cmds
            (repairBlocks P off V 0 (P.blocks.take b)
              (setBlockVars P off V σ))) := by
    have hblen :=
      (List.getElem?_eq_some_iff.mp (show P.blocks[b]? = some B from hB)).1
    have htake : (P.blocks.take b).length = b := by
      rw [List.length_take]; omega
    rw [witness]
    conv_lhs => rw [list_split_getElem? (show P.blocks[b]? = some B from hB)]
    rw [repairBlocks_append, htake, Nat.zero_add, repairBlocks, if_neg hbV]
  set sm := repairCmds P off B.cmds
    (repairBlocks P off V 0 (P.blocks.take b) (setBlockVars P off V σ))
    with hsm
  have hrest_int : ∀ r, (∀ d j, IsDefAt P cmdIntDef r d j → d ≤ b) →
      (repairBlocks P off V (b + 1) (P.blocks.drop (b + 1)) sm).ints r
        = sm.ints r := by
    intro r hle
    refine repairBlocks_ints_nodef ?_
    intro B' hB' c' hc' hdef
    obtain ⟨m, hm⟩ := List.mem_iff_getElem?.mp hB'
    rw [List.getElem?_drop] at hm
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hc'
    have := hle _ _ ⟨B', c', hm, hj, hdef⟩
    omega
  have hrest_bool : ∀ r, off ≤ r →
      (repairBlocks P off V (b + 1) (P.blocks.drop (b + 1)) sm).bools r
        = sm.bools r := by
    intro r hge
    refine repairBlocks_bools_nodef ?_
    intro B' hB' c' hc' hdef
    have := boolDef_lt_off hoff (List.mem_of_mem_drop hB') hc' hdef
    omega
  have hmid : sm.ints y = evalI sm (Vc.phiRhsI P off arms) := by
    refine repairCmds_phiI hc ?_ ?_ ?_
    · intro j c' hj hdef
      exact (ssa_unique_int hssa hy_def ⟨B, c', hB, hj, hdef⟩).2
    · intro c' hc' r hdef hr
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hc'
      have := hsrc_lt r hr b j ⟨B, c', hB, hj, hdef⟩
      omega
    · intro c' hc' r hdef hr
      have h1 := boolDef_lt_off hoff (List.mem_of_getElem? hB) hc' hdef
      have h2 := hguard_ge r hr
      omega
  rw [hw, hrest_int y (fun d j hd => by
      have := (ssa_unique_int hssa hy_def hd).1
      omega), hmid]
  exact evalI_congr _
    (fun r hr => (hrest_int r
      (fun d j hd => Nat.le_of_lt (hsrc_lt r hr d j hd))).symm)
    (fun r hr => (hrest_bool r (hguard_ge r hr)).symm)

theorem witness_phiB {P : Program} {off : Nat} {V : List Nat} {σ : State}
    (hssa : ssaOK P = true) (huse : usesOK P = true) (hphi : phiOK P = true)
    (hoff : offOK P off = true) {b : Nat} {B : Block} {i y : Nat}
    {arms : PhiArms} (hB : P.block? b = some B)
    (hc : B.cmds[i]? = some (.phiB y arms)) (hbV : b ∉ V) :
    (witness P off V σ).bools y
      = evalB (witness P off V σ) (Vc.phiRhsB P off arms) := by
  have harms : phiArmsOK P b arms = true :=
    (phiOK_at hphi hB (List.mem_of_getElem? hc)).2 y arms rfl
  have hu := usesOK_cmd huse hB hc
  simp only [cmdUsesOK] at hu
  have hbool_cases : ∀ r ∈ (Vc.phiRhsB P off arms).boolVars,
      (∀ d j, IsDefAt P cmdBoolDef r d j → d < b) ∨ off ≤ r := by
    intro r hr
    rcases phiRhsB_boolVars r hr with ⟨q, hq⟩ | ⟨q, s', hq, rfl⟩
    · left
      intro d j hd
      have hle := armUseOK_le (List.all_eq_true.mp hu (q, r) hq) d j hd
      have := phiArm_lt harms hq
      omega
    · right; omega
  have hy_def : IsDefAt P cmdBoolDef y b i :=
    ⟨B, _, hB, hc, by simp [cmdBoolDef]⟩
  have hw : witness P off V σ
      = repairBlocks P off V (b + 1) (P.blocks.drop (b + 1))
          (repairCmds P off B.cmds
            (repairBlocks P off V 0 (P.blocks.take b)
              (setBlockVars P off V σ))) := by
    have hblen :=
      (List.getElem?_eq_some_iff.mp (show P.blocks[b]? = some B from hB)).1
    have htake : (P.blocks.take b).length = b := by
      rw [List.length_take]; omega
    rw [witness]
    conv_lhs => rw [list_split_getElem? (show P.blocks[b]? = some B from hB)]
    rw [repairBlocks_append, htake, Nat.zero_add, repairBlocks, if_neg hbV]
  set sm := repairCmds P off B.cmds
    (repairBlocks P off V 0 (P.blocks.take b) (setBlockVars P off V σ))
    with hsm
  have hrest_bool : ∀ r,
      ((∀ d j, IsDefAt P cmdBoolDef r d j → d ≤ b) ∨ off ≤ r) →
      (repairBlocks P off V (b + 1) (P.blocks.drop (b + 1)) sm).bools r
        = sm.bools r := by
    intro r hcase
    refine repairBlocks_bools_nodef ?_
    intro B' hB' c' hc' hdef
    rcases hcase with hle | hge
    · obtain ⟨m, hm⟩ := List.mem_iff_getElem?.mp hB'
      rw [List.getElem?_drop] at hm
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hc'
      have := hle _ _ ⟨B', c', hm, hj, hdef⟩
      omega
    · have := boolDef_lt_off hoff (List.mem_of_mem_drop hB') hc' hdef
      omega
  have hmid : sm.bools y = evalB sm (Vc.phiRhsB P off arms) := by
    refine repairCmds_phiB hc ?_ ?_ ?_
    · intro j c' hj hdef
      exact (ssa_unique_bool hssa hy_def ⟨B, c', hB, hj, hdef⟩).2
    · intro c' hc' r hdef hr
      exact absurd hr (by intro h; exact phiRhsB_intVars r h)
    · intro c' hc' r hdef hr
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hc'
      rcases hbool_cases r hr with hlt | hge
      · have := hlt b j ⟨B, c', hB, hj, hdef⟩
        omega
      · have := boolDef_lt_off hoff (List.mem_of_getElem? hB) hc' hdef
        omega
  rw [hw, hrest_bool y (Or.inl fun d j hd => by
      have := (ssa_unique_bool hssa hy_def hd).1
      omega), hmid]
  exact evalB_congr _
    (fun r hr => absurd hr (by intro h; exact phiRhsB_intVars r h))
    (fun r hr => (hrest_bool r (by
      rcases hbool_cases r hr with hlt | hge
      · exact Or.inl fun d j hd => Nat.le_of_lt (hlt d j hd)
      · exact Or.inr hge)).symm)

/-! ## Chain selection for visited phis -/

theorem lookupArm_cons {q s' p : Nat} {rest : List (Nat × Nat)} :
    lookupArm ((q, s') :: rest) p
      = if p = q then some s' else lookupArm rest p := by
  by_cases h : p = q
  · simp [lookupArm, List.lookup, h]
  · simp only [lookupArm, List.lookup, if_neg h]
    rw [show (p == q) = false from beq_eq_false_iff_ne.mpr h]

theorem phiChainI_select {P : Program} {off : Nat} {V : List Nat} {w : State}
    (hblk : ∀ q, q < P.blocks.length → w.bools (off + q) = decide (q ∈ V))
    (hentryV : P.entry ∈ V) :
    ∀ (a : Nat × Nat) (rest : List (Nat × Nat)) {p src : Nat},
      lookupArm (a :: rest) p = some src → p ∈ V →
      (∀ x ∈ a :: rest, x.1 < P.blocks.length) →
      (∀ x ∈ a :: rest, x.1 ∈ V → x.1 = p) →
      evalI w (Vc.phiChainI P off a rest) = w.ints src := by
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
      have hguard : evalB w (Vc.guardOf P off q) = decide (q ∈ V) := by
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

theorem phiChainB_select {P : Program} {off : Nat} {V : List Nat} {w : State}
    (hblk : ∀ q, q < P.blocks.length → w.bools (off + q) = decide (q ∈ V))
    (hentryV : P.entry ∈ V) :
    ∀ (a : Nat × Nat) (rest : List (Nat × Nat)) {p src : Nat},
      lookupArm (a :: rest) p = some src → p ∈ V →
      (∀ x ∈ a :: rest, x.1 < P.blocks.length) →
      (∀ x ∈ a :: rest, x.1 ∈ V → x.1 = p) →
      evalB w (Vc.phiChainB P off a rest) = w.bools src := by
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
      have hguard : evalB w (Vc.guardOf P off q) = decide (q ∈ V) := by
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

theorem phiRhsI_select {P : Program} {off : Nat} {V : List Nat} {w : State}
    (hblk : ∀ q, q < P.blocks.length → w.bools (off + q) = decide (q ∈ V))
    (hentryV : P.entry ∈ V) {arms : PhiArms} {p src : Nat}
    (harm : lookupArm arms p = some src) (hpV : p ∈ V)
    (hlt : ∀ x ∈ arms, x.1 < P.blocks.length)
    (huniq : ∀ x ∈ arms, x.1 ∈ V → x.1 = p) :
    evalI w (Vc.phiRhsI P off arms) = w.ints src := by
  cases arms with
  | nil => simp [lookupArm, List.lookup] at harm
  | cons a rest =>
      exact phiChainI_select hblk hentryV a rest harm hpV hlt huniq

theorem phiRhsB_select {P : Program} {off : Nat} {V : List Nat} {w : State}
    (hblk : ∀ q, q < P.blocks.length → w.bools (off + q) = decide (q ∈ V))
    (hentryV : P.entry ∈ V) {arms : PhiArms} {p src : Nat}
    (harm : lookupArm arms p = some src) (hpV : p ∈ V)
    (hlt : ∀ x ∈ arms, x.1 < P.blocks.length)
    (huniq : ∀ x ∈ arms, x.1 ∈ V → x.1 = p) :
    evalB w (Vc.phiRhsB P off arms) = w.bools src := by
  cases arms with
  | nil => simp [lookupArm, List.lookup] at harm
  | cons a rest =>
      exact phiChainB_select hblk hentryV a rest harm hpV hlt huniq

end Ttac
