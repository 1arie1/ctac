import Ttac.VcReplay

/-!
# Soundness of the VC checker

`checkVC P off vc = true` implies: every failing execution of `P`
induces a satisfying assignment of `vc` (the witness of
`Ttac.VcReplay`). Corollary: if `vc` is unsatisfiable, `P` is safe.

The satisfaction argument is per constraint family: guarded facts of
unvisited blocks hold because their guard is false; facts of visited
blocks hold because the execution established them (`Suffix` coverage)
and the witness agrees with σ on dominated registers; unguarded phi
equations of unvisited joins hold by repair; at-most-one clauses hold by
`visited_amo`; the CFG constraints restate the taken edges; the
objective restates the failing assert.
-/

namespace Ttac

/-! ## Small bridges -/

theorem useOK_dom {P : Program} {f : Cmd → Option Nat} {r b i : Nat}
    (h : useOK (domTable P) (defPositions P f r) b i = true) :
    ∀ d j, IsDefAt P f r d j → d = b ∨ d ∈ domOf P b := by
  intro d j hd
  have := List.all_eq_true.mp h (d, j) (mem_defPositions.mpr hd)
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this
  rcases this with ⟨hdb, _⟩ | ⟨_, hcont⟩
  · exact Or.inl hdb
  · exact Or.inr (List.contains_iff_mem.mp hcont)

theorem armUseOK_dom {P : Program} {f : Cmd → Option Nat} {src p : Nat}
    (h : armUseOK (domTable P) (defPositions P f src) p = true) :
    ∀ d j, IsDefAt P f src d j → d ∈ domOf P p := by
  intro d j hd
  have := List.all_eq_true.mp h (d, j) (mem_defPositions.mpr hd)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact List.contains_iff_mem.mp this.2

/-- Any bool register occurring in a command lies below `off`. -/
theorem cmdBoolReg_lt_off {P : Program} {off : Nat} (hoff : offOK P off = true)
    {B : Block} (hB : B ∈ P.blocks) {c : Cmd} (hc : c ∈ B.cmds) {t : Nat}
    (ht : t ∈ cmdBoolRegs c) : t < off := by
  have hmem : t ∈ boolRegsOf P := by
    simp only [boolRegsOf, List.mem_flatten, List.mem_map]
    refine ⟨_, ⟨B, hB, rfl⟩, List.mem_append_left _ ?_⟩
    simp only [List.mem_flatten, List.mem_map]
    exact ⟨_, ⟨c, hc, rfl⟩, ht⟩
  exact of_decide_eq_true (List.all_eq_true.mp hoff t hmem)

/-- The branch condition of a terminator lies below `off`. -/
theorem termBoolReg_lt_off {P : Program} {off : Nat} (hoff : offOK P off = true)
    {B : Block} (hB : B ∈ P.blocks) {creg t e : Nat}
    (hterm : B.term = .ifGoto creg t e) : creg < off := by
  have hmem : creg ∈ boolRegsOf P := by
    simp only [boolRegsOf, List.mem_flatten, List.mem_map]
    refine ⟨_, ⟨B, hB, rfl⟩, List.mem_append_right _ ?_⟩
    rw [hterm]
    exact List.mem_singleton.mpr rfl
  exact of_decide_eq_true (List.all_eq_true.mp hoff creg hmem)

/-- Guard evaluation under the witness: visited iff true. -/
theorem guard_eval {P : Program} {off : Nat} {V : List Nat} {σ : State}
    (hoff : offOK P off = true) (hentryV : P.entry ∈ V) {q : Nat}
    (hq : q < P.blocks.length) :
    evalB (witness P off V σ) (Vc.guardOf P off q) = decide (q ∈ V) := by
  unfold Vc.guardOf
  split
  · rename_i h
    rw [h]
    simp [evalB, hentryV]
  · simpa [evalB] using witness_blk hoff hq

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

/-- Every command of a visited block has its σ-fact; for tail blocks the
phi key is the actual predecessor, which was visited and edge-connected. -/
theorem facts_of_suffix {P : Program} {σ : State} {V : List Nat}
    (hone : singleAssertOK P = true)
    (hS : Suffix P σ P.entry 0 none V) :
    ∀ v ∈ V, ∀ (B : Block) (i : Nat) (c' : Cmd),
      P.block? v = some B → B.cmds[i]? = some c' →
      ∃ prev : Option Nat, CmdFact P σ prev c'
        ∧ ∀ p, prev = some p → p ∈ V ∧ EdgeTaken P σ p v := by
  have htail := hS.tail_covers hone
  have hedge := hS.chain_edge
  have hcov := hS.covers hone
  intro v hv B i c' hB hc'
  cases hVs : V with
  | nil => rw [hVs] at hv; cases hv
  | cons v0 rest =>
      have hhead := hS.head
      rw [hVs] at hhead
      obtain rfl : v0 = P.entry := Option.some.inj hhead
      rw [hVs] at hv
      rcases List.mem_cons.mp hv with rfl | hvtail
      · exact ⟨none, hcov B i c' hB hc' (Nat.zero_le i),
          fun p hp => by cases hp⟩
      · rw [hVs] at htail hedge
        obtain ⟨p, hp, hfact, hedgepv⟩ :=
          chained_pred htail hedge (v := v) hvtail
        refine ⟨some p, hfact B i c' hB hc', fun p' hp' => ?_⟩
        obtain rfl := Option.some.inj hp'
        exact ⟨hp, hedgepv⟩

/-- Two distinct members force length at least two. -/
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

/-- An edge condition mentions no int register, and its bool registers
are exactly the source block's branch condition. -/
theorem edge_cond_vars {P : Program} {S p : Nat} {cond : BExp}
    (h : (p, cond) ∈ Vc.edgesTo P S) :
    cond.intVars = []
      ∧ ∀ r ∈ cond.boolVars,
          ∃ B t e, P.block? p = some B ∧ B.term = .ifGoto r t e := by
  obtain ⟨B, hB, hout⟩ := mem_allEdges_elim (mem_edgesTo.mp h)
  unfold Vc.outEdges at hout
  split at hout
  · cases hout
  · obtain rfl : cond = .lit true := by
      simp only [List.mem_singleton, Prod.mk.injEq] at hout
      exact hout.2.2
    exact ⟨rfl, fun r hr => by cases hr⟩
  · rename_i creg t e hterm
    simp only [List.mem_cons, Prod.mk.injEq,
      List.not_mem_nil, or_false] at hout
    rcases hout with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
    · refine ⟨rfl, fun r hr => ?_⟩
      obtain rfl : r = creg := by simpa [BExp.boolVars] using hr
      exact ⟨B, t, e, hB, hterm⟩
    · refine ⟨rfl, fun r hr => ?_⟩
      obtain rfl : r = creg := by simpa [BExp.boolVars, BExp.intVars] using hr
      exact ⟨B, t, e, hB, hterm⟩

/-! ## The main satisfaction theorem -/

theorem expected_sat {P : Program} {off : Nat} {σ : State} {V : List Nat}
    (hone : singleAssertOK P = true) (hssa : ssaOK P = true)
    (hfwd : forwardOK P = true) (hphi : phiOK P = true)
    (hamo : amoSideOK P = true) (hoff : offOK P off = true)
    (hdc : domClosedOK P = true) (huse : usesOK P = true)
    (hS : Suffix P σ P.entry 0 none V) :
    ∀ c ∈ Vc.expected P off, evalB (witness P off V σ) c = true := by
  have hedge := hS.chain_edge
  have hhead := hS.head
  have hentryV : P.entry ∈ V := by
    cases V with
    | nil => cases hhead
    | cons v0 rest =>
        obtain rfl := Option.some.inj hhead
        exact List.mem_cons_self ..
  have hdomV := dom_visited hdc hfwd hedge hhead
  have hfacts := facts_of_suffix hone hS
  set w := witness P off V σ with hwdef
  have hguard : ∀ q, q < P.blocks.length →
      evalB w (Vc.guardOf P off q) = decide (q ∈ V) :=
    fun q hq => guard_eval hoff hentryV hq
  have hagree_int : ∀ v ∈ V, ∀ r : Nat,
      (∀ d j, IsDefAt P cmdIntDef r d j → d = v ∨ d ∈ domOf P v) →
      w.ints r = σ.ints r := by
    intro v hv r hd
    refine witness_agree_int fun d j hdj => ?_
    rcases hd d j hdj with rfl | hdm
    · exact hv
    · exact hdomV v hv d hdm
  have hagree_bool : ∀ v ∈ V, ∀ r : Nat, r < off →
      (∀ d j, IsDefAt P cmdBoolDef r d j → d = v ∨ d ∈ domOf P v) →
      w.bools r = σ.bools r := by
    intro v hv r hrlt hd
    refine witness_agree_bool hrlt fun d j hdj => ?_
    rcases hd d j hdj with rfl | hdm
    · exact hv
    · exact hdomV v hv d hdm
  obtain ⟨aB, iA, okReg, BA, heq, hBA, hcA, hlastA⟩ := singleAssert_shape hone
  intro c hc
  have hexp : Vc.expected P off
      = (P.blocks.zipIdx.map fun (B, b) =>
          (B.cmds.map (Vc.cmdConstraints P off b)).flatten).flatten
        ++ Vc.cfgConstraints P off ++ Vc.objective P off aB okReg := by
    unfold Vc.expected
    rw [heq]
  rw [hexp, List.mem_append, List.mem_append] at hc
  rcases hc with (hc | hc) | hc
  -- ==================== per-command constraints ====================
  · rw [List.mem_flatten] at hc
    obtain ⟨L, hL, hcL⟩ := hc
    rw [List.mem_map] at hL
    obtain ⟨⟨B, b⟩, hbmem, rfl⟩ := hL
    rw [List.mem_flatten] at hcL
    obtain ⟨L2, hL2, hcL2⟩ := hcL
    rw [List.mem_map] at hL2
    obtain ⟨cmd, hcmdmem, rfl⟩ := hL2
    have hB : P.block? b = some B := List.mem_zipIdx_iff_getElem?.mp hbmem
    have hblt : b < P.blocks.length := (List.getElem?_eq_some_iff.mp hB).1
    obtain ⟨i, hci⟩ := List.mem_iff_getElem?.mp hcmdmem
    have hcuse := usesOK_cmd huse hB hci
    cases cmd with
    | assignI x e =>
        obtain rfl := List.mem_singleton.mp hcL2
        rw [Vc.evalB_mkImp]
        by_cases hbV : b ∈ V
        · rw [Bool.or_eq_true]; right
          simp only [cmdUsesOK, Bool.and_eq_true] at hcuse
          obtain ⟨prev, hfact, -⟩ := hfacts b hbV B i _ hB hci
          simp only [CmdFact] at hfact
          have hwx : w.ints x = σ.ints x := by
            refine witness_agree_int fun d j hdj => ?_
            obtain ⟨rfl, -⟩ := ssa_unique_int hssa
              ⟨B, _, hB, hci, by simp [cmdIntDef]⟩ hdj
            exact hbV
          have hevals : evalI w e = evalI σ e := by
            refine evalI_congr e ?_ ?_
            · intro r hr
              exact hagree_int b hbV r
                (useOK_dom (List.all_eq_true.mp hcuse.1 r hr))
            · intro r hr
              refine hagree_bool b hbV r
                (cmdBoolReg_lt_off hoff (List.mem_of_getElem? hB) hcmdmem
                  (by simp [cmdBoolRegs, hr]))
                (useOK_dom (List.all_eq_true.mp hcuse.2 r hr))
          simp only [evalB, evalI, Vc.evalI_lowerI, hwx, hevals, hfact]
          simp
        · rw [Bool.or_eq_true]; left
          rw [hguard b hblt]
          simp [hbV]
    | assignB x e =>
        obtain rfl := List.mem_singleton.mp hcL2
        rw [Vc.evalB_mkImp]
        by_cases hbV : b ∈ V
        · rw [Bool.or_eq_true]; right
          simp only [cmdUsesOK, Bool.and_eq_true] at hcuse
          obtain ⟨prev, hfact, -⟩ := hfacts b hbV B i _ hB hci
          simp only [CmdFact] at hfact
          have hwx : w.bools x = σ.bools x := by
            refine witness_agree_bool
              (cmdBoolReg_lt_off hoff (List.mem_of_getElem? hB) hcmdmem
                (by simp [cmdBoolRegs]))
              fun d j hdj => ?_
            obtain ⟨rfl, -⟩ := ssa_unique_bool hssa
              ⟨B, _, hB, hci, by simp [cmdBoolDef]⟩ hdj
            exact hbV
          have hevals : evalB w e = evalB σ e := by
            refine evalB_congr e ?_ ?_
            · intro r hr
              exact hagree_int b hbV r
                (useOK_dom (List.all_eq_true.mp hcuse.1 r hr))
            · intro r hr
              refine hagree_bool b hbV r
                (cmdBoolReg_lt_off hoff (List.mem_of_getElem? hB) hcmdmem
                  (by simp [cmdBoolRegs, hr]))
                (useOK_dom (List.all_eq_true.mp hcuse.2 r hr))
          simp only [evalB, Vc.evalB_lowerB, hwx, hevals, hfact]
          simp
        · rw [Bool.or_eq_true]; left
          rw [hguard b hblt]
          simp [hbV]
    | havocI x => cases hcL2
    | havocB x => cases hcL2
    | assume φ =>
        obtain rfl := List.mem_singleton.mp hcL2
        rw [Vc.evalB_mkImp]
        by_cases hbV : b ∈ V
        · rw [Bool.or_eq_true]; right
          simp only [cmdUsesOK, Bool.and_eq_true] at hcuse
          obtain ⟨prev, hfact, -⟩ := hfacts b hbV B i _ hB hci
          simp only [CmdFact] at hfact
          have hevals : evalB w φ = evalB σ φ := by
            refine evalB_congr φ ?_ ?_
            · intro r hr
              exact hagree_int b hbV r
                (useOK_dom (List.all_eq_true.mp hcuse.1 r hr))
            · intro r hr
              refine hagree_bool b hbV r
                (cmdBoolReg_lt_off hoff (List.mem_of_getElem? hB) hcmdmem
                  (by simp [cmdBoolRegs, hr]))
                (useOK_dom (List.all_eq_true.mp hcuse.2 r hr))
          rw [Vc.evalB_lowerB, hevals, hfact]
        · rw [Bool.or_eq_true]; left
          rw [hguard b hblt]
          simp [hbV]
    | assert r => cases hcL2
    | phiI y arms =>
        have harms : phiArmsOK P b arms = true :=
          (phiOK_at hphi hB (List.mem_of_getElem? hci)).1 y arms rfl
        have harm_lt : ∀ x ∈ arms, x.1 < P.blocks.length := by
          intro a ha
          have := phiArm_lt harms (show (a.1, a.2) ∈ arms by simpa using ha)
          omega
        rcases List.mem_cons.mp hcL2 with rfl | hcamo
        · -- the phi equation
          simp only [evalB, evalI]
          by_cases hbV : b ∈ V
          · simp only [cmdUsesOK] at hcuse
            obtain ⟨prev, hfact, hpred⟩ := hfacts b hbV B i _ hB hci
            simp only [CmdFact] at hfact
            obtain ⟨p, src, rfl, harm, hσy⟩ := hfact
            obtain ⟨hpV, hEdge⟩ := hpred p rfl
            have hpP : p ∈ predsOf P b := by
              obtain ⟨cond, hcond, -⟩ := hEdge.edge_cond
              exact mem_predsOf.mpr ⟨cond, hcond⟩
            have hwy : w.ints y = σ.ints y := by
              refine witness_agree_int fun d j hdj => ?_
              obtain ⟨rfl, -⟩ := ssa_unique_int hssa
                ⟨B, _, hB, hci, by simp [cmdIntDef]⟩ hdj
              exact hbV
            have huniq : ∀ x ∈ arms, x.1 ∈ V → x.1 = p := by
              intro a ha haV
              have haP : a.1 ∈ predsOf P b :=
                phiArm_pred harms (show (a.1, a.2) ∈ arms by simpa using ha)
              by_cases hap : a.1 = p
              · exact hap
              · exact visited_amo hfwd hamo hedge hblt
                  (two_mem_le_length haP hpP hap) haV haP hpV hpP
            have hsel : evalI w (Vc.phiRhsI P off arms) = w.ints src :=
              phiRhsI_select (fun q hq => witness_blk hoff hq) hentryV
                harm hpV harm_lt huniq
            have hwsrc : w.ints src = σ.ints src := by
              refine witness_agree_int fun d j hdj => ?_
              have harmuse := List.all_eq_true.mp hcuse (p, src) (lookup_mem harm)
              exact hdomV p hpV d (armUseOK_dom harmuse d j hdj)
            exact decide_eq_true (by rw [hwy, hσy, ← hwsrc, ← hsel])
          · have hphiv : w.ints y = evalI w (Vc.phiRhsI P off arms) :=
              witness_phiI hssa huse hphi hoff hB hci hbV
            exact decide_eq_true hphiv
        · -- the at-most-one clauses
          split at hcamo
          · obtain ⟨g1, g2, hg1, hg2, hne, rfl⟩ := Vc.mem_amoClauses hcamo
            rw [List.mem_map] at hg1 hg2
            obtain ⟨⟨q1, s1⟩, hq1arm, rfl⟩ := hg1
            obtain ⟨⟨q2, s2⟩, hq2arm, rfl⟩ := hg2
            have hq1lt : q1 < P.blocks.length := by
              have := phiArm_lt harms hq1arm; omega
            have hq2lt : q2 < P.blocks.length := by
              have := phiArm_lt harms hq2arm; omega
            simp only [evalB, hguard q1 hq1lt, hguard q2 hq2lt]
            by_cases h1 : q1 ∈ V
            · by_cases h2 : q2 ∈ V
              · exfalso
                have hq12 : q1 ≠ q2 := fun h => hne (by rw [h])
                exact hq12 (visited_amo hfwd hamo hedge hblt
                  (two_mem_le_length (phiArm_pred harms hq1arm)
                    (phiArm_pred harms hq2arm) hq12)
                  h1 (phiArm_pred harms hq1arm) h2 (phiArm_pred harms hq2arm))
              · simp [h2]
            · simp [h1]
          · cases hcamo
    | phiB y arms =>
        have harms : phiArmsOK P b arms = true :=
          (phiOK_at hphi hB (List.mem_of_getElem? hci)).2 y arms rfl
        have harm_lt : ∀ x ∈ arms, x.1 < P.blocks.length := by
          intro a ha
          have := phiArm_lt harms (show (a.1, a.2) ∈ arms by simpa using ha)
          omega
        rcases List.mem_cons.mp hcL2 with rfl | hcamo
        · simp only [evalB]
          by_cases hbV : b ∈ V
          · simp only [cmdUsesOK] at hcuse
            obtain ⟨prev, hfact, hpred⟩ := hfacts b hbV B i _ hB hci
            simp only [CmdFact] at hfact
            obtain ⟨p, src, rfl, harm, hσy⟩ := hfact
            obtain ⟨hpV, hEdge⟩ := hpred p rfl
            have hpP : p ∈ predsOf P b := by
              obtain ⟨cond, hcond, -⟩ := hEdge.edge_cond
              exact mem_predsOf.mpr ⟨cond, hcond⟩
            have hylt : y < off :=
              cmdBoolReg_lt_off hoff (List.mem_of_getElem? hB) hcmdmem
                (by simp [cmdBoolRegs])
            have hwy : w.bools y = σ.bools y := by
              refine witness_agree_bool hylt fun d j hdj => ?_
              obtain ⟨rfl, -⟩ := ssa_unique_bool hssa
                ⟨B, _, hB, hci, by simp [cmdBoolDef]⟩ hdj
              exact hbV
            have huniq : ∀ x ∈ arms, x.1 ∈ V → x.1 = p := by
              intro a ha haV
              have haP : a.1 ∈ predsOf P b :=
                phiArm_pred harms (show (a.1, a.2) ∈ arms by simpa using ha)
              by_cases hap : a.1 = p
              · exact hap
              · exact visited_amo hfwd hamo hedge hblt
                  (two_mem_le_length haP hpP hap) haV haP hpV hpP
            have hsel : evalB w (Vc.phiRhsB P off arms) = w.bools src :=
              phiRhsB_select (fun q hq => witness_blk hoff hq) hentryV
                harm hpV harm_lt huniq
            have hwsrc : w.bools src = σ.bools src := by
              refine witness_agree_bool
                (cmdBoolReg_lt_off hoff (List.mem_of_getElem? hB) hcmdmem
                  (by simp [cmdBoolRegs]; exact Or.inr ⟨p, lookup_mem harm⟩))
                fun d j hdj => ?_
              have harmuse := List.all_eq_true.mp hcuse (p, src) (lookup_mem harm)
              exact hdomV p hpV d (armUseOK_dom harmuse d j hdj)
            have hyeq : w.bools y = evalB w (Vc.phiRhsB P off arms) := by
              rw [hwy, hσy, ← hwsrc, ← hsel]
            simp [hyeq]
          · have hphiv : w.bools y = evalB w (Vc.phiRhsB P off arms) :=
              witness_phiB hssa huse hphi hoff hB hci hbV
            simp [hphiv]
        · split at hcamo
          · obtain ⟨g1, g2, hg1, hg2, hne, rfl⟩ := Vc.mem_amoClauses hcamo
            rw [List.mem_map] at hg1 hg2
            obtain ⟨⟨q1, s1⟩, hq1arm, rfl⟩ := hg1
            obtain ⟨⟨q2, s2⟩, hq2arm, rfl⟩ := hg2
            have hq1lt : q1 < P.blocks.length := by
              have := phiArm_lt harms hq1arm; omega
            have hq2lt : q2 < P.blocks.length := by
              have := phiArm_lt harms hq2arm; omega
            simp only [evalB, hguard q1 hq1lt, hguard q2 hq2lt]
            by_cases h1 : q1 ∈ V
            · by_cases h2 : q2 ∈ V
              · exfalso
                have hq12 : q1 ≠ q2 := fun h => hne (by rw [h])
                exact hq12 (visited_amo hfwd hamo hedge hblt
                  (two_mem_le_length (phiArm_pred harms hq1arm)
                    (phiArm_pred harms hq2arm) hq12)
                  h1 (phiArm_pred harms hq1arm) h2 (phiArm_pred harms hq2arm))
              · simp [h2]
            · simp [h1]
          · cases hcamo
  -- ==================== CFG constraints ====================
  · simp only [Vc.cfgConstraints, List.mem_flatten, List.mem_map] at hc
    obtain ⟨L, ⟨S, hSmem, rfl⟩, hcL⟩ := hc
    rw [List.mem_range] at hSmem
    by_cases hSe : S = P.entry
    · rw [if_pos hSe] at hcL; cases hcL
    · rw [if_neg hSe] at hcL
      have hStail : S ∈ V → S ∈ V.tail := by
        intro hSV
        cases V with
        | nil => cases hhead
        | cons v0 rest =>
            obtain rfl := Option.some.inj hhead
            rcases List.mem_cons.mp hSV with rfl | h
            · exact absurd rfl hSe
            · exact h
      rcases List.mem_cons.mp hcL with rfl | hcL'
      · -- edge feasibility
        rw [Vc.evalB_mkImp]
        by_cases hSV : S ∈ V
        · rw [Bool.or_eq_true]; right
          rw [Vc.evalB_mkOr]
          obtain ⟨p, hpV, hE, -⟩ := chained_pred hedge hedge (hStail hSV)
          obtain ⟨cond, hcondmem, hcondeval⟩ := hE.edge_cond
          apply List.any_eq_true.mpr
          refine ⟨Vc.mkAnd2 (Vc.guardOf P off p) cond,
            List.mem_map.mpr ⟨(p, cond), hcondmem, rfl⟩, ?_⟩
          rw [Vc.evalB_mkAnd2]
          have hplt : p < P.blocks.length :=
            Nat.lt_trans (pred_lt hfwd (mem_predsOf.mpr ⟨cond, hcondmem⟩)) hSmem
          rw [hguard p hplt]
          obtain ⟨hintnil, hbvars⟩ := edge_cond_vars hcondmem
          have hcondw : evalB w cond = evalB σ cond := by
            refine evalB_congr cond ?_ ?_
            · intro r hr
              rw [hintnil] at hr
              cases hr
            · intro r hr
              obtain ⟨B', t, e, hB', hterm'⟩ := hbvars r hr
              have hterm_use := usesOK_term huse hB'
              simp only [termUsesOK, hterm'] at hterm_use
              exact hagree_bool p hpV r
                (termBoolReg_lt_off hoff (List.mem_of_getElem? hB') hterm')
                (useOK_dom (List.all_eq_true.mp hterm_use r
                  (List.mem_singleton.mpr rfl)))
          rw [hcondw, hcondeval]
          simp [hpV]
        · rw [Bool.or_eq_true]; left
          rw [hguard S hSmem]
          simp [hSV]
      · rcases List.mem_cons.mp hcL' with rfl | hcL''
        · -- block existence
          rw [Vc.evalB_mkImp]
          by_cases hSV : S ∈ V
          · rw [Bool.or_eq_true]; right
            rw [Vc.evalB_mkOr]
            obtain ⟨p, hpV, hE, -⟩ := chained_pred hedge hedge (hStail hSV)
            obtain ⟨cond, hcondmem, -⟩ := hE.edge_cond
            apply List.any_eq_true.mpr
            refine ⟨Vc.guardOf P off p,
              List.mem_map.mpr ⟨(p, cond), hcondmem, rfl⟩, ?_⟩
            have hplt : p < P.blocks.length :=
              Nat.lt_trans (pred_lt hfwd (mem_predsOf.mpr ⟨cond, hcondmem⟩)) hSmem
            rw [hguard p hplt]
            simp [hpV]
          · rw [Bool.or_eq_true]; left
            rw [hguard S hSmem]
            simp [hSV]
        · -- guarded at-most-one over predecessors
          rw [List.mem_map] at hcL''
          obtain ⟨cl, hclmem, rfl⟩ := hcL''
          rw [Vc.evalB_mkImp]
          by_cases hSV : S ∈ V
          · rw [Bool.or_eq_true]; right
            obtain ⟨g1, g2, hg1, hg2, hne, rfl⟩ := Vc.mem_amoClauses hclmem
            rw [List.mem_map] at hg1 hg2
            obtain ⟨⟨q1, c1⟩, hq1e, rfl⟩ := hg1
            obtain ⟨⟨q2, c2⟩, hq2e, rfl⟩ := hg2
            have hq1p : q1 ∈ predsOf P S := mem_predsOf.mpr ⟨c1, hq1e⟩
            have hq2p : q2 ∈ predsOf P S := mem_predsOf.mpr ⟨c2, hq2e⟩
            have hq1lt : q1 < P.blocks.length :=
              Nat.lt_trans (pred_lt hfwd hq1p) hSmem
            have hq2lt : q2 < P.blocks.length :=
              Nat.lt_trans (pred_lt hfwd hq2p) hSmem
            simp only [evalB, hguard q1 hq1lt, hguard q2 hq2lt]
            by_cases h1 : q1 ∈ V
            · by_cases h2 : q2 ∈ V
              · exfalso
                have hq12 : q1 ≠ q2 := fun h => hne (by rw [h])
                exact hq12 (visited_amo hfwd hamo hedge hSmem
                  (two_mem_le_length hq1p hq2p hq12) h1 hq1p h2 hq2p)
              · simp [h2]
            · simp [h1]
          · rw [Bool.or_eq_true]; left
            rw [hguard S hSmem]
            simp [hSV]
  -- ==================== objective ====================
  · rcases List.mem_cons.mp hc with rfl | hc'
    · rw [Vc.evalB_mkImp]
      rw [Bool.or_eq_true]; right
      obtain ⟨bf, Bf, pcf, cf, hlastV, hBf, hcf, hfalse⟩ := hS.last_block
      obtain ⟨hbf, hpcf, hcfok⟩ := singleAssert_unique hone hBf hcf hBA hcA
      have hbf' := hbf.symm
      have hcfok' := hcfok.symm
      subst hbf'
      subst hcfok'
      have haBV : aB ∈ V := getLast?_mem hlastV
      have haBlt : aB < P.blocks.length := (List.getElem?_eq_some_iff.mp hBA).1
      rw [Vc.evalB_mkAnd2, hguard aB haBlt]
      have hok : w.bools okReg = false := by
        have hcuse := usesOK_cmd huse hBA hcA
        simp only [cmdUsesOK] at hcuse
        rw [hagree_bool aB haBV okReg
          (cmdBoolReg_lt_off hoff (List.mem_of_getElem? hBA)
            (List.mem_of_getElem? hcA) (by simp [cmdBoolRegs]))
          (useOK_dom (List.all_eq_true.mp hcuse okReg
            (List.mem_singleton.mpr rfl)))]
        exact hfalse
      rw [Vc.evalB_mkNot]
      simp [evalB, hok, haBV]
    · rcases List.mem_cons.mp hc' with rfl | hc''
      · simp only [Vc.exitVar, evalB]
        exact witness_exit hoff
      · cases hc''

/-! ## Soundness -/

theorem checkVC_sound {P : Program} {off : Nat} {vc : List BExp}
    (hchk : checkVC P off vc = true) {s0 σ : State}
    (hrun : Steps P (Config.init P s0) (.failed σ)) :
    ∃ w, Vc.Sat w vc := by
  rw [checkVC, Bool.and_eq_true] at hchk
  obtain ⟨hwf, hmem⟩ := hchk
  rw [wellFormed] at hwf
  simp only [Bool.and_eq_true] at hwf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hone, hssa⟩, hfwd⟩, hphi⟩, hamo⟩, hoff⟩, hentry⟩, hdc⟩, huse⟩ := hwf
  obtain ⟨V, hS⟩ := suffix_of_steps hfwd hssa huse hphi hone hrun rfl
  refine ⟨witness P off V σ, fun c hc => ?_⟩
  exact expected_sat hone hssa hfwd hphi hamo hoff hdc huse hS c
    (of_decide_eq_true (List.all_eq_true.mp hmem c hc))

/-- If `checkVC` accepts and the VC is unsatisfiable, the program is
safe: every model of the expected constraint set is refuted, so no
failing execution can exist. -/
theorem checkVC_safe {P : Program} {off : Nat} {vc : List BExp}
    (hchk : checkVC P off vc = true) (hunsat : Vc.Unsat vc) : P.Safe :=
  fun ⟨_s0, _σ, hrun⟩ => hunsat (checkVC_sound hchk hrun)

end Ttac
