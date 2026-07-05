import Ttac.VcReplay

/-!
# Soundness of the VC checker

`checkVC P vc = true` implies: every failing execution of `P` induces a
satisfying assignment of `vc`. Corollary: if `vc` is unsatisfiable, `P`
is safe.

The argument is a definitional extension (`Ttac.DefExt`): with `W` =
the registers phi-defined in unvisited blocks, `expected_robust_or_def`
shows that every expected constraint is either **W-robust** at the base
state (σ plus visit guards) or **is** one of the unvisited-phi
definitions; `sat_extend` then closes both halves at the witness.

The robustness case analysis is where the bwd0 encoding's shape lives -
per constraint family:
- guarded facts of unvisited blocks are robust because their guard is
  false in every agreeing state (guards are untouched by the extension);
- facts of visited blocks are robust because the execution established
  them (`Suffix` coverage) and their variables are dominated, hence
  defined in visited blocks, hence outside `W`;
- visited phi equations are robust via chain selection
  (`phiRhsI_select`): the witnessing arm's source is dominated at the
  visited predecessor, and unvisited arms sit behind false guards;
- at-most-one clauses are robust by `visited_amo`; the CFG constraints
  restate the taken edges; the objective restates the failing assert.

Note which constraints are *not* handled by the syntactic bridge
`robust_of_avoids`: a guard-false fact of an unvisited block and a dead
disjunct of a visited CFG constraint may well mention `W`-variables -
this is exactly why robustness is semantic.
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
    evalB w (Vc.guardOf P q) = decide (q ∈ V) := by
  unfold Vc.guardOf
  split
  · rename_i h
    rw [h]
    simp [evalB, hentryV]
  · simpa [evalB] using hblk q hq

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
    cond.intVars = [] ∧ cond.blkVars = []
      ∧ ∀ r ∈ cond.boolVars,
          ∃ B t e, P.block? p = some B ∧ B.term = .ifGoto r t e := by
  obtain ⟨B, hB, hout⟩ := mem_allEdges_elim (mem_edgesTo.mp h)
  unfold Vc.outEdges at hout
  split at hout
  · cases hout
  · obtain rfl : cond = .lit true := by
      simp only [List.mem_singleton, Prod.mk.injEq] at hout
      exact hout.2.2
    exact ⟨rfl, rfl, fun r hr => by cases hr⟩
  · rename_i creg t e hterm
    simp only [List.mem_cons, Prod.mk.injEq,
      List.not_mem_nil, or_false] at hout
    rcases hout with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
    · refine ⟨rfl, rfl, fun r hr => ?_⟩
      obtain rfl : r = creg := by simpa [BExp.boolVars] using hr
      exact ⟨B, t, e, hB, hterm⟩
    · refine ⟨rfl, rfl, fun r hr => ?_⟩
      obtain rfl : r = creg := by simpa [BExp.boolVars, BExp.intVars] using hr
      exact ⟨B, t, e, hB, hterm⟩

/-! ## Robustness introduction

`Agrees` with the base state (σ plus visit guards), read through the
target inventory of `witnessDefs`, buys exactly the facts the old
witness lemmas provided: guards evaluate by visitedness, the exit guard
is true, and a register whose definitions are confined to visited
blocks keeps its σ value (primitively, or through a dominator of a
visited block). Robustness proofs consume this interface and never see
`Agrees` itself. -/

theorem robust_intro {P : Program} {V : List Nat} {σ : State} {c : BExp}
    (hentryV : P.entry ∈ V)
    (hdomV : ∀ v ∈ V, ∀ d, d ∈ domOf P v → d ∈ V)
    (h : ∀ w' : State,
      (∀ q, q < P.blocks.length → w'.blks q = decide (q ∈ V)) →
      w'.blks P.blocks.length = true →
      (∀ q, q < P.blocks.length →
        evalB w' (Vc.guardOf P q) = decide (q ∈ V)) →
      (∀ r, (∀ d j, IsDefAt P cmdIntDef r d j → d ∈ V) →
        w'.ints r = σ.ints r) →
      (∀ r, (∀ d j, IsDefAt P cmdBoolDef r d j → d ∈ V) →
        w'.bools r = σ.bools r) →
      (∀ v ∈ V, ∀ r,
        (∀ d j, IsDefAt P cmdIntDef r d j → d = v ∨ d ∈ domOf P v) →
        w'.ints r = σ.ints r) →
      (∀ v ∈ V, ∀ r,
        (∀ d j, IsDefAt P cmdBoolDef r d j → d = v ∨ d ∈ domOf P v) →
        w'.bools r = σ.bools r) →
      evalB w' c = true) :
    DefExt.Robust (· ∈ DefExt.intTargets (witnessDefs P V))
      (· ∈ DefExt.boolTargets (witnessDefs P V))
      (setBlockVars P V σ) c := by
  intro w' hag
  obtain ⟨aI, aB, ablk⟩ := hag
  have hblk : ∀ q, q < P.blocks.length → w'.blks q = decide (q ∈ V) :=
    fun q hq => by rw [congrFun ablk q, setBlockVars_blk _ _ _ hq]
  have hagI : ∀ r, (∀ d j, IsDefAt P cmdIntDef r d j → d ∈ V) →
      w'.ints r = σ.ints r :=
    fun r hr => by rw [aI r (not_intTarget_of_visited hr)]; rfl
  have hagB : ∀ r, (∀ d j, IsDefAt P cmdBoolDef r d j → d ∈ V) →
      w'.bools r = σ.bools r :=
    fun r hr => by rw [aB r (not_boolTarget_of_visited hr)]; rfl
  refine h w' hblk ?_ (fun q hq => guard_eval hentryV hblk hq) hagI hagB ?_ ?_
  · rw [congrFun ablk _, setBlockVars_exit]
  · intro v hv r hd
    refine hagI r fun d j hdj => ?_
    rcases hd d j hdj with rfl | hdm
    · exact hv
    · exact hdomV v hv d hdm
  · intro v hv r hd
    refine hagB r fun d j hdj => ?_
    rcases hd d j hdj with rfl | hdm
    · exact hv
    · exact hdomV v hv d hdm

/-! ## The main case analysis -/

/-- Every expected constraint is either robust with respect to the
unvisited-phi targets, or is itself one of the unvisited-phi
definitions. This is the encoding-specific half of the soundness
argument; `DefExt.sat_extend` supplies the generic half. -/
theorem expected_robust_or_def {P : Program} {σ : State} {V : List Nat}
    (hone : singleAssertOK P = true) (hssa : ssaOK P = true)
    (hfwd : forwardOK P = true) (hphi : phiOK P = true)
    (hamo : amoSideOK P = true) (hgf : guardFreeOK P = true)
    (hdc : domClosedOK P = true) (huse : usesOK P = true)
    (hS : Suffix P σ P.entry 0 none V) :
    ∀ c ∈ Vc.expected P,
      DefExt.Robust (· ∈ DefExt.intTargets (witnessDefs P V))
          (· ∈ DefExt.boolTargets (witnessDefs P V))
          (setBlockVars P V σ) c
        ∨ ∃ d ∈ witnessDefs P V, c = d.toConstraint := by
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
  obtain ⟨aB, iA, okReg, BA, heq, hBA, hcA, hlastA⟩ := singleAssert_shape hone
  intro c hc
  have hexp : Vc.expected P
      = (P.blocks.zipIdx.map fun (B, b) =>
          (B.cmds.map (Vc.cmdConstraints P b)).flatten).flatten
        ++ Vc.cfgConstraints P ++ Vc.objective P aB okReg := by
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
        refine Or.inl (robust_intro hentryV hdomV
          fun w' _hblk _hexit hguard hagI _hagB hdomI hdomB => ?_)
        rw [Vc.evalB_mkImp]
        by_cases hbV : b ∈ V
        · rw [Bool.or_eq_true]; right
          simp only [cmdUsesOK, Bool.and_eq_true] at hcuse
          obtain ⟨prev, hfact, -⟩ := hfacts b hbV B i _ hB hci
          simp only [CmdFact] at hfact
          have hwx : w'.ints x = σ.ints x := by
            refine hagI x fun d j hdj => ?_
            obtain ⟨rfl, -⟩ := ssa_unique_int hssa
              ⟨B, _, hB, hci, by simp [cmdIntDef]⟩ hdj
            exact hbV
          have hgfc := guardFree_at hgf (List.mem_of_getElem? hB) hcmdmem
          simp only [cmdGuardFree, List.isEmpty_iff] at hgfc
          have hevals : evalI w' e = evalI σ e := by
            refine evalI_congr e ?_ ?_ ?_
            · intro r hr
              exact hdomI b hbV r
                (useOK_dom (List.all_eq_true.mp hcuse.1 r hr))
            · intro r hr
              exact hdomB b hbV r
                (useOK_dom (List.all_eq_true.mp hcuse.2 r hr))
            · intro q hq
              rw [hgfc] at hq
              cases hq
          simp only [evalB, evalI, Vc.evalI_lowerI, hwx, hevals, hfact]
          simp
        · rw [Bool.or_eq_true]; left
          rw [hguard b hblt]
          simp [hbV]
    | assignB x e =>
        obtain rfl := List.mem_singleton.mp hcL2
        refine Or.inl (robust_intro hentryV hdomV
          fun w' _hblk _hexit hguard _hagI hagB hdomI hdomB => ?_)
        rw [Vc.evalB_mkImp]
        by_cases hbV : b ∈ V
        · rw [Bool.or_eq_true]; right
          simp only [cmdUsesOK, Bool.and_eq_true] at hcuse
          obtain ⟨prev, hfact, -⟩ := hfacts b hbV B i _ hB hci
          simp only [CmdFact] at hfact
          have hwx : w'.bools x = σ.bools x := by
            refine hagB x fun d j hdj => ?_
            obtain ⟨rfl, -⟩ := ssa_unique_bool hssa
              ⟨B, _, hB, hci, by simp [cmdBoolDef]⟩ hdj
            exact hbV
          have hgfc := guardFree_at hgf (List.mem_of_getElem? hB) hcmdmem
          simp only [cmdGuardFree, List.isEmpty_iff] at hgfc
          have hevals : evalB w' e = evalB σ e := by
            refine evalB_congr e ?_ ?_ ?_
            · intro r hr
              exact hdomI b hbV r
                (useOK_dom (List.all_eq_true.mp hcuse.1 r hr))
            · intro r hr
              exact hdomB b hbV r
                (useOK_dom (List.all_eq_true.mp hcuse.2 r hr))
            · intro q hq
              rw [hgfc] at hq
              cases hq
          simp only [evalB, Vc.evalB_lowerB, hwx, hevals, hfact]
          simp
        · rw [Bool.or_eq_true]; left
          rw [hguard b hblt]
          simp [hbV]
    | havocI x => cases hcL2
    | havocB x => cases hcL2
    | assume φ =>
        obtain rfl := List.mem_singleton.mp hcL2
        refine Or.inl (robust_intro hentryV hdomV
          fun w' _hblk _hexit hguard _hagI _hagB hdomI hdomB => ?_)
        rw [Vc.evalB_mkImp]
        by_cases hbV : b ∈ V
        · rw [Bool.or_eq_true]; right
          simp only [cmdUsesOK, Bool.and_eq_true] at hcuse
          obtain ⟨prev, hfact, -⟩ := hfacts b hbV B i _ hB hci
          simp only [CmdFact] at hfact
          have hgfc := guardFree_at hgf (List.mem_of_getElem? hB) hcmdmem
          simp only [cmdGuardFree, List.isEmpty_iff] at hgfc
          have hevals : evalB w' φ = evalB σ φ := by
            refine evalB_congr φ ?_ ?_ ?_
            · intro r hr
              exact hdomI b hbV r
                (useOK_dom (List.all_eq_true.mp hcuse.1 r hr))
            · intro r hr
              exact hdomB b hbV r
                (useOK_dom (List.all_eq_true.mp hcuse.2 r hr))
            · intro q hq
              rw [hgfc] at hq
              cases hq
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
          by_cases hbV : b ∈ V
          · -- visited: robust via chain selection
            refine Or.inl (robust_intro hentryV hdomV
              fun w' hblk _hexit _hguard hagI _hagB _hdomI _hdomB => ?_)
            simp only [evalB, evalI]
            simp only [cmdUsesOK] at hcuse
            obtain ⟨prev, hfact, hpred⟩ := hfacts b hbV B i _ hB hci
            simp only [CmdFact] at hfact
            obtain ⟨p, src, rfl, harm, hσy⟩ := hfact
            obtain ⟨hpV, hEdge⟩ := hpred p rfl
            have hpP : p ∈ predsOf P b := by
              obtain ⟨cond, hcond, -⟩ := hEdge.edge_cond
              exact mem_predsOf.mpr ⟨cond, hcond⟩
            have hwy : w'.ints y = σ.ints y := by
              refine hagI y fun d j hdj => ?_
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
            have hsel : evalI w' (Vc.phiRhsI P arms) = w'.ints src :=
              phiRhsI_select hblk hentryV harm hpV harm_lt huniq
            have hwsrc : w'.ints src = σ.ints src := by
              refine hagI src fun d j hdj => ?_
              have harmuse := List.all_eq_true.mp hcuse (p, src) (lookup_mem harm)
              exact hdomV p hpV d (armUseOK_dom harmuse d j hdj)
            exact decide_eq_true (by rw [hwy, hσy, ← hwsrc, ← hsel])
          · -- unvisited: the constraint IS the definition
            exact Or.inr ⟨.defI y (Vc.phiRhsI P arms),
              phiDefAt_mem_witnessDefs ⟨B, _, hB, hci, rfl⟩ hbV, rfl⟩
        · -- the at-most-one clauses
          split at hcamo
          · obtain ⟨g1, g2, hg1, hg2, hne, rfl⟩ := Vc.mem_amoClauses hcamo
            rw [List.mem_map] at hg1 hg2
            obtain ⟨⟨q1, s1⟩, hq1arm, rfl⟩ := hg1
            obtain ⟨⟨q2, s2⟩, hq2arm, rfl⟩ := hg2
            refine Or.inl (robust_intro hentryV hdomV
              fun w' _hblk _hexit hguard _hagI _hagB _hdomI _hdomB => ?_)
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
        · by_cases hbV : b ∈ V
          · refine Or.inl (robust_intro hentryV hdomV
              fun w' hblk _hexit _hguard _hagI hagB _hdomI _hdomB => ?_)
            simp only [evalB]
            simp only [cmdUsesOK] at hcuse
            obtain ⟨prev, hfact, hpred⟩ := hfacts b hbV B i _ hB hci
            simp only [CmdFact] at hfact
            obtain ⟨p, src, rfl, harm, hσy⟩ := hfact
            obtain ⟨hpV, hEdge⟩ := hpred p rfl
            have hpP : p ∈ predsOf P b := by
              obtain ⟨cond, hcond, -⟩ := hEdge.edge_cond
              exact mem_predsOf.mpr ⟨cond, hcond⟩
            have hwy : w'.bools y = σ.bools y := by
              refine hagB y fun d j hdj => ?_
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
            have hsel : evalB w' (Vc.phiRhsB P arms) = w'.bools src :=
              phiRhsB_select hblk hentryV harm hpV harm_lt huniq
            have hwsrc : w'.bools src = σ.bools src := by
              refine hagB src fun d j hdj => ?_
              have harmuse := List.all_eq_true.mp hcuse (p, src) (lookup_mem harm)
              exact hdomV p hpV d (armUseOK_dom harmuse d j hdj)
            have hyeq : w'.bools y = evalB w' (Vc.phiRhsB P arms) := by
              rw [hwy, hσy, ← hwsrc, ← hsel]
            simp [hyeq]
          · exact Or.inr ⟨.defB y (Vc.phiRhsB P arms),
              phiDefAt_mem_witnessDefs ⟨B, _, hB, hci, rfl⟩ hbV, rfl⟩
        · split at hcamo
          · obtain ⟨g1, g2, hg1, hg2, hne, rfl⟩ := Vc.mem_amoClauses hcamo
            rw [List.mem_map] at hg1 hg2
            obtain ⟨⟨q1, s1⟩, hq1arm, rfl⟩ := hg1
            obtain ⟨⟨q2, s2⟩, hq2arm, rfl⟩ := hg2
            refine Or.inl (robust_intro hentryV hdomV
              fun w' _hblk _hexit hguard _hagI _hagB _hdomI _hdomB => ?_)
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
        refine Or.inl (robust_intro hentryV hdomV
          fun w' _hblk _hexit hguard _hagI _hagB _hdomI hdomB => ?_)
        rw [Vc.evalB_mkImp]
        by_cases hSV : S ∈ V
        · rw [Bool.or_eq_true]; right
          rw [Vc.evalB_mkOr]
          obtain ⟨p, hpV, hE, -⟩ := chained_pred hedge hedge (hStail hSV)
          obtain ⟨cond, hcondmem, hcondeval⟩ := hE.edge_cond
          apply List.any_eq_true.mpr
          refine ⟨Vc.mkAnd2 (Vc.guardOf P p) cond,
            List.mem_map.mpr ⟨(p, cond), hcondmem, rfl⟩, ?_⟩
          rw [Vc.evalB_mkAnd2]
          have hplt : p < P.blocks.length :=
            Nat.lt_trans (pred_lt hfwd (mem_predsOf.mpr ⟨cond, hcondmem⟩)) hSmem
          rw [hguard p hplt]
          obtain ⟨hintnil, hblknil, hbvars⟩ := edge_cond_vars hcondmem
          have hcondw : evalB w' cond = evalB σ cond := by
            refine evalB_congr cond ?_ ?_ ?_
            · intro r hr
              rw [hintnil] at hr
              cases hr
            · intro r hr
              obtain ⟨B', t, e, hB', hterm'⟩ := hbvars r hr
              have hterm_use := usesOK_term huse hB'
              simp only [termUsesOK, hterm'] at hterm_use
              exact hdomB p hpV r
                (useOK_dom (List.all_eq_true.mp hterm_use r
                  (List.mem_singleton.mpr rfl)))
            · intro q hq
              rw [hblknil] at hq
              cases hq
          rw [hcondw, hcondeval]
          simp [hpV]
        · rw [Bool.or_eq_true]; left
          rw [hguard S hSmem]
          simp [hSV]
      · rcases List.mem_cons.mp hcL' with rfl | hcL''
        · -- block existence
          refine Or.inl (robust_intro hentryV hdomV
            fun w' _hblk _hexit hguard _hagI _hagB _hdomI _hdomB => ?_)
          rw [Vc.evalB_mkImp]
          by_cases hSV : S ∈ V
          · rw [Bool.or_eq_true]; right
            rw [Vc.evalB_mkOr]
            obtain ⟨p, hpV, hE, -⟩ := chained_pred hedge hedge (hStail hSV)
            obtain ⟨cond, hcondmem, -⟩ := hE.edge_cond
            apply List.any_eq_true.mpr
            refine ⟨Vc.guardOf P p,
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
          refine Or.inl (robust_intro hentryV hdomV
            fun w' _hblk _hexit hguard _hagI _hagB _hdomI _hdomB => ?_)
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
    · refine Or.inl (robust_intro hentryV hdomV
        fun w' _hblk _hexit hguard _hagI _hagB _hdomI hdomB => ?_)
      rw [Vc.evalB_mkImp]
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
      have hok : w'.bools okReg = false := by
        have hcuse := usesOK_cmd huse hBA hcA
        simp only [cmdUsesOK] at hcuse
        rw [hdomB aB haBV okReg
          (useOK_dom (List.all_eq_true.mp hcuse okReg
            (List.mem_singleton.mpr rfl)))]
        exact hfalse
      rw [Vc.evalB_mkNot]
      simp [evalB, hok, haBV]
    · rcases List.mem_cons.mp hc' with rfl | hc''
      · refine Or.inl (robust_intro hentryV hdomV
          fun w' _hblk hexit _hguard _hagI _hagB _hdomI _hdomB => ?_)
        simp only [Vc.exitVar, evalB]
        exact hexit
      · cases hc''

/-! ## Assembly -/

theorem expected_sat {P : Program} {σ : State} {V : List Nat}
    (hone : singleAssertOK P = true) (hssa : ssaOK P = true)
    (hfwd : forwardOK P = true) (hphi : phiOK P = true)
    (hamo : amoSideOK P = true) (hgf : guardFreeOK P = true)
    (hdc : domClosedOK P = true) (huse : usesOK P = true)
    (hS : Suffix P σ P.entry 0 none V) :
    ∀ c ∈ Vc.expected P, evalB (witness P V σ) c = true :=
  DefExt.sat_extend (orderedDefs_witnessDefs hssa huse hphi)
    (expected_robust_or_def hone hssa hfwd hphi hamo hgf hdc huse hS)

/-! ## Soundness -/

theorem checkVC_sound {P : Program} {vc : List BExp}
    (hchk : checkVC P vc = true) {s0 σ : State}
    (hrun : Steps P (Config.init P s0) (.failed σ)) :
    ∃ w, Vc.Sat w vc := by
  rw [checkVC, Bool.and_eq_true] at hchk
  obtain ⟨hwf, hmem⟩ := hchk
  rw [wellFormed] at hwf
  simp only [Bool.and_eq_true] at hwf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hone, hssa⟩, hfwd⟩, hphi⟩, hamo⟩, hentry⟩, hgf⟩, hdc⟩, huse⟩ := hwf
  obtain ⟨V, hS⟩ := suffix_of_steps hfwd hssa huse hphi hone hrun rfl
  refine ⟨witness P V σ, fun c hc => ?_⟩
  exact expected_sat hone hssa hfwd hphi hamo hgf hdc huse hS c
    (of_decide_eq_true (List.all_eq_true.mp hmem c hc))

/-- If `checkVC` accepts and the VC is unsatisfiable, the program is
safe: every model of the expected constraint set is refuted, so no
failing execution can exist. -/
theorem checkVC_safe {P : Program} {vc : List BExp}
    (hchk : checkVC P vc = true) (hunsat : Vc.Unsat vc) : P.Safe :=
  fun ⟨_s0, _σ, hrun⟩ => hunsat (checkVC_sound hchk hrun)

end Ttac
