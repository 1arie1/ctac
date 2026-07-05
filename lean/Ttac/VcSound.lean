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

The robustness case analysis is where the bwd0 encoding's shape lives,
and it is table-driven where the constraints are:
- every command with a `factB` entry gets the ONE `robust_cmd_fact`
  case - guarded facts of unvisited blocks are robust because their
  guard is false in every agreeing state, and facts of visited blocks
  because the execution established them (`Suffix` coverage, through
  the effect-table law `CmdFact.factB_eval`) with dominated variables
  outside `W`;
- visited phi equations are robust via chain selection
  (`phiRhs_select`), sort-generically; unvisited ones ARE the
  definitions (`Or.inr`);
- at-most-one clauses are robust by `visited_amo`; the CFG constraints
  restate the taken edges; the objective restates the failing assert.

Note which constraints are *not* handled by the syntactic bridge
`robust_of_avoids`: a guard-false fact of an unvisited block and a dead
disjunct of a visited CFG constraint may well mention `W`-variables -
this is exactly why robustness is semantic.
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

/-- Every command of a visited block has its σ-fact; for tail blocks the
phi key is the actual predecessor, which was visited and edge-connected. -/
theorem facts_of_suffix {P : Program} {σ : State} {V : List Nat}
    (hone : singleAssertOK P = true)
    (hS : Suffix P σ P.entry 0 none V) :
    ∀ v ∈ V, ∀ (B : Block) (i : Nat) (c' : Cmd),
      P.block? v = some B → B.cmds[i]? = some c' →
      ∃ prev : Option Nat, CmdFact σ prev c'
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

/-! ## Effect-table side lemmas

Two mechanical facts per `factB` row: the fact's variables are the
target (defined here) plus the command's uses (dominated), and the fact
reads no guard atom. A new local instruction discharges these by adding
its own small cases. -/

theorem factB_vars_dom {P : Program}
    (hssa : ssaOK P = true) (huse : usesOK P = true)
    {b : Nat} {B : Block} {i : Nat} {cmd : Cmd} {f : BExp}
    (hB : P.block? b = some B) (hci : B.cmds[i]? = some cmd)
    (hf : cmd.factB = some f) :
    ∀ p ∈ f.vars, ∀ d j, IsDefAt P p d j → d = b ∨ d ∈ domOf P b := by
  have hu := usesOK_cmd huse hB hci
  cases cmd with
  | assign t y e =>
      simp only [cmdUsesOK] at hu
      have htarget : ∀ d j, IsDefAt P (t, y) d j → d = b ∨ d ∈ domOf P b := by
        intro d j hd
        have hydef : IsDefAt P (t, y) b i := ⟨B, _, hB, hci, rfl⟩
        obtain ⟨rfl, -⟩ := ssa_unique hssa hydef hd
        exact Or.inl rfl
      cases t with
      | int =>
          obtain rfl := Option.some.inj hf
          intro p hp
          simp only [Exp.vars, List.singleton_append, List.mem_cons] at hp
          rcases hp with rfl | hp
          · exact htarget
          · exact useOK_dom (List.all_eq_true.mp hu p hp)
      | bool =>
          obtain rfl := Option.some.inj hf
          intro p hp
          simp only [Exp.vars, List.singleton_append, List.mem_cons] at hp
          rcases hp with rfl | hp
          · exact htarget
          · exact useOK_dom (List.all_eq_true.mp hu p hp)
      | map => cases hf
  | assume φ =>
      obtain rfl := Option.some.inj hf
      simp only [cmdUsesOK] at hu
      exact fun p hp => useOK_dom (List.all_eq_true.mp hu p hp)
  | havoc t y => cases hf
  | phi t y arms => cases hf
  | assert r => cases hf

theorem factB_blkVars {cmd : Cmd} {f : BExp} (hgf : cmdGuardFree cmd = true)
    (hf : cmd.factB = some f) : f.blkVars = [] := by
  cases cmd with
  | assign t y e =>
      simp only [cmdGuardFree, List.isEmpty_iff] at hgf
      cases t with
      | int =>
          obtain rfl := Option.some.inj hf
          simp [Exp.blkVars, hgf]
      | bool =>
          obtain rfl := Option.some.inj hf
          simp [Exp.blkVars, hgf]
      | map => cases hf
  | assume φ =>
      obtain rfl := Option.some.inj hf
      simpa [cmdGuardFree, List.isEmpty_iff] using hgf
  | havoc t y => cases hf
  | phi t y arms => cases hf
  | assert r => cases hf

/-! ## Robustness introduction

`Agrees` with the base state (σ plus visit guards), read through the
target inventory of `witnessDefs`, buys exactly these facts: guards
evaluate by visitedness, the exit guard is true, and a register whose
definitions are confined to visited blocks keeps its σ value
(primitively, or through a dominator of a visited block). Robustness
proofs consume this interface and never see `Agrees` itself. -/

theorem agrees_facts {P : Program} {V : List Nat} {σ : State}
    (hentryV : P.entry ∈ V)
    (hdomV : ∀ v ∈ V, ∀ d, d ∈ domOf P v → d ∈ V)
    {motive : State → Prop}
    (h : ∀ w' : State,
      (∀ q, q < P.blocks.length → w'.blks q = decide (q ∈ V)) →
      w'.blks P.blocks.length = true →
      (∀ q, q < P.blocks.length →
        (Vc.guardOf P q).eval w' = decide (q ∈ V)) →
      (∀ (t : Ty) (x : Nat), (∀ d j, IsDefAt P (t, x) d j → d ∈ V) →
        w'.regs t x = σ.regs t x) →
      (∀ v ∈ V, ∀ (t : Ty) (x : Nat),
        (∀ d j, IsDefAt P (t, x) d j → d = v ∨ d ∈ domOf P v) →
        w'.regs t x = σ.regs t x) →
      motive w') :
    ∀ w', DefExt.Agrees
        (fun t x => (t, x) ∈ DefExt.targets (witnessDefs P V))
        (setBlockVars P V σ) w' →
      motive w' := by
  intro w' hag'
  obtain ⟨areg, ablk⟩ := hag'
  have hblk : ∀ q, q < P.blocks.length → w'.blks q = decide (q ∈ V) :=
    fun q hq => by rw [congrFun ablk q, setBlockVars_blk _ _ _ hq]
  have hag : ∀ (t : Ty) (x : Nat),
      (∀ d j, IsDefAt P (t, x) d j → d ∈ V) →
      w'.regs t x = σ.regs t x :=
    fun t x hr => by rw [areg t x (not_target_of_visited hr)]; rfl
  refine h w' hblk ?_ (fun q hq => guard_eval hentryV hblk hq) hag ?_
  · rw [congrFun ablk _, setBlockVars_exit]
  · intro v hv t x hd
    refine hag t x fun d j hdj => ?_
    rcases hd d j hdj with rfl | hdm
    · exact hv
    · exact hdomV v hv d hdm

theorem robust_intro {P : Program} {V : List Nat} {σ : State} {c : BExp}
    (hentryV : P.entry ∈ V)
    (hdomV : ∀ v ∈ V, ∀ d, d ∈ domOf P v → d ∈ V)
    (h : ∀ w' : State,
      (∀ q, q < P.blocks.length → w'.blks q = decide (q ∈ V)) →
      w'.blks P.blocks.length = true →
      (∀ q, q < P.blocks.length →
        (Vc.guardOf P q).eval w' = decide (q ∈ V)) →
      (∀ (t : Ty) (x : Nat), (∀ d j, IsDefAt P (t, x) d j → d ∈ V) →
        w'.regs t x = σ.regs t x) →
      (∀ v ∈ V, ∀ (t : Ty) (x : Nat),
        (∀ d j, IsDefAt P (t, x) d j → d = v ∨ d ∈ domOf P v) →
        w'.regs t x = σ.regs t x) →
      c.eval w' = true) :
    DefExt.Robust (fun t x => (t, x) ∈ DefExt.targets (witnessDefs P V))
      (setBlockVars P V σ) c :=
  agrees_facts hentryV hdomV h

theorem robustDef_intro {P : Program} {V : List Nat} {σ : State}
    {d : DefExt.Def}
    (hentryV : P.entry ∈ V)
    (hdomV : ∀ v ∈ V, ∀ dd, dd ∈ domOf P v → dd ∈ V)
    (h : ∀ w' : State,
      (∀ q, q < P.blocks.length → w'.blks q = decide (q ∈ V)) →
      w'.blks P.blocks.length = true →
      (∀ q, q < P.blocks.length →
        (Vc.guardOf P q).eval w' = decide (q ∈ V)) →
      (∀ (t : Ty) (x : Nat), (∀ e j, IsDefAt P (t, x) e j → e ∈ V) →
        w'.regs t x = σ.regs t x) →
      (∀ v ∈ V, ∀ (t : Ty) (x : Nat),
        (∀ e j, IsDefAt P (t, x) e j → e = v ∨ e ∈ domOf P v) →
        w'.regs t x = σ.regs t x) →
      DefExt.DefHolds w' d) :
    DefExt.RobustDef (fun t x => (t, x) ∈ DefExt.targets (witnessDefs P V))
      (setBlockVars P V σ) d :=
  agrees_facts hentryV hdomV h

/-- The ONE guarded-fact case: the constraint of any command with a
`factB` entry is robust. Unvisited block: the guard is false in every
agreeing state. Visited block: the execution established the fact
(`CmdFact.factB_eval`), and its variables are defined here or dominated,
hence in visited blocks, hence outside `W`. -/
theorem robust_cmd_fact {P : Program} {σ : State} {V : List Nat}
    (hentryV : P.entry ∈ V)
    (hdomV : ∀ v ∈ V, ∀ d, d ∈ domOf P v → d ∈ V)
    {b : Nat} (hblt : b < P.blocks.length)
    {cmd : Cmd} {f : BExp} (hf : cmd.factB = some f)
    (hfact : b ∈ V → ∃ prev, CmdFact σ prev cmd)
    (hvars : ∀ p ∈ f.vars, ∀ d j, IsDefAt P p d j → d = b ∨ d ∈ domOf P b)
    (hblkv : f.blkVars = []) :
    DefExt.Robust (fun t x => (t, x) ∈ DefExt.targets (witnessDefs P V))
      (setBlockVars P V σ) (Vc.mkImp (Vc.guardOf P b) (Vc.lower f)) := by
  refine robust_intro hentryV hdomV
    fun w' _hblk _hexit hguard hag hdom => ?_
  rw [Vc.eval_mkImp]
  by_cases hbV : b ∈ V
  · rw [Bool.or_eq_true]; right
    obtain ⟨prev, hcf⟩ := hfact hbV
    have hσf : f.eval σ = true := hcf.factB_eval hf
    have hevals : f.eval w' = f.eval σ := by
      refine eval_congr f ?_ ?_
      · intro p hp
        exact hdom b hbV p.1 p.2 (hvars p hp)
      · intro q hq
        rw [hblkv] at hq
        cases hq
    rw [Vc.eval_lower, hevals, hσf]
  · rw [Bool.or_eq_true]; left
    rw [hguard b hblt]
    simp [hbV]

/-- A visited phi's defining equation holds in every agreeing state,
sort-generically: the target and the selected arm's source keep their
σ values (SSA + dominance), and the ITE chain selects the actual
predecessor's arm (`visited_amo` uniqueness). Consumed by the boolean
phi constraint (through `toConstraint_eval`) and by map-phi
definitions - the same fact, two renderings. -/
theorem visited_phi_defHolds {P : Program} {σ : State} {V : List Nat}
    (hssa : ssaOK P = true) (hfwd : forwardOK P = true)
    (hphi : phiOK P = true) (hamo : amoSideOK P = true)
    (huse : usesOK P = true)
    (hedge : Chained (EdgeTaken P σ) V) (hentryV : P.entry ∈ V)
    (hdomV : ∀ v ∈ V, ∀ d, d ∈ domOf P v → d ∈ V)
    (hfacts : ∀ v ∈ V, ∀ (B : Block) (i : Nat) (c' : Cmd),
      P.block? v = some B → B.cmds[i]? = some c' →
      ∃ prev : Option Nat, CmdFact σ prev c'
        ∧ ∀ p, prev = some p → p ∈ V ∧ EdgeTaken P σ p v)
    {b : Nat} {B : Block} {i : Nat} {t : Ty} {y : Nat} {arms : PhiArms}
    (hbV : b ∈ V) (hB : P.block? b = some B)
    (hci : B.cmds[i]? = some (.phi t y arms))
    (hblt : b < P.blocks.length)
    {w' : State}
    (hblk : ∀ q, q < P.blocks.length → w'.blks q = decide (q ∈ V))
    (hag : ∀ (u : Ty) (x : Nat),
      (∀ d j, IsDefAt P (u, x) d j → d ∈ V) → w'.regs u x = σ.regs u x) :
    DefExt.DefHolds w' ⟨t, y, Vc.phiRhs P t arms⟩ := by
  have harms : phiArmsOK P b arms = true :=
    phiOK_at hphi hB (List.mem_of_getElem? hci)
  have harm_lt : ∀ x ∈ arms, x.1 < P.blocks.length := by
    intro a ha
    have := phiArm_lt harms (show (a.1, a.2) ∈ arms by simpa using ha)
    omega
  have hu := usesOK_cmd huse hB hci
  simp only [cmdUsesOK] at hu
  obtain ⟨prev, hfact, hpred⟩ := hfacts b hbV B i _ hB hci
  simp only [CmdFact] at hfact
  obtain ⟨p, src, rfl, harm, hσy⟩ := hfact
  obtain ⟨hpV, hEdge⟩ := hpred p rfl
  have hpP : p ∈ predsOf P b := by
    obtain ⟨cond, hcond, -⟩ := hEdge.edge_cond
    exact mem_predsOf.mpr ⟨cond, hcond⟩
  have hwy : w'.regs t y = σ.regs t y := by
    refine hag t y fun d j hdj => ?_
    obtain ⟨rfl, -⟩ := ssa_unique hssa
      ⟨B, _, hB, hci, by simp [Cmd.def?]⟩ hdj
    exact hbV
  have huniq : ∀ x ∈ arms, x.1 ∈ V → x.1 = p := by
    intro a ha haV
    have haP : a.1 ∈ predsOf P b :=
      phiArm_pred harms (show (a.1, a.2) ∈ arms by simpa using ha)
    by_cases hap : a.1 = p
    · exact hap
    · exact visited_amo hfwd hamo hedge hblt
        (two_mem_le_length haP hpP hap) haV haP hpV hpP
  have hsel : (Vc.phiRhs P t arms).eval w' = w'.regs t src :=
    phiRhs_select hblk hentryV harm hpV harm_lt huniq
  have hwsrc : w'.regs t src = σ.regs t src := by
    refine hag t src fun d j hdj => ?_
    have harmuse := List.all_eq_true.mp hu (p, src) (lookup_mem harm)
    exact hdomV p hpV d (armUseOK_dom harmuse d j hdj)
  show w'.regs t y = (Vc.phiRhs P t arms).eval w'
  rw [hwy, hσy, ← hwsrc, ← hsel]

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
      DefExt.Robust (fun t x => (t, x) ∈ DefExt.targets (witnessDefs P V))
          (setBlockVars P V σ) c
        ∨ ∃ d ∈ witnessDefs P V, d.toConstraint? = some c := by
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
  obtain ⟨aB, iA, okReg, BA, heqs, hBA, hcA, hlastA⟩ := singleAssert_shape hone
  intro c hc
  have hexp : Vc.expected P
      = (P.blocks.zipIdx.map fun (B, b) =>
          (B.cmds.map (Vc.cmdConstraints P b)).flatten).flatten
        ++ Vc.cfgConstraints P ++ Vc.objective P aB okReg := by
    unfold Vc.expected
    rw [heqs]
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
    rcases mem_cmdConstraints hcL2 with hfc | ⟨t, y, arms, rfl, hshape⟩
    · -- the guarded-fact case, once for every factB command
      obtain ⟨f, hfb, rfl⟩ := mem_factConstraints hfc
      refine Or.inl (robust_cmd_fact hentryV hdomV hblt hfb ?_
        (factB_vars_dom hssa huse hB hci hfb)
        (factB_blkVars (guardFree_at hgf (List.mem_of_getElem? hB)
          hcmdmem) hfb))
      intro hbV
      obtain ⟨prev, hfact, -⟩ := hfacts b hbV B i _ hB hci
      exact ⟨prev, hfact⟩
    · -- phi
      have harms : phiArmsOK P b arms = true := phiOK_at hphi hB hcmdmem
      rcases hshape with heq | ⟨hlen2, hcamo⟩
      · -- the phi equation, sort-generically
        by_cases hbV : b ∈ V
        · refine Or.inl (robust_intro hentryV hdomV
            fun w' hblk _hexit _hguard hag _hdom => ?_)
          exact (visited_phi_defHolds hssa hfwd hphi hamo huse hedge
            hentryV hdomV hfacts hbV hB hci hblt hblk hag).toConstraint_eval
            heq
        · exact Or.inr ⟨⟨t, y, Vc.phiRhs P t arms⟩,
            witnessDefAt_mem_witnessDefs ⟨B, _, hB, hci, rfl⟩ hbV, heq⟩
      · -- the at-most-one clauses
        obtain ⟨g1, g2, hg1, hg2, hne, rfl⟩ := Vc.mem_amoClauses hcamo
        rw [List.mem_map] at hg1 hg2
        obtain ⟨⟨q1, s1⟩, hq1arm, rfl⟩ := hg1
        obtain ⟨⟨q2, s2⟩, hq2arm, rfl⟩ := hg2
        refine Or.inl (robust_intro hentryV hdomV
          fun w' _hblk _hexit hguard _hag _hdom => ?_)
        have hq1lt : q1 < P.blocks.length := by
          have := phiArm_lt harms hq1arm; omega
        have hq2lt : q2 < P.blocks.length := by
          have := phiArm_lt harms hq2arm; omega
        simp only [Exp.eval, UnOp.denote, BinOp.denote,
          hguard q1 hq1lt, hguard q2 hq2lt]
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
          fun w' _hblk _hexit hguard _hag hdom => ?_)
        rw [Vc.eval_mkImp]
        by_cases hSV : S ∈ V
        · rw [Bool.or_eq_true]; right
          rw [Vc.eval_mkOr]
          obtain ⟨p, hpV, hE, -⟩ := chained_pred hedge hedge (hStail hSV)
          obtain ⟨cond, hcondmem, hcondeval⟩ := hE.edge_cond
          apply List.any_eq_true.mpr
          refine ⟨Vc.mkAnd2 (Vc.guardOf P p) cond,
            List.mem_map.mpr ⟨(p, cond), hcondmem, rfl⟩, ?_⟩
          rw [Vc.eval_mkAnd2]
          have hplt : p < P.blocks.length :=
            Nat.lt_trans (pred_lt hfwd (mem_predsOf.mpr ⟨cond, hcondmem⟩)) hSmem
          rw [hguard p hplt]
          obtain ⟨hblknil, hbvars⟩ := edge_cond_vars hcondmem
          have hcondw : cond.eval w' = cond.eval σ := by
            refine eval_congr cond ?_ ?_
            · intro q hq
              obtain ⟨r, B', t', e', rfl, hB', hterm'⟩ := hbvars q hq
              have hterm_use := usesOK_term huse hB'
              simp only [termUsesOK, hterm'] at hterm_use
              exact hdom p hpV .bool r (useOK_dom hterm_use)
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
            fun w' _hblk _hexit hguard _hag _hdom => ?_)
          rw [Vc.eval_mkImp]
          by_cases hSV : S ∈ V
          · rw [Bool.or_eq_true]; right
            rw [Vc.eval_mkOr]
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
            fun w' _hblk _hexit hguard _hag _hdom => ?_)
          rw [Vc.eval_mkImp]
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
            simp only [Exp.eval, UnOp.denote, BinOp.denote,
              hguard q1 hq1lt, hguard q2 hq2lt]
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
        fun w' _hblk _hexit hguard _hag hdom => ?_)
      rw [Vc.eval_mkImp]
      rw [Bool.or_eq_true]; right
      obtain ⟨bf, Bf, pcf, cf, hlastV, hBf, hcf, hfalse⟩ := hS.last_block
      obtain ⟨hbf, hpcf, hcfok⟩ := singleAssert_unique hone hBf hcf hBA hcA
      have hbf' := hbf.symm
      have hcfok' := hcfok.symm
      subst hbf'
      subst hcfok'
      have haBV : aB ∈ V := getLast?_mem hlastV
      have haBlt : aB < P.blocks.length := (List.getElem?_eq_some_iff.mp hBA).1
      rw [Vc.eval_mkAnd2, hguard aB haBlt]
      have hok : w'.regs .bool okReg = false := by
        have hcuse := usesOK_cmd huse hBA hcA
        simp only [cmdUsesOK] at hcuse
        rw [hdom aB haBV .bool okReg (useOK_dom hcuse)]
        exact hfalse
      rw [Vc.eval_mkNot]
      simp [Exp.eval, hok, haBV]
    · rcases List.mem_cons.mp hc' with rfl | hc''
      · refine Or.inl (robust_intro hentryV hdomV
          fun w' _hblk hexit _hguard _hag _hdom => ?_)
        simp only [Vc.exitVar, Exp.eval]
        exact hexit
      · cases hc''

/-- Every expected map definition is either robust (visited block:
established by the execution) or is itself an extension entry
(unvisited block). The two rows share `visited_phi_defHolds` and the
dominated-uses argument with the scalar cases. -/
theorem expectedMapDefs_robust_or_def {P : Program} {σ : State}
    {V : List Nat}
    (hone : singleAssertOK P = true) (hssa : ssaOK P = true)
    (hfwd : forwardOK P = true) (hphi : phiOK P = true)
    (hamo : amoSideOK P = true) (hgf : guardFreeOK P = true)
    (hdc : domClosedOK P = true) (huse : usesOK P = true)
    (hS : Suffix P σ P.entry 0 none V) :
    ∀ md ∈ Vc.expectedMapDefs P,
      DefExt.RobustDef
          (fun t x => (t, x) ∈ DefExt.targets (witnessDefs P V))
          (setBlockVars P V σ) ⟨.map, md.1, md.2⟩
        ∨ (⟨.map, md.1, md.2⟩ : DefExt.Def) ∈ witnessDefs P V := by
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
  intro md hmd
  obtain ⟨b, B, i, c, hB, hci, hcd⟩ := mem_expectedMapDefs hmd
  have hblt : b < P.blocks.length := (List.getElem?_eq_some_iff.mp hB).1
  by_cases hbV : b ∈ V
  · refine Or.inl (robustDef_intro hentryV hdomV
      fun w' hblk _hexit _hguard hag hdom => ?_)
    obtain ⟨x, rhs⟩ := md
    rcases cmdMapDef?_eq_some hcd with ⟨e, rfl, rfl⟩ | ⟨arms, rfl, rfl⟩
    · -- store / alias assignment
      obtain ⟨prev, hfact, -⟩ := hfacts b hbV B i _ hB hci
      simp only [CmdFact] at hfact
      have hu := usesOK_cmd huse hB hci
      simp only [cmdUsesOK] at hu
      have hgfc := guardFree_at hgf (List.mem_of_getElem? hB)
        (List.mem_of_getElem? hci)
      simp only [cmdGuardFree, List.isEmpty_iff] at hgfc
      have hwx : w'.regs .map x = σ.regs .map x := by
        refine hag .map x fun d j hdj => ?_
        obtain ⟨rfl, -⟩ := ssa_unique hssa
          ⟨B, _, hB, hci, by simp [Cmd.def?]⟩ hdj
        exact hbV
      have hevals : (Vc.lower e).eval w' = (Vc.lower e).eval σ := by
        refine eval_congr _ ?_ ?_
        · intro p hp
          exact hdom b hbV p.1 p.2
            (useOK_dom (List.all_eq_true.mp hu p (lower_vars e p hp)))
        · intro q hq
          have := lower_blkVars e q hq
          rw [hgfc] at this
          cases this
      show w'.regs .map x = (Vc.lower e).eval w'
      rw [hwx, hevals, Vc.eval_lower]
      exact hfact
    · -- map phi
      exact visited_phi_defHolds hssa hfwd hphi hamo huse hedge hentryV
        hdomV hfacts hbV hB hci hblt hblk hag
  · exact Or.inr (witnessDefAt_mem_witnessDefs
      ⟨B, c, hB, hci, Vc.cmdMapDef?_unguarded hcd⟩ hbV)

/-! ## Assembly -/

theorem expected_sat {P : Program} {σ : State} {V : List Nat}
    (hone : singleAssertOK P = true) (hssa : ssaOK P = true)
    (hfwd : forwardOK P = true) (hphi : phiOK P = true)
    (hamo : amoSideOK P = true) (hgf : guardFreeOK P = true)
    (hdc : domClosedOK P = true) (huse : usesOK P = true)
    (hS : Suffix P σ P.entry 0 none V) :
    ∀ c ∈ Vc.expected P, c.eval (witness P V σ) = true :=
  DefExt.sat_extend (orderedDefs_witnessDefs hssa huse hphi)
    (expected_robust_or_def hone hssa hfwd hphi hamo hgf hdc huse hS)

theorem expectedMapDefs_sat {P : Program} {σ : State} {V : List Nat}
    (hone : singleAssertOK P = true) (hssa : ssaOK P = true)
    (hfwd : forwardOK P = true) (hphi : phiOK P = true)
    (hamo : amoSideOK P = true) (hgf : guardFreeOK P = true)
    (hdc : domClosedOK P = true) (huse : usesOK P = true)
    (hS : Suffix P σ P.entry 0 none V) :
    ∀ md ∈ Vc.expectedMapDefs P,
      (witness P V σ).regs .map md.1 = md.2.eval (witness P V σ) := by
  have hall := DefExt.sat_extend_defs
    (ds := (Vc.expectedMapDefs P).map fun md =>
      (⟨.map, md.1, md.2⟩ : DefExt.Def))
    (orderedDefs_witnessDefs hssa huse hphi)
    (fun d hd => by
      obtain ⟨md, hmd, rfl⟩ := List.mem_map.mp hd
      exact expectedMapDefs_robust_or_def hone hssa hfwd hphi hamo hgf
        hdc huse hS md hmd)
  intro md hmd
  exact hall _ (List.mem_map.mpr ⟨md, hmd, rfl⟩)

/-! ## Soundness -/

theorem checkVC_sound {P : Program} {vc : Vc.VC}
    (hchk : checkVC P vc = true) {s0 σ : State}
    (hrun : Steps P (Config.init P s0) (.failed σ)) :
    ∃ w, Vc.Sat w vc := by
  rw [checkVC, Bool.and_eq_true] at hchk
  obtain ⟨hchk1, hmdefs⟩ := hchk
  rw [Bool.and_eq_true] at hchk1
  obtain ⟨hwf, hmem⟩ := hchk1
  rw [wellFormed] at hwf
  simp only [Bool.and_eq_true] at hwf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hone, hssa⟩, hfwd⟩, hphi⟩, hamo⟩, hentry⟩, hgf⟩, hdc⟩, huse⟩ := hwf
  obtain ⟨V, hS⟩ := suffix_of_steps hfwd hssa huse hphi hone hrun rfl
  refine ⟨witness P V σ, fun c hc => ?_, fun md hmd => ?_⟩
  · exact expected_sat hone hssa hfwd hphi hamo hgf hdc huse hS c
      (of_decide_eq_true (List.all_eq_true.mp hmem c hc))
  · exact expectedMapDefs_sat hone hssa hfwd hphi hamo hgf hdc huse hS md
      (of_decide_eq_true (List.all_eq_true.mp hmdefs md hmd))

/-- If `checkVC` accepts and the VC is unsatisfiable, the program is
safe: every model of the expected constraint set is refuted, so no
failing execution can exist. -/
theorem checkVC_safe {P : Program} {vc : Vc.VC}
    (hchk : checkVC P vc = true) (hunsat : Vc.Unsat vc) : P.Safe :=
  fun ⟨_s0, _σ, hrun⟩ => hunsat (checkVC_sound hchk hrun)

end Ttac
