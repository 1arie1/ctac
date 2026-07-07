import Ttac.VcWeaken

/-!
# Adequacy: an operational failure reaches EXIT denotationally

`Adequacy P` (`P.Unsafe → ∃ s0, (denot P s0).blks EXIT = true`) is the
one obligation tying the denotational reading back to the operational
semantics. This file proves it. The seed is the **final operational
state σ**: under SSA the run's every value — assigned, phi-selected,
havoc-chosen, or never-written junk — is present in σ, so the fold over
σ recomputes the run.

The invariant carried block by block:

* **Clean registers agree with σ.** A register is *clean* when every
  fold-writing definition site of it (assign or phi; havoc is a fold
  identity, the seed carries its value) is a visited block. The fold
  writes a clean register only at its visited site, and there it writes
  exactly the σ-value: the site's `CmdFact` gives the operational
  equation, and the right-hand side's reads are dominated hence visited
  (`dom_visited`) hence clean — the *no-leak* fact, and the place the
  dominator table earns its keep in the denotational story.
* **Guards match visitedness below the fail block.** A visited block is
  reached (its chain predecessor's guard is true and the taken edge's
  condition, a clean read, is true) and feasible (its assumes hold at σ
  by `CmdFact`, transported by cleanliness). An unvisited block below
  the fail block is unreached: an unvisited predecessor has a false
  guard by induction, and a visited predecessor's edge to it cannot be
  the taken one — the taken edge is unique (`edgeTaken_unique`) and
  goes to the visited successor. Above the fail block guards are
  unconstrained (the fail block's never-executed terminator may
  spuriously activate later blocks), and nothing below reads them:
  edges and phi arms only look backwards.

At the end the single assert's block is active with a false condition
(a clean read), so `reachExit` fires. Composed with the checker:
`checkVCW_safe` — the full operational chain through the denotational
proof, `checkVC`-equivalent in statement.
-/

namespace Ttac

/-! ## Clean registers -/

/-- The register a command writes *in the fold*: assign and phi
targets. Havoc is a definition site but a fold identity. -/
def foldWrites : Cmd → Option (Ty × Nat)
  | .assign t x _ => some (t, x)
  | .phi t x _ => some (t, x)
  | _ => none

theorem foldWrites_def? {c : Cmd} {tx : Ty × Nat}
    (h : foldWrites c = some tx) : c.def? = some tx := by
  cases c <;> simp_all [foldWrites, Cmd.def?]

/-- Every fold-writing definition site of the register is visited. -/
abbrev CleanReg (P : Program) (V : List Nat) (tx : Ty × Nat) : Prop :=
  ∀ (d j : Nat) (B : Block) (c : Cmd),
    P.block? d = some B → B.cmds[j]? = some c →
    foldWrites c = some tx → d ∈ V

abbrev RegsAgree (P : Program) (V : List Nat) (W σ : State) : Prop :=
  ∀ (t : Ty) (x : Nat), CleanReg P V (t, x) → W.regs t x = σ.regs t x

/-- A register read at a visited site is clean: its unique definition
is at the site's block or a dominator, and dominators of visited blocks
are visited. Havoc definitions are clean vacuously. -/
theorem clean_of_use {P : Program} {V : List Nat}
    (hdomV : ∀ u ∈ V, ∀ d ∈ domOf P u, d ∈ V)
    {b : Nat} (hbV : b ∈ V) {tx : Ty × Nat}
    (hdom : ∀ d j, IsDefAt P tx d j → d = b ∨ d ∈ domOf P b) :
    CleanReg P V tx := by
  intro d j B c hB hc hw
  rcases hdom d j ⟨B, c, hB, hc, foldWrites_def? hw⟩ with rfl | hd
  · exact hbV
  · exact hdomV b hbV d hd

/-- The dual for phi-arm sources: dominated at the arm's predecessor. -/
theorem clean_of_armUse {P : Program} {V : List Nat}
    (hdomV : ∀ u ∈ V, ∀ d ∈ domOf P u, d ∈ V)
    {p : Nat} (hpV : p ∈ V) {tx : Ty × Nat}
    (hdom : ∀ d j, IsDefAt P tx d j → d ∈ domOf P p) :
    CleanReg P V tx :=
  fun d j B c hB hc hw =>
    hdomV p hpV d (hdom d j ⟨B, c, hB, hc, foldWrites_def? hw⟩)

theorem denotCmd_regs_ne_fold {P : Program} {W : State} {c : Cmd}
    {u : Ty} {z : Nat} (h : foldWrites c ≠ some (u, z)) :
    (denotCmd P W c).regs u z = W.regs u z := by
  cases c with
  | assign t x e =>
      exact State.upd_regs_of_ne W
        (fun heq => h (by rw [foldWrites, ← heq])) _
  | phi t x arms =>
      exact State.upd_regs_of_ne W
        (fun heq => h (by rw [foldWrites, ← heq])) _
  | havoc t x => rfl
  | assume φ => rfl
  | assert r => rfl

/-- Transport an expression across clean agreement. -/
theorem eval_eq_of_agree {P : Program} {V : List Nat} {W σ : State}
    (hagree : RegsAgree P V W σ) {t : Ty} (e : Exp t)
    (hclean : ∀ p ∈ e.vars, CleanReg P V p)
    (hbnil : e.blkVars = []) : e.eval W = e.eval σ :=
  eval_congr e (fun p hp => hagree p.1 p.2 (hclean p hp))
    (fun q hq => by rw [hbnil] at hq; cases hq)

/-! ## Chain order facts -/

theorem chained_le_getLast {V : List Nat} (hlt : Chained (· < ·) V)
    {z : Nat} (hz : V.getLast? = some z) : ∀ q ∈ V, q ≤ z := by
  induction V with
  | nil => intro q hq; cases hq
  | cons x rest ih =>
      intro q hq
      cases rest with
      | nil =>
          obtain rfl := Option.some.inj hz
          obtain rfl := List.mem_singleton.mp hq
          exact Nat.le_refl _
      | cons y rest' =>
          rw [List.getLast?_cons_cons] at hz
          obtain ⟨hxy, hch⟩ := chained_destruct hlt
          rcases List.mem_cons.mp hq with rfl | hq'
          · exact Nat.le_of_lt (Nat.lt_of_lt_of_le hxy
              (ih hch hz y (List.mem_cons_self ..)))
          · exact ih hch hz q hq'

theorem chained_next_mem {R : Nat → Nat → Prop} {z : Nat} :
    ∀ {V : List Nat}, Chained R V → V.getLast? = some z →
      ∀ {p : Nat}, p ∈ V → p ≠ z → ∃ n ∈ V, R p n := by
  intro V
  induction V with
  | nil => intro _ hz; cases hz
  | cons x rest ih =>
      intro hch hz p hp hne
      cases rest with
      | nil =>
          obtain rfl := Option.some.inj hz
          obtain rfl := List.mem_singleton.mp hp
          exact absurd rfl hne
      | cons y rest' =>
          obtain ⟨hRxy, hch'⟩ := chained_destruct hch
          rw [List.getLast?_cons_cons] at hz
          rcases List.mem_cons.mp hp with rfl | hp'
          · exact ⟨y, List.mem_cons_of_mem _ (List.mem_cons_self ..), hRxy⟩
          · obtain ⟨n, hn, hRn⟩ := ih hch' hz hp' hne
            exact ⟨n, List.mem_cons_of_mem _ hn, hRn⟩

/-- Rebuild a taken edge from an edge record whose condition holds. -/
theorem edgeTaken_of_cond {P : Program} {σ : State} {p k : Nat}
    {cond : BExp} (hmem : (p, cond) ∈ Vc.edgesTo P k)
    (hc : cond.eval σ = true) : EdgeTaken P σ p k := by
  obtain ⟨B', hB', hout⟩ := mem_allEdges_elim (mem_edgesTo.mp hmem)
  refine ⟨B', hB', ?_⟩
  unfold Vc.outEdges at hout
  split at hout
  · cases hout
  · rename_i tgt hterm
    simp only [List.mem_singleton, Prod.mk.injEq] at hout
    obtain ⟨-, rfl, rfl⟩ := hout
    exact Or.inl hterm
  · rename_i creg tt ee hterm
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
      or_false] at hout
    rcases hout with ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩
    · exact Or.inr ⟨creg, _, _, hterm, Or.inl ⟨rfl, by
        simpa [Exp.eval] using hc⟩⟩
    · refine Or.inr ⟨creg, _, _, hterm, Or.inr ⟨rfl, ?_⟩⟩
      simp only [Exp.eval, UnOp.denote, Bool.not_eq_true'] at hc
      exact hc

/-! ## Phi selection

The fold computes `phiRhs`, a guard-ITE over the arms. When the actual
predecessor's guard is true and every other arm's guard is false, the
chain selects the actual arm — the value the run's phi read. -/

theorem phiChain_eval_select {P : Program} {W : State} {t : Ty} {p src : Nat} :
    ∀ (a : Nat × Nat) (rest : List (Nat × Nat)),
      lookupArm (a :: rest) p = some src →
      (Vc.guardOf P p).eval W = true →
      (∀ q s', (q, s') ∈ a :: rest → q ≠ p →
        (Vc.guardOf P q).eval W = false) →
      (Vc.phiChain P t a rest).eval W = W.regs t src
  | (q, s), [], hlk, hp, hq => by
      cases hb : (p == q) with
      | true =>
          have hqp : q = p := (beq_iff_eq.mp hb).symm
          subst hqp
          simp only [lookupArm, List.lookup, hb] at hlk
          obtain rfl := Option.some.inj hlk
          rfl
      | false =>
          simp only [lookupArm, List.lookup, hb] at hlk
          cases hlk
  | (q, s), a' :: r, hlk, hp, hq => by
      simp only [Vc.phiChain, Vc.eval_mkIte]
      cases hb : (p == q) with
      | true =>
          have hqp : q = p := (beq_iff_eq.mp hb).symm
          subst hqp
          simp only [lookupArm, List.lookup, hb] at hlk
          obtain rfl := Option.some.inj hlk
          rw [hp]
          simp [Exp.eval]
      | false =>
          have hqp : q ≠ p := fun h => by rw [h] at hb; simp at hb
          rw [hq q s (List.mem_cons_self ..) hqp]
          simp only [Bool.false_eq_true, if_false]
          refine phiChain_eval_select a' r ?_ hp
            (fun q' s' hmem hne =>
              hq q' s' (List.mem_cons_of_mem _ hmem) hne)
          simpa only [lookupArm, List.lookup, hb] using hlk

/-! ## The per-command agreement step -/

/-- One fold step preserves clean agreement. At an unvisited block the
write target is unclean; at a visited block the written value is the
σ-value: assign via `CmdFact` + clean reads, phi via the selection
lemma (actual predecessor's guard true by G1, others false by G2 +
`visited_amo`). -/
theorem adq_denotCmd_agree {P : Program} {σ : State} {V : List Nat}
    {bf : Nat}
    (hfwd : forwardOK P = true)
    (hphi : phiOK P = true) (hamo : amoSideOK P = true)
    (hgf : guardFreeOK P = true) (huse : usesOK P = true)
    (hedge : Chained (EdgeTaken P σ) V)
    (hdomV : ∀ u ∈ V, ∀ d ∈ domOf P u, d ∈ V)
    (hentryV : P.entry ∈ V)
    (hmaxV : ∀ v ∈ V, v ≤ bf)
    {k : Nat} {B : Block} (hB : P.block? k = some B)
    (hfactsK : k ∈ V → ∀ (i : Nat) (c : Cmd), B.cmds[i]? = some c →
      ∃ prev : Option Nat, CmdFact σ prev c
        ∧ ∀ p, prev = some p → p ∈ V ∧ EdgeTaken P σ p k)
    {i : Nat} {c : Cmd} (hci : B.cmds[i]? = some c)
    {W : State} (hagree : RegsAgree P V W σ)
    (hG1 : ∀ q, q < k → q ∈ V → W.blks q = true)
    (hG2 : ∀ q, q < k → q ∉ V → q < bf → W.blks q = false) :
    RegsAgree P V (denotCmd P W c) σ := by
  have hklt : k < P.blocks.length := (List.getElem?_eq_some_iff.mp hB).1
  cases c with
  | havoc t x => exact hagree
  | assume φ => exact hagree
  | assert r => exact hagree
  | assign t y e =>
      by_cases hkV : k ∈ V
      · -- clean write of the σ-value
        have hu := usesOK_cmd huse hB hci
        simp only [cmdUsesOK] at hu
        have hgfc := guardFree_at hgf (List.mem_of_getElem? hB)
          (List.mem_of_getElem? hci)
        simp only [cmdGuardFree, List.isEmpty_iff] at hgfc
        have hev : e.eval W = e.eval σ :=
          eval_eq_of_agree hagree e
            (fun p hp => clean_of_use hdomV hkV
              (useOK_dom (List.all_eq_true.mp hu p hp))) hgfc
        obtain ⟨prev, hcf, -⟩ := hfactsK hkV i _ hci
        simp only [CmdFact] at hcf
        intro t' x' hclean
        by_cases htx : (t', x') = ((t, y) : Ty × Nat)
        · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp htx
          rw [show denotCmd P W (.assign t' x' e) = W.upd t' x' (e.eval W)
              from rfl,
            State.upd_regs_self, hev, hcf]
        · rw [denotCmd_regs_ne_fold (fun hw => htx (by
            simp only [foldWrites, Option.some.injEq] at hw
            exact hw.symm))]
          exact hagree t' x' hclean
      · -- unclean target: clean registers untouched
        intro t' x' hclean
        rw [denotCmd_regs_ne_fold (fun hw => hkV
          (hclean k i B _ hB hci hw))]
        exact hagree t' x' hclean
  | phi t y arms =>
      by_cases hkV : k ∈ V
      · obtain ⟨prev, hcf, hprev⟩ := hfactsK hkV i _ hci
        simp only [CmdFact] at hcf
        obtain ⟨p, src, rfl, harm, hval⟩ := hcf
        obtain ⟨hpV, -⟩ := hprev p rfl
        have harms : phiArmsOK P k arms = true :=
          phiOK_at hphi hB (List.mem_of_getElem? hci)
        have hparm : (p, src) ∈ arms := lookup_mem harm
        have hplt : p < k := phiArm_lt harms hparm
        -- the actual predecessor's guard is true
        have hgp : (Vc.guardOf P p).eval W = true := by
          unfold Vc.guardOf
          split
          · rfl
          · exact hG1 p hplt hpV
        -- every other arm's guard is false
        have hgq : ∀ q s', (q, s') ∈ arms → q ≠ p →
            (Vc.guardOf P q).eval W = false := by
          intro q s' hqarm hqp
          have hqlt : q < k := phiArm_lt harms hqarm
          by_cases hqV : q ∈ V
          · exact absurd (visited_amo hfwd hamo hedge hklt
              (two_mem_le_length (phiArm_pred harms hqarm)
                (phiArm_pred harms hparm) hqp)
              hqV (phiArm_pred harms hqarm) hpV (phiArm_pred harms hparm)) hqp
          · have hqe : q ≠ P.entry := fun h => hqV (h ▸ hentryV)
            unfold Vc.guardOf
            rw [if_neg hqe]
            exact hG2 q hqlt hqV (Nat.lt_of_lt_of_le hqlt (hmaxV k hkV))
        -- the selected value is the σ-value
        have hu := usesOK_cmd huse hB hci
        simp only [cmdUsesOK] at hu
        have hsrc_clean : CleanReg P V (t, src) :=
          clean_of_armUse hdomV hpV
            (armUseOK_dom (List.all_eq_true.mp hu (p, src) hparm))
        have hsel : (Vc.phiRhs P t arms).eval W = W.regs t src := by
          cases arms with
          | nil => cases hparm
          | cons a rest =>
              exact phiChain_eval_select a rest harm hgp hgq
        intro t' x' hclean
        by_cases htx : (t', x') = ((t, y) : Ty × Nat)
        · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp htx
          rw [show denotCmd P W (.phi t' x' arms)
              = W.upd t' x' ((Vc.phiRhs P t' arms).eval W) from rfl,
            State.upd_regs_self, hsel, hagree t' src hsrc_clean, ← hval]
        · rw [denotCmd_regs_ne_fold (fun hw => htx (by
            simp only [foldWrites, Option.some.injEq] at hw
            exact hw.symm))]
          exact hagree t' x' hclean
      · intro t' x' hclean
        rw [denotCmd_regs_ne_fold (fun hw => hkV
          (hclean k i B _ hB hci hw))]
        exact hagree t' x' hclean

/-- Fold a block's command suffix, preserving clean agreement. -/
theorem adq_cmds_agree {P : Program} {σ : State} {V : List Nat} {bf : Nat}
    (hfwd : forwardOK P = true)
    (hphi : phiOK P = true) (hamo : amoSideOK P = true)
    (hgf : guardFreeOK P = true) (huse : usesOK P = true)
    (hedge : Chained (EdgeTaken P σ) V)
    (hdomV : ∀ u ∈ V, ∀ d ∈ domOf P u, d ∈ V)
    (hentryV : P.entry ∈ V) (hmaxV : ∀ v ∈ V, v ≤ bf)
    {k : Nat} {B : Block} (hB : P.block? k = some B)
    (hfactsK : k ∈ V → ∀ (i : Nat) (c : Cmd), B.cmds[i]? = some c →
      ∃ prev : Option Nat, CmdFact σ prev c
        ∧ ∀ p, prev = some p → p ∈ V ∧ EdgeTaken P σ p k) :
    ∀ (n j : Nat), B.cmds.length ≤ j + n → ∀ (W : State),
      RegsAgree P V W σ →
      (∀ q, q < k → q ∈ V → W.blks q = true) →
      (∀ q, q < k → q ∉ V → q < bf → W.blks q = false) →
      RegsAgree P V ((B.cmds.drop j).foldl (denotCmd P) W) σ := by
  intro n
  induction n with
  | zero =>
      intro j hj W hagree _ _
      rw [List.drop_eq_nil_of_le (by omega), List.foldl_nil]
      exact hagree
  | succ n ih =>
      intro j hj W hagree hG1 hG2
      rcases Nat.lt_or_ge j B.cmds.length with hjlen | hjlen
      · have hcj : B.cmds[j]? = some B.cmds[j] :=
          List.getElem?_eq_getElem hjlen
        rw [List.drop_eq_getElem_cons hjlen, List.foldl_cons]
        refine ih (j + 1) (by omega) _
          (adq_denotCmd_agree hfwd hphi hamo hgf huse hedge hdomV
            hentryV hmaxV hB hfactsK hcj hagree hG1 hG2)
          (fun q hqk hqV => by rw [denotCmd_blks]; exact hG1 q hqk hqV)
          (fun q hqk hqV hqbf => by
            rw [denotCmd_blks]; exact hG2 q hqk hqV hqbf)
      · rw [List.drop_eq_nil_of_le hjlen, List.foldl_nil]
        exact hagree

/-! ## The guard of a processed block -/

/-- A visited block's guard computes true: its chain predecessor is
processed-true and the taken edge's condition is a clean read; its
assumes hold at σ and transport by cleanliness. -/
theorem adq_guard_visited {P : Program} {σ : State} {V : List Nat}
    (hfwd : forwardOK P = true) (hgf : guardFreeOK P = true)
    (huse : usesOK P = true)
    (hedge : Chained (EdgeTaken P σ) V) (hhead : V.head? = some P.entry)
    (hdomV : ∀ u ∈ V, ∀ d ∈ domOf P u, d ∈ V)
    {k : Nat} {B : Block} (hB : P.block? k = some B) (hkV : k ∈ V)
    (hfactsK : ∀ (i : Nat) (c : Cmd), B.cmds[i]? = some c →
      ∃ prev : Option Nat, CmdFact σ prev c
        ∧ ∀ p, prev = some p → p ∈ V ∧ EdgeTaken P σ p k)
    {Wc : State} (hagree : RegsAgree P V Wc σ)
    (hG1 : ∀ q, q < k → q ∈ V → Wc.blks q = true) :
    (reach P Wc k && assumesOK Wc B) = true := by
  rw [Bool.and_eq_true]
  constructor
  · unfold reach
    rw [Bool.or_eq_true]
    by_cases hke : k = P.entry
    · exact Or.inl (decide_eq_true hke)
    · right
      have hkt : k ∈ V.tail := by
        cases V with
        | nil => cases hhead
        | cons v0 rest =>
            obtain rfl := Option.some.inj hhead
            rcases List.mem_cons.mp hkV with rfl | h
            · exact absurd rfl hke
            · exact h
      obtain ⟨p, hpV, hE, -⟩ := chained_pred hedge hedge hkt
      obtain ⟨cond, hcondmem, hcondσ⟩ := hE.edge_cond
      have hplt : p < k := hE.lt hfwd
      obtain ⟨hbnil, hbvars⟩ := edge_cond_vars hcondmem
      have hcondW : cond.eval Wc = cond.eval σ := by
        refine eval_eq_of_agree hagree cond (fun q hq => ?_) hbnil
        obtain ⟨r, B', t', e', rfl, hB', hterm'⟩ := hbvars q hq
        have hterm_use := usesOK_term huse hB'
        simp only [termUsesOK, hterm'] at hterm_use
        exact clean_of_use hdomV hpV (useOK_dom hterm_use)
      apply List.any_eq_true.mpr
      exact ⟨(p, cond), hcondmem, by
        simp only [hG1 p hplt hpV, hcondW, hcondσ, Bool.and_self]⟩
  · unfold assumesOK
    apply List.all_eq_true.mpr
    intro c hc
    cases c with
    | assume φ =>
        obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hc
        obtain ⟨prev, hcf, -⟩ := hfactsK i _ hi
        simp only [CmdFact] at hcf
        have hu := usesOK_cmd huse hB hi
        simp only [cmdUsesOK] at hu
        have hgfc := guardFree_at hgf (List.mem_of_getElem? hB) hc
        simp only [cmdGuardFree, List.isEmpty_iff] at hgfc
        show φ.eval Wc = true
        rw [eval_eq_of_agree hagree φ
          (fun p hp => clean_of_use hdomV hkV
            (useOK_dom (List.all_eq_true.mp hu p hp))) hgfc]
        exact hcf
    | assign t y e => rfl
    | havoc t y => rfl
    | phi t y arms => rfl
    | assert r => rfl

/-- An unvisited block below the fail block is unreached: an unvisited
predecessor's guard is false by induction, and a visited predecessor's
edge to it cannot be the taken one — the taken edge is unique and goes
to the visited chain successor. -/
theorem adq_guard_unvisited {P : Program} {σ : State} {V : List Nat}
    {bf : Nat}
    (hfwd : forwardOK P = true) (huse : usesOK P = true)
    (hedge : Chained (EdgeTaken P σ) V) (hlast : V.getLast? = some bf)
    (hentryV : P.entry ∈ V)
    (hdomV : ∀ u ∈ V, ∀ d ∈ domOf P u, d ∈ V)
    {k : Nat} (hkV : k ∉ V) (hkbf : k < bf)
    {Wc : State} (hagree : RegsAgree P V Wc σ)
    (hG2 : ∀ q, q < k → q ∉ V → q < bf → Wc.blks q = false) :
    reach P Wc k = false := by
  unfold reach
  rw [Bool.or_eq_false_iff]
  refine ⟨decide_eq_false (fun hke => hkV (hke ▸ hentryV)), ?_⟩
  apply List.any_eq_false.mpr
  rintro ⟨p, cond⟩ hmem
  intro hcon
  rw [Bool.and_eq_true] at hcon
  have hplt : p < k := pred_lt hfwd (mem_predsOf.mpr ⟨cond, hmem⟩)
  by_cases hpV : p ∈ V
  · have hpbf : p ≠ bf := by omega
    obtain ⟨w, hwV, hEpw⟩ := chained_next_mem hedge hlast hpV hpbf
    obtain ⟨hbnil, hbvars⟩ := edge_cond_vars hmem
    have hcondW : cond.eval Wc = cond.eval σ := by
      refine eval_eq_of_agree hagree cond (fun q hq => ?_) hbnil
      obtain ⟨r, B', t', e', rfl, hB', hterm'⟩ := hbvars q hq
      have hterm_use := usesOK_term huse hB'
      simp only [termUsesOK, hterm'] at hterm_use
      exact clean_of_use hdomV hpV (useOK_dom hterm_use)
    have hcσ : cond.eval σ = true := by rw [← hcondW]; exact hcon.2
    have hk_eq : w = k :=
      edgeTaken_unique hEpw (edgeTaken_of_cond hmem hcσ)
    exact hkV (hk_eq ▸ hwV)
  · have hfalse := hcon.1
    rw [hG2 p hplt hpV (by omega)] at hfalse
    cases hfalse

/-! ## The main induction over the fold -/

theorem adq_prefix {P : Program} {σ : State} {V : List Nat} {bf : Nat}
    (hfwd : forwardOK P = true) (hphi : phiOK P = true)
    (hamo : amoSideOK P = true) (hgf : guardFreeOK P = true)
    (huse : usesOK P = true)
    (hedge : Chained (EdgeTaken P σ) V) (hhead : V.head? = some P.entry)
    (hlast : V.getLast? = some bf)
    (hdomV : ∀ u ∈ V, ∀ d ∈ domOf P u, d ∈ V)
    (hfacts : ∀ v ∈ V, ∀ (B : Block) (i : Nat) (c : Cmd),
      P.block? v = some B → B.cmds[i]? = some c →
      ∃ prev : Option Nat, CmdFact σ prev c
        ∧ ∀ p, prev = some p → p ∈ V ∧ EdgeTaken P σ p v) :
    ∀ k, k ≤ P.blocks.length →
      RegsAgree P V (prefixState P σ k) σ
      ∧ (∀ q, q < k → q ∈ V → (prefixState P σ k).blks q = true)
      ∧ (∀ q, q < k → q ∉ V → q < bf →
          (prefixState P σ k).blks q = false) := by
  have hentryV : P.entry ∈ V := by
    cases V with
    | nil => cases hhead
    | cons v0 rest =>
        obtain rfl := Option.some.inj hhead
        exact List.mem_cons_self ..
  have hmaxV : ∀ v ∈ V, v ≤ bf :=
    chained_le_getLast (hedge.imp fun _ _ h => h.lt hfwd) hlast
  intro k
  induction k with
  | zero =>
      intro _
      exact ⟨fun t x _ => rfl,
        fun q hq => absurd hq (by omega),
        fun q hq => absurd hq (by omega)⟩
  | succ k ih =>
      intro hk1
      have hk : k < P.blocks.length := by omega
      obtain ⟨hagree, hG1, hG2⟩ := ih (by omega)
      have hB : P.block? k = some P.blocks[k] := List.getElem?_eq_getElem hk
      have hfactsK : k ∈ V → ∀ (i : Nat) (c : Cmd),
          P.blocks[k].cmds[i]? = some c →
          ∃ prev : Option Nat, CmdFact σ prev c
            ∧ ∀ p, prev = some p → p ∈ V ∧ EdgeTaken P σ p k :=
        fun hkV i c hci => hfacts k hkV _ i c hB hci
      have hagree' : RegsAgree P V
          (P.blocks[k].cmds.foldl (denotCmd P) (prefixState P σ k)) σ := by
        have h := adq_cmds_agree hfwd hphi hamo hgf huse hedge hdomV
          hentryV hmaxV hB hfactsK P.blocks[k].cmds.length 0 (by omega)
          (prefixState P σ k) hagree hG1 hG2
        simpa using h
      have hblkc : (P.blocks[k].cmds.foldl (denotCmd P)
          (prefixState P σ k)).blks = (prefixState P σ k).blks :=
        cmdsFold_blks P _ _
      have hregs : (prefixState P σ (k + 1)).regs
          = (P.blocks[k].cmds.foldl (denotCmd P) (prefixState P σ k)).regs := by
        rw [prefixState_succ]
        simp only [denotBlock, hB]
      have hblk_self : (prefixState P σ (k + 1)).blks k
          = (reach P (P.blocks[k].cmds.foldl (denotCmd P)
                (prefixState P σ k)) k
              && assumesOK (P.blocks[k].cmds.foldl (denotCmd P)
                (prefixState P σ k)) P.blocks[k]) := by
        rw [prefixState_succ]
        simp only [denotBlock, hB]
        rw [Function.update_self]
      refine ⟨?_, ?_, ?_⟩
      · intro t x hcl
        rw [show (prefixState P σ (k + 1)).regs t x
            = (P.blocks[k].cmds.foldl (denotCmd P)
                (prefixState P σ k)).regs t x from by rw [hregs]]
        exact hagree' t x hcl
      · intro q hq hqV
        rcases Nat.lt_or_ge q k with hqk | hqk
        · rw [prefixState_succ, denotBlock_blks_ne (by omega)]
          exact hG1 q hqk hqV
        · obtain rfl : q = k := by omega
          rw [hblk_self]
          exact adq_guard_visited hfwd hgf huse hedge hhead hdomV hB hqV
            (hfactsK hqV) hagree'
            (fun q' hq' hq'V => by rw [hblkc]; exact hG1 q' hq' hq'V)
      · intro q hq hqV hqbf
        rcases Nat.lt_or_ge q k with hqk | hqk
        · rw [prefixState_succ, denotBlock_blks_ne (by omega)]
          exact hG2 q hqk hqV hqbf
        · obtain rfl : q = k := by omega
          rw [hblk_self,
            adq_guard_unvisited hfwd huse hedge hlast hentryV hdomV hqV
              hqbf hagree'
              (fun q' hq' hq'V hq'bf => by
                rw [hblkc]; exact hG2 q' hq' hq'V hq'bf)]
          rfl

/-! ## Adequacy -/

/-- **An operational failure reaches EXIT denotationally.** The seed is
the final operational state; the single assert's block is active with a
false condition, so `reachExit` fires. -/
theorem adequacy_of_flags {P : Program}
    (hone : singleAssertOK P = true) (hssa : ssaOK P = true)
    (hfwd : forwardOK P = true) (hphi : phiOK P = true)
    (hamo : amoSideOK P = true) (hentry : entryOK P = true)
    (hgf : guardFreeOK P = true) (hdc : domClosedOK P = true)
    (huse : usesOK P = true) : Adequacy P := by
  rintro ⟨s0op, σ, hrun⟩
  obtain ⟨V, hentryV, hhead, hedge, hfacts, bf, Bf, pcf, cf, hlastV,
    hBf, hcf, hcffalse⟩ :=
    forwardStructural hone hssa huse hfwd hphi hentry hrun
  refine ⟨σ, ?_⟩
  rw [denot_blks_exit]
  have hdomV := dom_visited hdc hfwd hedge hhead
  obtain ⟨hagree, hG1, -⟩ := adq_prefix hfwd hphi hamo hgf huse hedge
    hhead hlastV hdomV hfacts P.blocks.length (Nat.le_refl _)
  obtain ⟨aB, iA, okReg, BA, heqs, hBA, hcA, -⟩ := singleAssert_shape hone
  obtain ⟨hb, -, hc⟩ := singleAssert_unique hone hBf hcf hBA hcA
  unfold reachExit
  rw [heqs]
  simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.and_eq_true,
    Bool.not_eq_true']
  have haBlt : aB < P.blocks.length := (List.getElem?_eq_some_iff.mp hBA).1
  have haBV : aB ∈ V := hb ▸ getLast?_mem hlastV
  refine ⟨hG1 aB haBlt haBV, ?_⟩
  have hu := usesOK_cmd huse hBA hcA
  simp only [cmdUsesOK] at hu
  rw [hagree .bool okReg (clean_of_use hdomV haBV (useOK_dom hu)), ← hc]
  exact hcffalse

theorem adequacy {P : Program} (hwf : wellFormed P = true) : Adequacy P := by
  rw [wellFormed] at hwf
  simp only [Bool.and_eq_true] at hwf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hone, hssa⟩, hfwd⟩, hphi⟩, hamo⟩, hentry⟩, hgf⟩, hdc⟩, huse⟩ := hwf
  exact adequacy_of_flags hone hssa hfwd hphi hamo hentry hgf hdc huse

/-! ## The full operational chain through the denotational proof -/

/-- The weakening-table checker is sound for the *operational*
semantics: `checkVC_safe`-equivalent in statement, proved via the
denotational model and adequacy — no `DefExt`, no witness. -/
theorem checkVCW_safe {P : Program} {vc : Vc.VC}
    (hchk : checkVCW P vc = true) (hunsat : Vc.Unsat vc) : P.Safe := by
  have hwf : wellFormed P = true := by
    rw [checkVCW, Bool.and_eq_true, Bool.and_eq_true] at hchk
    exact hchk.1.1
  exact safe_of_safe_denot (adequacy hwf) (checkVCW_safe_denot hchk hunsat)

/-- The original checker through the denotational route — the same
statement as `checkVC_safe`, proved by a fully independent path. -/
theorem checkVC_safe_via_denot {P : Program} {vc : Vc.VC}
    (hchk : checkVC P vc = true) (hunsat : Vc.Unsat vc) : P.Safe := by
  have hwf : wellFormed P = true := by
    rw [checkVC, Bool.and_eq_true, Bool.and_eq_true] at hchk
    exact hchk.1.1
  exact safe_of_safe_denot (adequacy hwf) (checkVC_safe_denot hchk hunsat)

/-- The site-tagged weakening checker, operationally: no global
expected VC computed, no `DefExt`, no witness. -/
theorem checkVCWAnn_safe {P : Program} {a : Vc.AnnVC}
    (hchk : checkVCWAnn P a = true) (hunsat : a.Unsat) : P.Safe := by
  have hwf : wellFormed P = true := by
    rw [checkVCWAnn, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
      Bool.and_eq_true] at hchk
    exact hchk.1.1.1.1
  exact safe_of_safe_denot (adequacy hwf) (checkVCWAnn_safe_denot hchk hunsat)

end Ttac
