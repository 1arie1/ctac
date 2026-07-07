import Ttac.VcCfgPath

/-!
# A denotational semantics as last-block reachability

The semantics the checker's soundness is proven against: make **every
block "execute"** — in topological order, with
inactive blocks acting as identity *except* that phi nodes are always
computed as `eval(phiRhs)` (the same guard-selected ITE the VC uses).
The result is one **total** state whose guard component is the
reachability valuation of a single feasible path, and which is a *model
of the VC by construction*: each command's defining equation holds
because the fold computed exactly that value.

It is **not** about "unsafe" or a distinguished failing state. Convert
`assert c` into `assume c`; then there are no asserts, only assumes, and
the failing continuation is just an edge to the synthetic last block
`BLK_EXIT` guarded by `¬c`. The only dynamic notion is **stuck**: a
feasible path is one that never hits a false `assume`. Everything
reduces to a single question — **does some seed reach the last block?**
`Safe_denot P` is exactly "the last block is unreachable". EXIT is then
just another block reached by the same `reach` rule, so the VC's
`objective` constraints are EXIT's edge-feasibility/reachability
constraints — discharged like any other block's, not a special case.

The checker's soundness is `checkVC ∧ Unsat ⇒ Safe_denot` — a
by-construction argument with no definitional extension and no
dominance. The bridge to the operational `Program.Safe` (`Adequacy`:
a real execution reaching `.failed` induces a seed reaching EXIT) is
stated here and proven in `VcAdequacy`.
-/

namespace Ttac

open Vc

/-! ## The denotational fold

`denotCmd` is the register effect of one command on the running total
state. `assign`/`phi` always write (unconditional — so their equations
hold by construction, at every block, active or not); `havoc` keeps the
input value already present in the seed state (the seed is the
nondeterminism oracle, matching `State`'s havoc-at-entry design);
`assume`/`assert` touch no register. -/
def denotCmd (P : Program) (W : State) : Cmd → State
  | .assign t x e => W.upd t x (e.eval W)
  | .havoc _ _ => W
  | .phi t x arms => W.upd t x ((phiRhs P t arms).eval W)
  | .assume _ => W
  | .assert _ => W

/-- Reachability of block `b` from the guards set for earlier blocks:
entry is always reached; a non-entry block is reached iff some incoming
edge has a reached source and a true edge condition. -/
def reach (P : Program) (W : State) (b : Nat) : Bool :=
  decide (b = P.entry)
    || (edgesTo P b).any (fun e => W.blks e.1 && e.2.eval W)

/-- `assume`-feasibility of a block: every `assume` in it holds at the
post-command state. A reached-but-infeasible block is stuck (its guard
is false), so its guarded facts are vacuous — matching the operational
"stuck at a false assume = vacuously safe". -/
def assumesOK (W : State) (B : Block) : Bool :=
  B.cmds.all fun c => match c with | .assume φ => φ.eval W | _ => true

/-- Process one block: run its register effects, then set its guard to
`reached ∧ feasible`. -/
def denotBlock (P : Program) (W : State) (b : Nat) : State :=
  match P.block? b with
  | none => W
  | some B =>
      let Wc := B.cmds.foldl (denotCmd P) W
      { Wc with blks := Function.update Wc.blks b (reach P Wc b && assumesOK Wc B) }

/-- Reachability of the synthetic last block `BLK_EXIT`. `assert c` is
read as `assume c`, so the only edge into EXIT is the failing branch of
an assert: from a feasibly-reached assert block whose condition is
false. This is the *same* shape as `reach` for a real block — EXIT's one
in-edge is `(assert-block, ¬cond)`. -/
def reachExit (P : Program) (W : State) : Bool :=
  (assertSites P).any fun s => W.blks s.1 && !(W.regs .bool s.2.2)

/-- The total denotational state induced by a seed `s0` (the havoc /
entry oracle): fold every block in index order, then set the last-block
guard `BLK_EXIT` by the same reachability rule. -/
def denot (P : Program) (s0 : State) : State :=
  let W := (List.range P.blocks.length).foldl (denotBlock P) s0
  { W with blks := Function.update W.blks P.blocks.length (reachExit P W) }

/-! ## Safety = the last block is unreachable -/

/-- A program is denotationally safe iff no seed drives the fold to a
state whose last-block guard is set — i.e. EXIT is unreachable. There is
no "unsafe" notion; this is pure reachability of the last block. -/
def Safe_denot (P : Program) : Prop :=
  ∀ s0 : State, (denot P s0).blks P.blocks.length = false

/-! ## The adequacy seam (factored out)

`Adequacy P` is the only obligation that ties the denotational reading
back to the operational semantics: a real execution reaching `.failed`
induces a seed that reaches EXIT. It is the home of the no-leak /
path-structure reasoning (a dead block's registers never feed live
computation), stated VC-free and — the bet — proved once,
language-generically, rather than re-entangled per command in a
robustness lemma. -/
def Adequacy (P : Program) : Prop :=
  P.Unsafe → ∃ s0 : State, (denot P s0).blks P.blocks.length = true

/-- Given adequacy, denotational safety transfers to operational safety.
This is the whole point of the factoring: our checker proves
`Safe_denot`; `Adequacy` (owned elsewhere) closes the gap. -/
theorem safe_of_safe_denot {P : Program} (had : Adequacy P)
    (h : Safe_denot P) : P.Safe := by
  intro hu
  obtain ⟨s0, hs0⟩ := had hu
  exact absurd (h s0) (by rw [hs0]; simp)

/-- Counterexample certificate: a seed whose denotational run reaches
the last block refutes `Safe_denot`. Since `denot` is a computable fold,
the hypothesis is a closed `Bool` equation — a solver model transpiled
into a seed is certified by evaluation (`native_decide`); no trace or
proof object is needed. A wrong seed merely fails to evaluate to `true`
(completeness loss, never a soundness hole). -/
theorem not_safe_denot_of_seed {P : Program} (s0 : State)
    (h : (denot P s0).blks P.blocks.length = true) : ¬Safe_denot P :=
  fun hs => by rw [hs s0] at h; exact Bool.false_ne_true h

/-! ## Lemma B: a path state is a model, by construction (dominance-free)

Given the *denotational-execution facts* — the guard valuation is a real
forward path (`hblk`/`hedge`, the structural hypothesis A), the last
block is reached (`hexit`), the executed-command facts hold (`hfacts`),
and the phi equations hold by construction (`hphi`, since the fold
assigns `eval(phiRhs)`) — any path state `w` satisfies the whole VC. No
definitional extension, no dominance: CFG constraints and the objective come from
`cfgConstraints_sat` (EXIT is just another reached block), guarded facts
from `factConstraints_sat`, phi equations/at-most-one directly. This is
the payoff: the checker's local obligation is a clean assembly of the
dominance-free path lemmas; all the hardness is isolated in establishing
the hypotheses (Lemma A / adequacy). -/

/-- A phi (or assign) defining equation `y = e` holds when the state's
register already equals `e` — the by-construction content. -/
theorem eqConstraint_eval {w : State} {t : Ty} {y : Nat} {e : Exp t}
    {c : BExp} (heq : eqConstraint? t y e = some c)
    (hval : w.regs t y = e.eval w) : c.eval w = true := by
  cases t with
  | int =>
      simp only [eqConstraint?] at heq
      obtain rfl := Option.some.inj heq
      simp [Exp.eval, BinOp.denote, hval]
  | bool =>
      simp only [eqConstraint?] at heq
      obtain rfl := Option.some.inj heq
      simp [Exp.eval, BinOp.denote, hval]
  | map => simp [eqConstraint?] at heq

theorem expected_sat_of_path {P : Program} {w : State} {V : List Nat}
    (hone : singleAssertOK P = true) (hfwd : forwardOK P = true)
    (hamo : amoSideOK P = true) (hphiOK : phiOK P = true)
    (hentryV : P.entry ∈ V) (hhead : V.head? = some P.entry)
    (hblk : ∀ q, q < P.blocks.length → w.blks q = decide (q ∈ V))
    (hexit : w.blks P.blocks.length = true)
    (hedge : Chained (EdgeTaken P w) V)
    (hfacts : ∀ v ∈ V, ∀ (B : Block) (i : Nat) (c' : Cmd) (f : BExp),
      P.block? v = some B → B.cmds[i]? = some c' → c'.factB = some f →
      f.eval w = true)
    (hphi : ∀ (b : Nat) (B : Block) (t : Ty) (y : Nat) (arms : PhiArms),
      P.block? b = some B → (Cmd.phi t y arms) ∈ B.cmds →
      w.regs t y = (Vc.phiRhs P t arms).eval w)
    (hfail : ∀ aB iA okReg, Vc.assertSites P = [(aB, iA, okReg)] →
      aB ∈ V ∧ w.regs .bool okReg = false) :
    ∀ c ∈ Vc.expected P, c.eval w = true := by
  obtain ⟨aB, iA, okReg, BA, heqs, hBA, hcA, -⟩ := singleAssert_shape hone
  have haBlt : aB < P.blocks.length := (List.getElem?_eq_some_iff.mp hBA).1
  obtain ⟨haBV, hok⟩ := hfail aB iA okReg heqs
  intro c hc
  have hexp : Vc.expected P
      = (P.blocks.zipIdx.map fun (B, b) =>
          (B.cmds.map (Vc.cmdConstraints P b)).flatten).flatten
        ++ Vc.cfgConstraints P ++ Vc.objective P aB okReg := by
    unfold Vc.expected; rw [heqs]
  rw [hexp, List.mem_append, List.mem_append] at hc
  rcases hc with (hc | hc) | hc
  · -- per-command constraints
    rw [List.mem_flatten] at hc
    obtain ⟨L, hL, hcL⟩ := hc
    rw [List.mem_map] at hL
    obtain ⟨⟨B, b⟩, hbmem, rfl⟩ := hL
    rw [List.mem_flatten] at hcL
    obtain ⟨L2, hL2, hcL2⟩ := hcL
    rw [List.mem_map] at hL2
    obtain ⟨cmd, hcmdmem, rfl⟩ := hL2
    have hB : P.block? b = some B := List.mem_zipIdx_iff_getElem?.mp hbmem
    have hblt : b < P.blocks.length := (List.getElem?_eq_some_iff.mp hB).1
    rcases mem_cmdConstraints hcL2 with hfc | ⟨t, y, arms, rfl, hshape⟩
    · -- guarded fact
      refine factConstraints_sat hentryV hblt hblk (fun hbV f hf => ?_) c hfc
      obtain ⟨i, hci⟩ := List.mem_iff_getElem?.mp hcmdmem
      exact hfacts b hbV B i _ f hB hci hf
    · have harms : phiArmsOK P b arms = true := phiOK_at hphiOK hB hcmdmem
      rcases hshape with heq | ⟨hlen2, hcamo⟩
      · -- phi equation, by construction
        exact eqConstraint_eval heq (hphi b B t y arms hB hcmdmem)
      · -- phi at-most-one
        obtain ⟨g1, g2, hg1, hg2, hne, rfl⟩ := Vc.mem_amoClauses hcamo
        rw [List.mem_map] at hg1 hg2
        obtain ⟨⟨q1, s1⟩, hq1arm, rfl⟩ := hg1
        obtain ⟨⟨q2, s2⟩, hq2arm, rfl⟩ := hg2
        have hq1lt : q1 < P.blocks.length := by
          have := phiArm_lt harms hq1arm; omega
        have hq2lt : q2 < P.blocks.length := by
          have := phiArm_lt harms hq2arm; omega
        simp only [Exp.eval, UnOp.denote, BinOp.denote,
          guard_eval hentryV hblk hq1lt, guard_eval hentryV hblk hq2lt,
          Bool.or_eq_true]
        by_cases h1 : q1 ∈ V
        · by_cases h2 : q2 ∈ V
          · exact absurd (visited_amo hfwd hamo hedge hblt
              (two_mem_le_length (phiArm_pred harms hq1arm)
                (phiArm_pred harms hq2arm) (fun h => hne (by rw [h])))
              h1 (phiArm_pred harms hq1arm) h2 (phiArm_pred harms hq2arm))
              (fun h => hne (by rw [h]))
          · right; simp [h2]
        · left; simp [h1]
  · -- CFG constraints
    exact cfgConstraints_sat hfwd hamo hentryV hhead hblk hedge c hc
  · -- objective
    rcases List.mem_cons.mp hc with rfl | hc'
    · have hex : (Vc.exitVar P).eval w = true := by
        unfold Vc.exitVar; exact hexit
      rw [Vc.eval_mkImp, hex]
      simp only [Bool.not_true, Bool.false_or]
      rw [Vc.eval_mkAnd2, guard_eval hentryV hblk haBlt, Vc.eval_mkNot]
      simp [Exp.eval, decide_eq_true haBV, hok]
    · rcases List.mem_cons.mp hc' with rfl | hfalse
      · unfold Vc.exitVar; exact hexit
      · cases hfalse

/-! ## Lemma A, by-construction half: the fold delivers its equations

The denotational fold processes blocks in index order and, under SSA,
each register is written at most once — so every defining equation the
fold establishes survives to the final state. This section proves the
four by-construction hypotheses of Lemma B (`hblk`, `hfacts`, `hphi`,
`hmap`, plus `hfail`) directly from `denot`'s definition. The residue —
that the guard-true set is a chained `EdgeTaken` path from entry — is
the reachability core, taken as a hypothesis in the assembly below. -/

/-- State after processing blocks `0..k-1`. -/
def prefixState (P : Program) (s0 : State) (k : Nat) : State :=
  (List.range k).foldl (denotBlock P) s0

theorem prefixState_succ (P : Program) (s0 : State) (k : Nat) :
    prefixState P s0 (k + 1) = denotBlock P (prefixState P s0 k) k := by
  unfold prefixState
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem denotCmd_blks (P : Program) (W : State) (c : Cmd) :
    (denotCmd P W c).blks = W.blks := by
  cases c <;> simp [denotCmd]

theorem denotCmd_regs_ne {P : Program} {W : State} {c : Cmd} {u : Ty} {z : Nat}
    (h : ∀ tx, c.def? = some tx → tx ≠ (u, z)) :
    (denotCmd P W c).regs u z = W.regs u z := by
  cases c with
  | assign t x e => exact State.upd_regs_of_ne W (Ne.symm (h (t, x) rfl)) _
  | phi t x arms => exact State.upd_regs_of_ne W (Ne.symm (h (t, x) rfl)) _
  | havoc t x => rfl
  | assume φ => rfl
  | assert r => rfl

theorem cmdsFold_blks (P : Program) : ∀ (cs : List Cmd) (W : State),
    (cs.foldl (denotCmd P) W).blks = W.blks
  | [], _ => rfl
  | c :: cs, W => by
      rw [List.foldl_cons, cmdsFold_blks P cs, denotCmd_blks]

theorem cmdsFold_regs_ne {P : Program} {u : Ty} {z : Nat} :
    ∀ {cs : List Cmd} {W : State},
      (∀ c ∈ cs, ∀ tx, c.def? = some tx → tx ≠ (u, z)) →
      (cs.foldl (denotCmd P) W).regs u z = W.regs u z
  | [], _, _ => rfl
  | c :: cs, W, h => by
      rw [List.foldl_cons,
        cmdsFold_regs_ne (fun c' hc' => h c' (List.mem_cons_of_mem _ hc')),
        denotCmd_regs_ne (h c (List.mem_cons_self ..))]

theorem denotBlock_blks_ne {P : Program} {W : State} {b q : Nat} (h : q ≠ b) :
    (denotBlock P W b).blks q = W.blks q := by
  cases hB : P.block? b with
  | none => simp [denotBlock, hB]
  | some B => simp [denotBlock, hB, Function.update_of_ne h, cmdsFold_blks]

theorem denotBlock_regs_ne {P : Program} {W : State} {b : Nat} {u : Ty} {z : Nat}
    (h : ∀ i, ¬ IsDefAt P (u, z) b i) :
    (denotBlock P W b).regs u z = W.regs u z := by
  unfold denotBlock
  cases hB : P.block? b with
  | none => rfl
  | some B =>
      show (B.cmds.foldl (denotCmd P) W).regs u z = W.regs u z
      refine cmdsFold_regs_ne (fun c hc tx htx heq => ?_)
      subst heq
      obtain ⟨i, hci⟩ := List.mem_iff_getElem?.mp hc
      exact h i ⟨B, c, hB, hci, htx⟩

theorem prefixState_regs_stable {P : Program} {s0 : State} {u : Ty} {z : Nat}
    {k : Nat} (h : ∀ d j, IsDefAt P (u, z) d j → d < k) :
    ∀ {m : Nat}, k ≤ m →
      (prefixState P s0 m).regs u z = (prefixState P s0 k).regs u z := by
  intro m
  induction m with
  | zero => intro hk; obtain rfl : k = 0 := Nat.le_zero.mp hk; rfl
  | succ m ih =>
      intro hk
      rcases Nat.lt_or_ge m k with hlt | hge
      · obtain rfl : k = m + 1 := by omega
        rfl
      · rw [prefixState_succ,
          denotBlock_regs_ne (fun i hdef => by have := h _ _ hdef; omega),
          ih hge]

theorem prefixState_blks_stable {P : Program} {s0 : State} {q k : Nat}
    (hq : q < k) :
    ∀ {m : Nat}, k ≤ m →
      (prefixState P s0 m).blks q = (prefixState P s0 k).blks q := by
  intro m
  induction m with
  | zero => intro hk; obtain rfl : k = 0 := Nat.le_zero.mp hk; rfl
  | succ m ih =>
      intro hk
      rcases Nat.lt_or_ge m k with hlt | hge
      · obtain rfl : k = m + 1 := by omega
        rfl
      · rw [prefixState_succ, denotBlock_blks_ne (by omega), ih hge]

theorem denot_regs (P : Program) (s0 : State) :
    (denot P s0).regs = (prefixState P s0 P.blocks.length).regs := rfl

theorem denot_blks_lt {P : Program} {s0 : State} {q : Nat}
    (hq : q < P.blocks.length) :
    (denot P s0).blks q = (prefixState P s0 P.blocks.length).blks q := by
  have h : q ≠ P.blocks.length := by omega
  simp only [denot, Function.update_of_ne h]
  rfl

theorem denot_blks_exit (P : Program) (s0 : State) :
    (denot P s0).blks P.blocks.length
      = reachExit P (prefixState P s0 P.blocks.length) := by
  simp only [denot, Function.update_self]
  rfl

/-! ### Per-command equations through the fold

`FoldFact` is the defining equation the fold establishes for a command:
`assign`/`phi` targets equal their right-hand sides (phi's is the
guard-selected `phiRhs`, at *every* block — the "execute dead phi"
step). The freeze (`foldFact_upd`) is the single SSA argument: a write
at a strictly later position touches neither the target (unique def)
nor the right-hand side's reads (defined before). -/

def FoldFact (P : Program) (W : State) : Cmd → Prop
  | .assign t y e => W.regs t y = e.eval W
  | .phi t y arms => W.regs t y = (Vc.phiRhs P t arms).eval W
  | _ => True

theorem foldFact_upd {P : Program} (hssa : ssaOK P = true)
    (huse : usesOK P = true) (hphiOK : phiOK P = true) {v i : Nat}
    {Bv : Block} {c : Cmd} (hBv : P.block? v = some Bv)
    (hci : Bv.cmds[i]? = some c) {b pc : Nat}
    (hlt : posLt (v, i) (b, pc) = true)
    {t : Ty} {y : Nat} (hydef : IsDefAt P (t, y) b pc) (val : t.denote)
    {W : State} (h : FoldFact P W c) : FoldFact P (W.upd t y val) c := by
  have hu := usesOK_cmd huse hBv hci
  simp only [cmdUsesOK] at hu
  cases c with
  | assign t' y' e =>
      simp only [FoldFact] at h ⊢
      have hy'ne : ((t', y') : Ty × Nat) ≠ (t, y) :=
        write_ne_of_before hlt (fun d j hdj => by
          obtain ⟨rfl, rfl⟩ := ssa_unique hssa ⟨Bv, _, hBv, hci, rfl⟩ hdj
          simp [posLt]) hydef
      have hev : e.eval (W.upd t y val) = e.eval W :=
        eval_congr e (fun p hp => State.upd_regs_of_ne W
          (write_ne_of_before hlt
            (fun d j hdj => posLt_succ (expUsesOK_before hu p hp d j hdj))
            hydef) val)
          (fun q _ => by rw [State.upd_blks])
      rw [State.upd_regs_of_ne W hy'ne val, hev]
      exact h
  | phi t' y' arms =>
      simp only [FoldFact] at h ⊢
      have hy'ne : ((t', y') : Ty × Nat) ≠ (t, y) :=
        write_ne_of_before hlt (fun d j hdj => by
          obtain ⟨rfl, rfl⟩ := ssa_unique hssa ⟨Bv, _, hBv, hci, rfl⟩ hdj
          simp [posLt]) hydef
      have hev : (Vc.phiRhs P t' arms).eval (W.upd t y val)
          = (Vc.phiRhs P t' arms).eval W :=
        eval_congr _ (fun p hp => State.upd_regs_of_ne W
          (write_ne_of_before hlt (fun d j hdj => by
            have := phi_src_lt huse hphiOK hBv hci p hp d j hdj
            simp only [posLt, Bool.or_eq_true, Bool.and_eq_true,
              decide_eq_true_eq]
            omega) hydef) val)
          (fun q _ => by rw [State.upd_blks])
      rw [State.upd_regs_of_ne W hy'ne val, hev]
      exact h
  | havoc t' y' => trivial
  | assume φ => trivial
  | assert r => trivial

theorem foldFact_denotCmd {P : Program} (hssa : ssaOK P = true)
    (huse : usesOK P = true) (hphiOK : phiOK P = true) {v i : Nat}
    {Bv : Block} {c : Cmd} (hBv : P.block? v = some Bv)
    (hci : Bv.cmds[i]? = some c) {b j : Nat} {Bb : Block} {c' : Cmd}
    (hBb : P.block? b = some Bb) (hcj : Bb.cmds[j]? = some c')
    (hlt : posLt (v, i) (b, j) = true)
    {W : State} (h : FoldFact P W c) : FoldFact P (denotCmd P W c') c := by
  cases c' with
  | assign t x e =>
      exact foldFact_upd hssa huse hphiOK hBv hci hlt
        ⟨Bb, _, hBb, hcj, rfl⟩ _ h
  | phi t x arms =>
      exact foldFact_upd hssa huse hphiOK hBv hci hlt
        ⟨Bb, _, hBb, hcj, rfl⟩ _ h
  | havoc t x => exact h
  | assume φ => exact h
  | assert r => exact h

/-- Establishment: executing a command makes its own equation true. The
right-hand side's reads are defined strictly before this position, so
the write does not disturb them. -/
theorem foldFact_establish {P : Program} (huse : usesOK P = true)
    (hphiOK : phiOK P = true) {v j : Nat} {Bv : Block} {c : Cmd}
    (hBv : P.block? v = some Bv) (hcj : Bv.cmds[j]? = some c)
    (W : State) : FoldFact P (denotCmd P W c) c := by
  have hu := usesOK_cmd huse hBv hcj
  simp only [cmdUsesOK] at hu
  cases c with
  | assign t y e =>
      simp only [FoldFact, denotCmd]
      have hne : ∀ p ∈ e.vars, p ≠ ((t, y) : Ty × Nat) := by
        intro p hp heq
        have hd := expUsesOK_before hu p hp v j
          (by rw [heq]; exact ⟨Bv, _, hBv, hcj, rfl⟩)
        rw [posLt_irrefl] at hd
        cases hd
      have hev : e.eval (W.upd t y (e.eval W)) = e.eval W :=
        eval_congr e
          (fun p hp => State.upd_regs_of_ne W (hne p hp) (e.eval W))
          (fun q _ => by rw [State.upd_blks])
      rw [State.upd_regs_self, hev]
  | phi t y arms =>
      simp only [FoldFact, denotCmd]
      have hne : ∀ p ∈ (Vc.phiRhs P t arms).vars,
          p ≠ ((t, y) : Ty × Nat) := by
        intro p hp heq
        have := phi_src_lt huse hphiOK hBv hcj p hp v j
          (by rw [heq]; exact ⟨Bv, _, hBv, hcj, rfl⟩)
        omega
      have hev : (Vc.phiRhs P t arms).eval
            (W.upd t y ((Vc.phiRhs P t arms).eval W))
          = (Vc.phiRhs P t arms).eval W :=
        eval_congr _
          (fun p hp => State.upd_regs_of_ne W (hne p hp)
            ((Vc.phiRhs P t arms).eval W))
          (fun q _ => by rw [State.upd_blks])
      rw [State.upd_regs_self, hev]
  | havoc t y => trivial
  | assume φ => trivial
  | assert r => trivial

theorem posLt_same_block {v i j : Nat} (h : i < j) :
    posLt (v, i) (v, j) = true := by
  simp [posLt, h]

/-- Fold a block's suffix: previously established equations survive and
each executed command's equation is established. Fuel-indexed to keep
the recursion structural. -/
theorem blockFacts_go {P : Program} (hssa : ssaOK P = true)
    (huse : usesOK P = true) (hphiOK : phiOK P = true)
    {v : Nat} {Bv : Block} (hBv : P.block? v = some Bv) :
    ∀ (n j : Nat), Bv.cmds.length ≤ j + n → ∀ (W : State),
      (∀ (i : Nat) (c : Cmd), Bv.cmds[i]? = some c → i < j → FoldFact P W c) →
      ∀ (i : Nat) (c : Cmd), Bv.cmds[i]? = some c →
        FoldFact P ((Bv.cmds.drop j).foldl (denotCmd P) W) c := by
  intro n
  induction n with
  | zero =>
      intro j hj W hinv i c hci
      have hlen : Bv.cmds.length ≤ j := by omega
      rw [List.drop_eq_nil_of_le hlen, List.foldl_nil]
      have hi : i < Bv.cmds.length := (List.getElem?_eq_some_iff.mp hci).1
      exact hinv i c hci (by omega)
  | succ n ih =>
      intro j hj W hinv i c hci
      rcases Nat.lt_or_ge j Bv.cmds.length with hjlen | hjlen
      · have hcj : Bv.cmds[j]? = some Bv.cmds[j] :=
          List.getElem?_eq_getElem hjlen
        rw [List.drop_eq_getElem_cons hjlen, List.foldl_cons]
        refine ih (j + 1) (by omega) (denotCmd P W Bv.cmds[j])
          (fun i' c' hci' hi' => ?_) i c hci
        rcases Nat.lt_or_ge i' j with hij | hij
        · exact foldFact_denotCmd hssa huse hphiOK hBv hci' hBv hcj
            (posLt_same_block hij) (hinv i' c' hci' hij)
        · have hii : i' = j := by omega
          rw [hii] at hci'
          obtain rfl : c' = Bv.cmds[j] := Option.some.inj (hci'.symm.trans hcj)
          exact foldFact_establish huse hphiOK hBv hci' W
      · rw [List.drop_eq_nil_of_le hjlen, List.foldl_nil]
        have hi : i < Bv.cmds.length := (List.getElem?_eq_some_iff.mp hci).1
        exact hinv i c hci (by omega)

/-- End-of-block equations: at the end of block `v`'s command fold,
every command of `v` satisfies its defining equation. -/
theorem blockFacts {P : Program} (hssa : ssaOK P = true)
    (huse : usesOK P = true) (hphiOK : phiOK P = true)
    {v : Nat} {Bv : Block} (hBv : P.block? v = some Bv) (W : State) :
    ∀ (i : Nat) (c : Cmd), Bv.cmds[i]? = some c →
      FoldFact P (Bv.cmds.foldl (denotCmd P) W) c := by
  have h := blockFacts_go hssa huse hphiOK hBv Bv.cmds.length 0
    (by omega) W (fun i c _ hi => absurd hi (by omega))
  simpa using h

/-! ### Transport to the final state

A register whose definitions all lie in blocks `≤ v` has its final
value fixed at the end of block `v`'s command fold; guards of blocks
`< v` are likewise fixed. Together (via `eval_congr`) the end-of-block
equations transport to `denot P s0`. -/

theorem denot_regs_of_defsLe {P : Program} {s0 : State} {v : Nat}
    {Bv : Block} (hBv : P.block? v = some Bv) {u : Ty} {z : Nat}
    (h : ∀ d j, IsDefAt P (u, z) d j → d ≤ v) :
    (denot P s0).regs u z
      = (Bv.cmds.foldl (denotCmd P) (prefixState P s0 v)).regs u z := by
  have hvlt : v < P.blocks.length := (List.getElem?_eq_some_iff.mp hBv).1
  have h1 : (denot P s0).regs u z
      = (prefixState P s0 (v + 1)).regs u z := by
    rw [denot_regs]
    exact prefixState_regs_stable
      (fun d j hd => Nat.lt_succ_of_le (h d j hd)) hvlt
  rw [h1, prefixState_succ]
  simp only [denotBlock, hBv]

theorem denot_blks_of_lt {P : Program} {s0 : State} {v : Nat}
    {Bv : Block} (hBv : P.block? v = some Bv) {q : Nat} (hq : q < v) :
    (denot P s0).blks q
      = (Bv.cmds.foldl (denotCmd P) (prefixState P s0 v)).blks q := by
  have hvlt : v < P.blocks.length := (List.getElem?_eq_some_iff.mp hBv).1
  rw [cmdsFold_blks, denot_blks_lt (by omega),
    prefixState_blks_stable hq (by omega)]

theorem eval_denot_eq_block {P : Program} {s0 : State} {v : Nat}
    {Bv : Block} (hBv : P.block? v = some Bv) {t : Ty} (e : Exp t)
    (hvars : ∀ p ∈ e.vars, ∀ d j, IsDefAt P p d j → d ≤ v)
    (hblks : ∀ q ∈ e.blkVars, q < v) :
    e.eval (denot P s0)
      = e.eval (Bv.cmds.foldl (denotCmd P) (prefixState P s0 v)) :=
  eval_congr e
    (fun p hp => denot_regs_of_defsLe hBv (hvars p hp))
    (fun q hq => denot_blks_of_lt hBv (hblks q hq))

/-- The final guard of a real block is exactly what its `denotBlock`
processing computed: reached-and-feasible at the end of its own fold. -/
theorem denot_blks_char {P : Program} {s0 : State} {v : Nat} {Bv : Block}
    (hBv : P.block? v = some Bv) :
    (denot P s0).blks v
      = (reach P (Bv.cmds.foldl (denotCmd P) (prefixState P s0 v)) v
          && assumesOK (Bv.cmds.foldl (denotCmd P) (prefixState P s0 v)) Bv) := by
  have hvlt : v < P.blocks.length := (List.getElem?_eq_some_iff.mp hBv).1
  rw [denot_blks_lt hvlt,
    prefixState_blks_stable (Nat.lt_succ_self v) (by omega : v + 1 ≤ P.blocks.length),
    prefixState_succ]
  simp only [denotBlock, hBv]
  rw [Function.update_self]

/-! ### The phi-arm guard inventory -/

theorem phiChain_blkVars {P : Program} {t : Ty} :
    ∀ (a : Nat × Nat) (rest : List (Nat × Nat)),
      ∀ q ∈ (Vc.phiChain P t a rest).blkVars,
        ∃ s, (q, s) ∈ a :: rest
  | (q0, s0), [], q, hq => by
      simp [Vc.phiChain, Exp.blkVars] at hq
  | (q0, s0), a' :: rest', q, hq => by
      rcases mkIte_blkVars q hq with hg | hs | ht
      · unfold Vc.guardOf at hg
        split at hg
        · cases hg
        · simp only [Exp.blkVars, List.mem_singleton] at hg
          subst hg
          exact ⟨s0, List.mem_cons_self ..⟩
      · simp [Exp.blkVars] at hs
      · obtain ⟨s, hmem⟩ := phiChain_blkVars a' rest' q ht
        exact ⟨s, List.mem_cons_of_mem _ hmem⟩

theorem phiRhs_blkVars {P : Program} {t : Ty} {arms : PhiArms} :
    ∀ q ∈ (Vc.phiRhs P t arms).blkVars, ∃ s, (q, s) ∈ arms := by
  cases arms with
  | nil => intro q hq; simp [Vc.phiRhs, Exp.blkVars] at hq
  | cons a rest => exact phiChain_blkVars a rest

/-! ### The by-construction hypotheses of Lemma B -/

/-- Every phi equation holds at the final denotational state — at every
block, visited or not (the fold computed `phiRhs` unconditionally). -/
theorem denot_phi {P : Program} {s0 : State} (hssa : ssaOK P = true)
    (huse : usesOK P = true) (hphiOK : phiOK P = true)
    {b : Nat} {Bv : Block} {t : Ty} {y : Nat} {arms : PhiArms}
    (hBv : P.block? b = some Bv) (hmem : (Cmd.phi t y arms) ∈ Bv.cmds) :
    (denot P s0).regs t y = (Vc.phiRhs P t arms).eval (denot P s0) := by
  obtain ⟨i, hci⟩ := List.mem_iff_getElem?.mp hmem
  have hfact := blockFacts hssa huse hphiOK hBv (prefixState P s0 b) i _ hci
  simp only [FoldFact] at hfact
  have harms : phiArmsOK P b arms = true := phiOK_at hphiOK hBv hmem
  rw [denot_regs_of_defsLe hBv (fun d j hd => by
      obtain ⟨hdb, -⟩ := ssa_unique hssa ⟨Bv, _, hBv, hci, rfl⟩ hd
      omega),
    eval_denot_eq_block hBv _
      (fun p hp d j hd => Nat.le_of_lt (phi_src_lt huse hphiOK hBv hci p hp d j hd))
      (fun q hq => by
        obtain ⟨s, hqs⟩ := phiRhs_blkVars q hq
        exact phiArm_lt harms hqs)]
  exact hfact

/-- Every assign equation holds at the final denotational state. -/
theorem denot_assign {P : Program} {s0 : State} (hssa : ssaOK P = true)
    (huse : usesOK P = true) (hphiOK : phiOK P = true)
    (hgf : guardFreeOK P = true)
    {b : Nat} {Bv : Block} {i : Nat} {t : Ty} {y : Nat} {e : Exp t}
    (hBv : P.block? b = some Bv) (hci : Bv.cmds[i]? = some (.assign t y e)) :
    (denot P s0).regs t y = e.eval (denot P s0) := by
  have hfact := blockFacts hssa huse hphiOK hBv (prefixState P s0 b) i _ hci
  simp only [FoldFact] at hfact
  have hu := usesOK_cmd huse hBv hci
  simp only [cmdUsesOK] at hu
  have hgfc := guardFree_at hgf (List.mem_of_getElem? hBv)
    (List.mem_of_getElem? hci)
  simp only [cmdGuardFree, List.isEmpty_iff] at hgfc
  rw [denot_regs_of_defsLe hBv (fun d j hd => by
      obtain ⟨hdb, -⟩ := ssa_unique hssa ⟨Bv, _, hBv, hci, rfl⟩ hd
      omega),
    eval_denot_eq_block hBv e
      (fun p hp d j hd => by
        have := expUsesOK_before hu p hp d j hd
        simp only [posLt, Bool.or_eq_true, Bool.and_eq_true,
          decide_eq_true_eq] at this
        omega)
      (fun q hq => by rw [hgfc] at hq; cases hq)]
  exact hfact

/-- Every assume of a guard-true block holds at the final state: the
guard folds in `assumesOK` at the end of the block, and the condition's
reads are frozen from there on. -/
theorem denot_assume {P : Program} {s0 : State} (huse : usesOK P = true)
    (hgf : guardFreeOK P = true)
    {b : Nat} {Bv : Block} {i : Nat} {φ : BExp}
    (hBv : P.block? b = some Bv) (hci : Bv.cmds[i]? = some (.assume φ))
    (hguard : (denot P s0).blks b = true) :
    φ.eval (denot P s0) = true := by
  rw [denot_blks_char hBv, Bool.and_eq_true] at hguard
  have hφ := List.all_eq_true.mp hguard.2 _ (List.mem_of_getElem? hci)
  simp only at hφ
  have hu := usesOK_cmd huse hBv hci
  simp only [cmdUsesOK] at hu
  have hgfc := guardFree_at hgf (List.mem_of_getElem? hBv)
    (List.mem_of_getElem? hci)
  simp only [cmdGuardFree, List.isEmpty_iff] at hgfc
  rw [eval_denot_eq_block hBv φ
    (fun p hp d j hd => by
      have := expUsesOK_before hu p hp d j hd
      simp only [posLt, Bool.or_eq_true, Bool.and_eq_true,
        decide_eq_true_eq] at this
      omega)
    (fun q hq => by rw [hgfc] at hq; cases hq)]
  exact hφ

/-! ### Assembly: the guard-true set and the Lemma B hypotheses -/

/-- The blocks the denotational run activates, in index order. -/
def activeList (P : Program) (s0 : State) : List Nat :=
  (List.range P.blocks.length).filter (fun q => (denot P s0).blks q)

theorem mem_activeList {P : Program} {s0 : State} {q : Nat} :
    q ∈ activeList P s0
      ↔ q < P.blocks.length ∧ (denot P s0).blks q = true := by
  simp [activeList, List.mem_filter, List.mem_range]

theorem denot_hblk {P : Program} {s0 : State} {q : Nat}
    (hq : q < P.blocks.length) :
    (denot P s0).blks q = decide (q ∈ activeList P s0) := by
  by_cases h : (denot P s0).blks q = true
  · simp [mem_activeList, hq, h]
  · rw [Bool.not_eq_true] at h
    simp [mem_activeList, h]

/-- The `hfacts` hypothesis: every `factB` fact of an active block holds
at the final state (assign by its equation, assume by the guard). -/
theorem denot_factB {P : Program} {s0 : State} (hssa : ssaOK P = true)
    (huse : usesOK P = true) (hphiOK : phiOK P = true)
    (hgf : guardFreeOK P = true) :
    ∀ v ∈ activeList P s0, ∀ (B : Block) (i : Nat) (c' : Cmd) (f : BExp),
      P.block? v = some B → B.cmds[i]? = some c' → c'.factB = some f →
      f.eval (denot P s0) = true := by
  intro v hv B i c' f hB hci hf
  cases c' with
  | assign t y e =>
      simp only [Cmd.factB] at hf
      exact eqConstraint_eval hf (denot_assign hssa huse hphiOK hgf hB hci)
  | assume φ =>
      obtain rfl := Option.some.inj hf
      exact denot_assume huse hgf hB hci (mem_activeList.mp hv).2
  | havoc t y => cases hf
  | phi t y arms => cases hf
  | assert r => cases hf

/-- One site's map definition holds at the final state (assign via
`lower`-invariance, phi via `denot_phi`) — the per-site form the
site-tagged checker consumes directly. -/
theorem denot_mapDef {P : Program} {s0 : State} (hssa : ssaOK P = true)
    (huse : usesOK P = true) (hphiOK : phiOK P = true)
    (hgf : guardFreeOK P = true)
    {b : Nat} {B : Block} {c : Cmd} {md : Nat × MExp}
    (hB : P.block? b = some B) (hc : c ∈ B.cmds)
    (hcd : Vc.cmdMapDef? P c = some md) :
    (denot P s0).regs .map md.1 = md.2.eval (denot P s0) := by
  obtain ⟨i, hci⟩ := List.mem_iff_getElem?.mp hc
  obtain ⟨x, rhs⟩ := md
  rcases cmdMapDef?_eq_some hcd with ⟨e, rfl, rfl⟩ | ⟨arms, rfl, rfl⟩
  · rw [Vc.eval_lower]
    exact denot_assign hssa huse hphiOK hgf hB hci
  · exact denot_phi hssa huse hphiOK hB (List.mem_of_getElem? hci)

/-- The `hmap` hypothesis: every expected map definition holds at the
final state. -/
theorem denot_map {P : Program} {s0 : State} (hssa : ssaOK P = true)
    (huse : usesOK P = true) (hphiOK : phiOK P = true)
    (hgf : guardFreeOK P = true) :
    ∀ md ∈ Vc.expectedMapDefs P,
      (denot P s0).regs .map md.1 = md.2.eval (denot P s0) := by
  intro md hmd
  obtain ⟨b, B, i, c, hB, hci, hcd⟩ := mem_expectedMapDefs hmd
  exact denot_mapDef hssa huse hphiOK hgf hB (List.mem_of_getElem? hci) hcd

/-- The `hfail` hypothesis: a reached EXIT names the (single) assert
site — its block active, its condition false. -/
theorem denot_fail {P : Program} {s0 : State}
    (hexit : (denot P s0).blks P.blocks.length = true) :
    ∀ aB iA okReg, Vc.assertSites P = [(aB, iA, okReg)] →
      aB ∈ activeList P s0 ∧ (denot P s0).regs .bool okReg = false := by
  intro aB iA okReg hsites
  rw [denot_blks_exit, reachExit, hsites] at hexit
  simp only [List.any_cons, List.any_nil, Bool.or_false,
    Bool.and_eq_true, Bool.not_eq_true'] at hexit
  obtain ⟨B, hB, -⟩ := mem_assertSites.mp
    (by rw [hsites]; exact List.mem_cons_self .. :
      (aB, iA, okReg) ∈ Vc.assertSites P)
  have haBlt : aB < P.blocks.length := (List.getElem?_eq_some_iff.mp hB).1
  refine ⟨mem_activeList.mpr ⟨haBlt, ?_⟩, hexit.2⟩
  rw [denot_blks_lt haBlt]
  exact hexit.1

/-- Lemma B, packaged as VC satisfaction: a path state (plus the
by-construction map definitions `hmap`) is a full model of the VC. -/
theorem denot_sat_of_path {P : Program} {w : State} {V : List Nat}
    (hone : singleAssertOK P = true) (hfwd : forwardOK P = true)
    (hamo : amoSideOK P = true) (hphiOK : phiOK P = true)
    (hentryV : P.entry ∈ V) (hhead : V.head? = some P.entry)
    (hblk : ∀ q, q < P.blocks.length → w.blks q = decide (q ∈ V))
    (hexit : w.blks P.blocks.length = true)
    (hedge : Chained (EdgeTaken P w) V)
    (hfacts : ∀ v ∈ V, ∀ (B : Block) (i : Nat) (c' : Cmd) (f : BExp),
      P.block? v = some B → B.cmds[i]? = some c' → c'.factB = some f →
      f.eval w = true)
    (hphi : ∀ (b : Nat) (B : Block) (t : Ty) (y : Nat) (arms : PhiArms),
      P.block? b = some B → (Cmd.phi t y arms) ∈ B.cmds →
      w.regs t y = (Vc.phiRhs P t arms).eval w)
    (hfail : ∀ aB iA okReg, Vc.assertSites P = [(aB, iA, okReg)] →
      aB ∈ V ∧ w.regs .bool okReg = false)
    (hmap : ∀ md ∈ Vc.expectedMapDefs P, w.regs .map md.1 = md.2.eval w) :
    Vc.Sat w { constraints := Vc.expected P, mapDefs := Vc.expectedMapDefs P } :=
  ⟨expected_sat_of_path hone hfwd hamo hphiOK hentryV hhead hblk hexit hedge
    hfacts hphi hfail, hmap⟩

/-! ## The capstone: by-construction half done, reachability core isolated

Everything Lemma B needs is now derived from `denot`'s definition —
except the three *reachability-core* facts about the guard-true set
(entry active, entry first, consecutive actives edge-connected). Those
are exactly the relocated adequacy content; they appear here as the
only remaining hypotheses. -/

theorem denot_sat_of_reach {P : Program} {s0 : State}
    (hone : singleAssertOK P = true) (hssa : ssaOK P = true)
    (hfwd : forwardOK P = true) (hamo : amoSideOK P = true)
    (hphiOK : phiOK P = true) (huse : usesOK P = true)
    (hgf : guardFreeOK P = true)
    (hexit : (denot P s0).blks P.blocks.length = true)
    -- the reachability core (Lemma A's remaining obligations):
    (hentryV : P.entry ∈ activeList P s0)
    (hhead : (activeList P s0).head? = some P.entry)
    (hedge : Chained (EdgeTaken P (denot P s0)) (activeList P s0)) :
    Vc.Sat (denot P s0)
      { constraints := Vc.expected P, mapDefs := Vc.expectedMapDefs P } :=
  denot_sat_of_path hone hfwd hamo hphiOK hentryV hhead
    (fun _ hq => denot_hblk hq) hexit hedge
    (denot_factB hssa huse hphiOK hgf)
    (fun _ _ _ _ _ hB hmem => denot_phi hssa huse hphiOK hB hmem)
    (denot_fail hexit)
    (denot_map hssa huse hphiOK hgf)

/-! ## The reachability core

The three remaining hypotheses say the guard-true set is a chained
`EdgeTaken` path from entry. The argument needs no dominance and no
witness: (1) an active non-entry block has an active predecessor whose
edge was taken (`reach` unfolded at the block's own processing state,
transported to the final state); (2) a block's taken out-edge is
*unique* — `goto` has one edge, `ifGoto`'s conditions are exclusive at
any one state — so two chains from entry cannot diverge; (3) strong
induction turns (1) + (2) into "adjacent actives are edge-connected". -/

/-- (2) A block's taken out-edge is unique at a fixed state. -/
theorem edgeTaken_unique {P : Program} {s : State} {p w1 w2 : Nat}
    (h1 : EdgeTaken P s p w1) (h2 : EdgeTaken P s p w2) : w1 = w2 := by
  obtain ⟨B, hB, hs1⟩ := h1
  obtain ⟨B', hB', hs2⟩ := h2
  obtain rfl : B = B' := Option.some.inj (hB.symm.trans hB')
  rcases hs1 with hg1 | ⟨c1, t1, e1, hif1, harm1⟩
  · rcases hs2 with hg2 | ⟨c2, t2, e2, hif2, harm2⟩
    · rw [hg1] at hg2
      exact Terminator.goto.inj hg2
    · rw [hg1] at hif2; cases hif2
  · rcases hs2 with hg2 | ⟨c2, t2, e2, hif2, harm2⟩
    · rw [hg2] at hif1; cases hif1
    · rw [hif1] at hif2
      obtain ⟨rfl, rfl, rfl⟩ := Terminator.ifGoto.inj hif2
      rcases harm1 with ⟨rfl, hc1⟩ | ⟨rfl, hc1⟩ <;>
        rcases harm2 with ⟨rfl, hc2⟩ | ⟨rfl, hc2⟩ <;>
        first
          | rfl
          | (rw [hc1] at hc2; cases hc2)

/-- (1) An active non-entry block has an active predecessor with its
edge taken at the final state. -/
theorem denot_active_pred {P : Program} {s0 : State}
    (hfwd : forwardOK P = true) (huse : usesOK P = true)
    {w : Nat} {Bw : Block} (hBw : P.block? w = some Bw)
    (hactive : (denot P s0).blks w = true) (hne : w ≠ P.entry) :
    ∃ p, (denot P s0).blks p = true ∧ p < w
      ∧ EdgeTaken P (denot P s0) p w := by
  have hwlt : w < P.blocks.length := (List.getElem?_eq_some_iff.mp hBw).1
  rw [denot_blks_char hBw, Bool.and_eq_true] at hactive
  have hreach := hactive.1
  unfold reach at hreach
  rw [Bool.or_eq_true, decide_eq_true_eq] at hreach
  rcases hreach with rfl | hany
  · exact absurd rfl hne
  · obtain ⟨⟨p, cond⟩, hmem, hpc⟩ := List.any_eq_true.mp hany
    rw [Bool.and_eq_true] at hpc
    have hplt : p < w := pred_lt hfwd (mem_predsOf.mpr ⟨cond, hmem⟩)
    -- the predecessor's guard, transported end-of-block-w → final
    have hpact : (denot P s0).blks p = true := by
      rw [denot_blks_lt (by omega),
        prefixState_blks_stable hplt (by omega : w ≤ P.blocks.length)]
      rw [cmdsFold_blks] at hpc
      exact hpc.1
    -- the edge condition, transported end-of-block-w → final
    obtain ⟨hbnil, hbvars⟩ := edge_cond_vars hmem
    have hcond : cond.eval (denot P s0) = true := by
      rw [eval_denot_eq_block hBw cond
        (fun q hq d j hd => by
          obtain ⟨r, B', t', e', rfl, hB', hterm'⟩ := hbvars q hq
          have hterm_use := usesOK_term huse hB'
          simp only [termUsesOK, hterm'] at hterm_use
          have := useOK_before hterm_use d j hd
          simp only [posLt, Bool.or_eq_true, Bool.and_eq_true,
            decide_eq_true_eq] at this
          omega)
        (fun q hq => by rw [hbnil] at hq; cases hq)]
      exact hpc.2
    -- rebuild the EdgeTaken shape from the edge's syntactic form
    obtain ⟨B', hB', hout⟩ := mem_allEdges_elim (mem_edgesTo.mp hmem)
    refine ⟨p, hpact, hplt, B', hB', ?_⟩
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
          simpa [Exp.eval] using hcond⟩⟩
      · refine Or.inr ⟨creg, _, _, hterm, Or.inr ⟨rfl, ?_⟩⟩
        simp only [Exp.eval, UnOp.denote, Bool.not_eq_true'] at hcond
        exact hcond

theorem entry_eq_zero {P : Program} (h : entryOK P = true) :
    P.entry = 0 := by
  rw [entryOK, Bool.and_eq_true] at h
  exact of_decide_eq_true h.1

/-! ### Adjacency in the active set -/

/-- `u` and `w` are adjacent members of `A`: both in, `u < w`, nothing
of `A` strictly between. -/
def AdjIn (A : List Nat) (u w : Nat) : Prop :=
  u ∈ A ∧ w ∈ A ∧ u < w ∧ ∀ q ∈ A, q ≤ u ∨ w ≤ q

/-- Between two members there is an adjacent next member. -/
theorem adjIn_next : ∀ (n : Nat) {A : List Nat} {p u : Nat}, u - p ≤ n →
    p ∈ A → u ∈ A → p < u → ∃ q, AdjIn A p q ∧ q ≤ u := by
  intro n
  induction n with
  | zero => intro A p u h hp hu hpu; omega
  | succ n ih =>
      intro A p u h hp hu hpu
      by_cases hex : ∃ r ∈ A, p < r ∧ r < u
      · obtain ⟨r, hr, hpr, hru⟩ := hex
        obtain ⟨q, hq, hqr⟩ := ih (by omega) hp hr hpr
        exact ⟨q, hq, by omega⟩
      · refine ⟨u, ⟨hp, hu, hpu, fun q hq => ?_⟩, Nat.le_refl u⟩
        have hnq : ¬(p < q ∧ q < u) := fun hc => hex ⟨q, hq, hc.1, hc.2⟩
        omega

/-- (3) Adjacent actives are edge-connected: strong induction on the
upper block. The chosen active predecessor `p` of `w` sits at or below
`u`; were it strictly below, its own adjacent successor `q ≤ u` would be
edge-connected by the induction hypothesis, and edge uniqueness would
force `q = w > u` — contradiction. -/
theorem denot_adj_edge {P : Program} {s0 : State}
    (hfwd : forwardOK P = true) (huse : usesOK P = true)
    (hentry : entryOK P = true) :
    ∀ w, w < P.blocks.length → (denot P s0).blks w = true → w ≠ P.entry →
      ∀ u, AdjIn (activeList P s0) u w →
        EdgeTaken P (denot P s0) u w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
      intro hwlt hwact hwne u hadj
      obtain ⟨Bw, hBw⟩ : ∃ B, P.block? w = some B :=
        ⟨P.blocks[w], List.getElem?_eq_getElem hwlt⟩
      obtain ⟨p, hpact, hplt, hpE⟩ :=
        denot_active_pred hfwd huse hBw hwact hwne
      have hpA : p ∈ activeList P s0 :=
        mem_activeList.mpr ⟨by omega, hpact⟩
      have hpu : p ≤ u := by
        rcases hadj.2.2.2 p hpA with h | h
        · exact h
        · omega
      rcases Nat.eq_or_lt_of_le hpu with rfl | hplt_u
      · exact hpE
      · obtain ⟨q, hadj_pq, hqu⟩ := adjIn_next (u - p) (Nat.le_refl _)
          hpA hadj.1 hplt_u
        have hqA := hadj_pq.2.1
        have hpq : p < q := hadj_pq.2.2.1
        have huw : u < w := hadj.2.2.1
        have hq := mem_activeList.mp hqA
        have hent := entry_eq_zero hentry
        have hqne : q ≠ P.entry := by omega
        have hqE : EdgeTaken P (denot P s0) p q :=
          ih q (by omega) hq.1 hq.2 hqne p hadj_pq
        have : w = q := edgeTaken_unique hpE hqE
        omega

/-! ### From adjacency to the chained path -/

theorem adjIn_tail {x : Nat} {rest : List Nat}
    (hpw : List.Pairwise (· < ·) (x :: rest)) {u w : Nat}
    (h : AdjIn rest u w) : AdjIn (x :: rest) u w := by
  obtain ⟨hu, hw, huw, hq⟩ := h
  refine ⟨List.mem_cons_of_mem _ hu, List.mem_cons_of_mem _ hw, huw,
    fun q hqm => ?_⟩
  rcases List.mem_cons.mp hqm with rfl | hqm'
  · exact Or.inl (Nat.le_of_lt
      ((List.pairwise_cons.mp hpw).1 u hu))
  · exact hq q hqm'

/-- A sorted list all of whose adjacent pairs satisfy `R` is `R`-chained. -/
theorem chained_of_adj {R : Nat → Nat → Prop} :
    ∀ {L : List Nat}, List.Pairwise (· < ·) L →
      (∀ u w, AdjIn L u w → R u w) → Chained R L
  | [], _, _ => trivial
  | [_], _, _ => trivial
  | x :: y :: rest, hpw, hadj => by
      have hxy : x < y := (List.pairwise_cons.mp hpw).1 y (by simp)
      refine ⟨hadj x y ⟨by simp, by simp, hxy, fun q hq => ?_⟩, ?_⟩
      · rcases List.mem_cons.mp hq with rfl | hq'
        · exact Or.inl (Nat.le_refl _)
        · rcases List.mem_cons.mp hq' with rfl | hq''
          · exact Or.inr (Nat.le_refl _)
          · exact Or.inr (Nat.le_of_lt
              ((List.pairwise_cons.mp (List.pairwise_cons.mp hpw).2).1
                q hq''))
      · exact chained_of_adj (List.pairwise_cons.mp hpw).2
          (fun u w h => hadj u w (adjIn_tail hpw h))

theorem activeList_pairwise (P : Program) (s0 : State) :
    List.Pairwise (· < ·) (activeList P s0) :=
  List.pairwise_lt_range.filter _

/-! ### The three reachability facts, discharged -/

theorem denot_hedge {P : Program} {s0 : State}
    (hfwd : forwardOK P = true) (huse : usesOK P = true)
    (hentry : entryOK P = true) :
    Chained (EdgeTaken P (denot P s0)) (activeList P s0) := by
  refine chained_of_adj (activeList_pairwise P s0) (fun u w hadj => ?_)
  have hw := mem_activeList.mp hadj.2.1
  have hu := mem_activeList.mp hadj.1
  have hwne : w ≠ P.entry := by
    have hent := entry_eq_zero hentry
    have huw : u < w := hadj.2.2.1
    have hu0 : 0 ≤ u := Nat.zero_le u
    omega
  exact denot_adj_edge hfwd huse hentry w hw.1 hw.2 hwne u hadj

theorem denot_hentry {P : Program} {s0 : State}
    (hfwd : forwardOK P = true) (huse : usesOK P = true)
    {v : Nat} (hv : v ∈ activeList P s0) :
    P.entry ∈ activeList P s0
      ∧ (activeList P s0).head? = some P.entry := by
  cases hA : activeList P s0 with
  | nil => rw [hA] at hv; cases hv
  | cons h rest =>
      have hpw := activeList_pairwise P s0
      rw [hA] at hpw
      have hhA : h ∈ activeList P s0 := by rw [hA]; exact List.mem_cons_self ..
      have hh := mem_activeList.mp hhA
      have hhe : h = P.entry := by
        by_contra hne
        obtain ⟨Bh, hBh⟩ : ∃ B, P.block? h = some B :=
          ⟨P.blocks[h], List.getElem?_eq_getElem hh.1⟩
        obtain ⟨p, hpact, hplt, -⟩ :=
          denot_active_pred hfwd huse hBh hh.2 hne
        have hpA : p ∈ activeList P s0 :=
          mem_activeList.mpr ⟨by omega, hpact⟩
        rw [hA] at hpA
        rcases List.mem_cons.mp hpA with rfl | hp'
        · omega
        · have := (List.pairwise_cons.mp hpw).1 p hp'
          omega
      subst hhe
      exact ⟨List.mem_cons_self .., rfl⟩

/-! ### Lemma A complete: a reached EXIT makes the fold a model -/

theorem denot_sat {P : Program} {s0 : State}
    (hone : singleAssertOK P = true) (hssa : ssaOK P = true)
    (hfwd : forwardOK P = true) (hphiOK : phiOK P = true)
    (hamo : amoSideOK P = true) (hentry : entryOK P = true)
    (hgf : guardFreeOK P = true) (huse : usesOK P = true)
    (hexit : (denot P s0).blks P.blocks.length = true) :
    Vc.Sat (denot P s0)
      { constraints := Vc.expected P, mapDefs := Vc.expectedMapDefs P } := by
  obtain ⟨aB, iA, okReg, BA, heqs, hBA, hcA, -⟩ := singleAssert_shape hone
  obtain ⟨haBV, -⟩ := denot_fail hexit aB iA okReg heqs
  obtain ⟨hentryV, hhead⟩ := denot_hentry hfwd huse haBV
  exact denot_sat_of_reach hone hssa hfwd hamo hphiOK huse hgf hexit
    hentryV hhead (denot_hedge hfwd huse hentry)

/-! ## The semantic admission criterion: weak enough

With one concrete model per failing run — `denot P s0` — "the VC is
weak enough" has a direct semantic definition, with no expected set:
every failing denotational run models it. Any over-approximation of
the runs qualifies, and anything weaker than an admissible VC is
trivially admissible. Soundness needs nothing else
(`safe_denot_of_denotSound`). The expected set is thereby demoted to
its proper role: membership is ONE decidable certificate of
`DenotSound` (`denotSound_of_expected`), not part of the soundness
statement. Looser certificates — a per-site weakening table keyed by
the annotation — can be added without touching the theorems below. -/

/-- `vc` is *weak enough* for the denotational semantics. -/
def DenotSound (P : Program) (vc : Vc.VC) : Prop :=
  ∀ s0 : State, (denot P s0).blks P.blocks.length = true →
    Vc.Sat (denot P s0) vc

/-- Soundness from weakness alone: an unsatisfiable, weak-enough VC
makes the last block unreachable. -/
theorem safe_denot_of_denotSound {P : Program} {vc : Vc.VC}
    (h : DenotSound P vc) (hunsat : Vc.Unsat vc) : Safe_denot P := by
  intro s0
  cases hb : (denot P s0).blks P.blocks.length with
  | false => rfl
  | true => exact absurd ⟨denot P s0, h s0 hb⟩ hunsat

/-- The expected-membership certificate: a well-formed program's
expected set is weak enough, hence so is any subset of it. -/
theorem denotSound_of_expected {P : Program} {vc : Vc.VC}
    (hone : singleAssertOK P = true) (hssa : ssaOK P = true)
    (hfwd : forwardOK P = true) (hphiOK : phiOK P = true)
    (hamo : amoSideOK P = true) (hentry : entryOK P = true)
    (hgf : guardFreeOK P = true) (huse : usesOK P = true)
    (hsub : ∀ c ∈ vc.constraints, c ∈ Vc.expected P)
    (hmsub : ∀ md ∈ vc.mapDefs, md ∈ Vc.expectedMapDefs P) :
    DenotSound P vc := by
  intro s0 hexit
  have hsat := denot_sat hone hssa hfwd hphiOK hamo hentry hgf huse hexit
  exact ⟨fun c hc => hsat.1 c (hsub c hc),
    fun md hmd => hsat.2 md (hmsub md hmd)⟩

/-- The denotational `checkVC_safe`: an accepted, unsatisfiable VC makes
the last block unreachable. No dominator table, no witness
construction — `domClosedOK` is checked by `wellFormed` but never used. -/
theorem checkVC_safe_denot {P : Program} {vc : Vc.VC}
    (hchk : checkVC P vc = true) (hunsat : Vc.Unsat vc) : Safe_denot P := by
  rw [checkVC, Bool.and_eq_true, Bool.and_eq_true] at hchk
  obtain ⟨⟨hwf, hmem⟩, hmdefs⟩ := hchk
  rw [wellFormed] at hwf
  simp only [Bool.and_eq_true] at hwf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hone, hssa⟩, hfwd⟩, hphi⟩, hamo⟩, hentry⟩, hgf⟩, -⟩, huse⟩ := hwf
  exact safe_denot_of_denotSound
    (denotSound_of_expected hone hssa hfwd hphi hamo hentry hgf huse
      (fun c hc => of_decide_eq_true (List.all_eq_true.mp hmem c hc))
      (fun md hmd => of_decide_eq_true (List.all_eq_true.mp hmdefs md hmd)))
    hunsat

end Ttac
