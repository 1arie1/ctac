import Ttac.VcVal
import Ttac.VcAdequacy

/-!
# Gamma merges: the sea_gate hybrid encoding's value plane, certified

The hybrid sea_gate encoding keeps the whole control plane of bwd0
(block guards, CFG constraints, gated assumes, objective, map
definitions) and changes exactly one constraint family: a scalar phi's
defining equation. Instead of the guard-selected `phiRhs` (an ITE over
predecessor *block guards*), the encoder emits a **guarded gamma** —

    guard(b)  ⇒  x = ite(K₁, v₁, ite(K₂, v₂, … v_tail))

whose case guards `Kᵢ` are ordinary boolean expressions over *branch
registers* (thin gated-SSA gates), and whose tail is the phi's own
last arm (matching `phiRhs`'s else-tail; a fresh `undef` fallback would
need a model extension, which this development deliberately has none
of).

Admission is by certificate, per site (`GammaCert`):

* each case carries the predecessors it **covers**;
* per real predecessor `p`, a three-valued evaluation (`eval3`) under
  `p`'s valuation-table claims plus the arrival edge's own
  determinations must show the covering case true and every earlier
  case false — and the selected arm must be the arm `phiRhs` selects
  for `p`.

The truth lemma (`denot_gamma`) shows a certified gamma constraint
holds at every denotational fold state: at an inactive block the guard
is false; at an active block the (unique, by `visited_amo`) active
predecessor selects the same arm on both sides. The checker
(`checkVCGAnn`) is `checkVCWAnn` with the certified gamma constraints
added to each block's anchor pool — everything else is admitted by the
same weakening/rewrite tables against the same per-site generators.
-/

namespace Ttac

namespace Vc

/-! ## The certificate -/

/-- One gamma case: its guard expression (over branch registers), the
arm register it selects, and the predecessors it claims to cover. -/
structure GammaCase where
  guard : BExp
  src : Nat
  covers : List Nat
deriving Repr, DecidableEq

/-- The per-site certificate: the gamma's cases, in emission order. The
tail arm is implicit — the phi's own last arm. -/
structure GammaCert where
  cases : List GammaCase
deriving Repr, DecidableEq

/-- The gamma expression: an ITE chain over the case guards with the
tail register as the else-arm, built with the same folding `mkIte` the
encoder's term constructors use. -/
def gammaExp (t : Ty) (tail : Nat) : List GammaCase → Exp t
  | [] => .var t tail
  | c :: rest => mkIte c.guard (.var t c.src) (gammaExp t tail rest)

/-- The arm `phiRhs` selects when `p` is the one active predecessor:
the first arm keyed on `p`, else the fallthrough tail. -/
def armSrcFor (arms : PhiArms) (p tail : Nat) : Nat :=
  match arms with
  | [] => tail
  | a :: rest => if a.1 = p then a.2 else armSrcFor rest p tail

/-- Walk the cases for predecessor `p` with expected selection `es`:
the first covering case must be certified true and select `es`; cases
before it must be certified false; falling through requires the tail
to be the expected arm. -/
def checkCases (cl : List (Nat × Bool)) (p tail es : Nat) :
    List GammaCase → Bool
  | [] => decide (es = tail)
  | c :: rest =>
      if c.covers.contains p then
        decide (c.src = es) && decide (eval3 cl c.guard = .tt)
      else
        decide (eval3 cl c.guard = .ff) && checkCases cl p tail es rest

/-- Per-site gamma admission: for every real predecessor of the join,
the case walk certifies the selection `phiRhs` would make. -/
def checkGamma (P : Program) (T : ValTable) (b : Nat) (arms : PhiArms)
    (g : GammaCert) : Bool :=
  match arms.getLast? with
  | none => false
  | some la =>
      (predsOf P b).all fun p =>
        checkCases (valAt T p ++ edgeClaims P p b) p la.2
          (armSrcFor arms p la.2) g.cases

/-- The constraint a certified gamma site is entitled to emit:
`guard(b) ⇒ x = gammaExp`. `none` at `.map` (no map equality operator;
map merges stay on the classical `mapDefFrom` route). -/
def gammaConstraint? (P : Program) (b : Nat) (t : Ty) (x : Nat)
    (arms : PhiArms) (g : GammaCert) : Option BExp :=
  match arms.getLast? with
  | none => none
  | some la =>
      (eqConstraint? t x (gammaExp t la.2 g.cases)).map
        fun eq => mkImp (guardOf P b) eq

/-- The gamma anchors a block's certificates contribute: only entries
that name a real phi command and pass `checkGamma` yield an anchor —
an invalid certificate contributes nothing (rejection of whatever
constraint needed it, never unsoundness). -/
def gammaAnchors (P : Program) (T : ValTable) (b : Nat) (B : Block)
    (gs : List (Nat × GammaCert)) : List BExp :=
  gs.filterMap fun ig =>
    match B.cmds[ig.1]? with
    | some (Cmd.phi t x arms) =>
        if checkGamma P T b arms ig.2 then
          gammaConstraint? P b t x arms ig.2
        else none
    | _ => none

theorem mem_gammaAnchors {P : Program} {T : ValTable} {b : Nat}
    {B : Block} {gs : List (Nat × GammaCert)} {c : BExp}
    (h : c ∈ gammaAnchors P T b B gs) :
    ∃ (i : Nat) (t : Ty) (x : Nat) (arms : PhiArms) (g : GammaCert),
      B.cmds[i]? = some (Cmd.phi t x arms)
        ∧ checkGamma P T b arms g = true
        ∧ gammaConstraint? P b t x arms g = some c := by
  rw [gammaAnchors, List.mem_filterMap] at h
  obtain ⟨ig, -, heq⟩ := h
  split at heq
  · rename_i t x arms hci
    split at heq
    · rename_i hchk
      exact ⟨ig.1, t, x, arms, ig.2, hci, hchk, heq⟩
    · cases heq
  · cases heq

/-! ## The annotated VC with gamma certificates -/

/-- One block's buckets: as `BlockBucket`, plus the block's gamma
certificates, keyed by command index. Certificates are proof data, not
formula content. -/
structure GBlockBucket where
  cfg : List BExp
  cmds : List (List BExp)
  maps : List (Nat × MExp)
  gammas : List (Nat × GammaCert) := []
deriving Repr, DecidableEq

/-- The whole annotated VC: per-block buckets, the objective, and the
valuation table (certificate data shared by all gamma sites). -/
structure GAnnVC where
  perBlock : List GBlockBucket
  objective : List BExp
  val : ValTable := []
deriving Repr, DecidableEq

def GAnnVC.flatten (a : GAnnVC) : List BExp :=
  (a.perBlock.map fun bk => bk.cfg ++ bk.cmds.flatten).flatten ++ a.objective

def GAnnVC.mapDefs (a : GAnnVC) : List (Nat × MExp) :=
  (a.perBlock.map (·.maps)).flatten

def GAnnVC.Sat (w : State) (a : GAnnVC) : Prop :=
  (∀ c ∈ a.flatten, c.eval w = true)
    ∧ ∀ md ∈ a.mapDefs, w.regs .map md.1 = md.2.eval w

def GAnnVC.Unsat (a : GAnnVC) : Prop := ¬∃ w, a.Sat w

end Vc

/-! ## Selection lemmas -/

/-- The gamma side of selection: a passing case walk under claims that
hold pins the gamma's value to the expected arm register. -/
theorem checkCases_select {σ : State} {cl : List (Nat × Bool)}
    (hcl : ∀ rv ∈ cl, σ.regs .bool rv.1 = rv.2) {t : Ty} {p tail es : Nat} :
    ∀ cs : List Vc.GammaCase, Vc.checkCases cl p tail es cs = true →
      (Vc.gammaExp t tail cs).eval σ = σ.regs t es
  | [], h => by
      simp only [Vc.checkCases, decide_eq_true_eq] at h
      subst h
      rfl
  | c :: rest, h => by
      simp only [Vc.checkCases] at h
      split at h
      · rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
        have hg : c.guard.eval σ = true := eval3_tt hcl h.2
        simp [Vc.gammaExp, Vc.eval_mkIte, hg, Exp.eval, h.1]
      · rw [Bool.and_eq_true, decide_eq_true_eq] at h
        have hg : c.guard.eval σ = false := eval3_ff hcl h.1
        simp only [Vc.gammaExp, Vc.eval_mkIte, hg, Bool.false_eq_true,
          if_false]
        exact checkCases_select hcl rest h.2

/-- The phi side of selection: when every arm guard evaluates by
"is this the active predecessor `p`", the chain selects `armSrcFor`. -/
theorem phiChain_select {P : Program} {σ : State} {t : Ty} {p tail : Nat} :
    ∀ (a : Nat × Nat) (rest : List (Nat × Nat)),
      (∀ qs ∈ a :: rest, (Vc.guardOf P qs.1).eval σ = decide (qs.1 = p)) →
      (a :: rest).getLast?.map (·.2) = some tail →
      (Vc.phiChain P t a rest).eval σ
        = σ.regs t (Vc.armSrcFor (a :: rest) p tail)
  | (q0, s0), [], hg, hlast => by
      obtain rfl : s0 = tail := by simpa using hlast
      by_cases hq : q0 = p <;>
        simp [Vc.phiChain, Vc.armSrcFor, hq, Exp.eval]
  | (q0, s0), a' :: rest', hg, hlast => by
      have hlast' : (a' :: rest').getLast?.map (·.2) = some tail := by
        rwa [List.getLast?_cons_cons] at hlast
      have hg0 : (Vc.guardOf P q0).eval σ = decide (q0 = p) :=
        hg (q0, s0) (List.mem_cons_self ..)
      have hrec := phiChain_select (t := t) a' rest'
        (fun qs hqs => hg qs (List.mem_cons_of_mem _ hqs)) hlast'
      by_cases hq : q0 = p
      · subst hq
        simp [Vc.phiChain, Vc.eval_mkIte, hg0, Vc.armSrcFor, Exp.eval]
      · simp [Vc.phiChain, Vc.eval_mkIte, hg0, hq, Vc.armSrcFor, hrec]

/-! ## The truth lemma -/

/-- A certified gamma constraint holds at every denotational fold
state: inactive block ⇒ guard false; active block ⇒ the unique active
predecessor drives both the gamma (case walk + claim transport) and
`phiRhs` (guard selection + `visited_amo`) to the same arm. -/
theorem denot_gamma {P : Program} {s0 : State} (hwf : WellFormed P)
    {T : ValTable} (hcl : valClosedOK P T = true)
    {b : Nat} {B : Block} {i : Nat} {t : Ty} {x : Nat} {arms : PhiArms}
    {g : Vc.GammaCert} {gc : BExp}
    (hB : P.block? b = some B) (hci : B.cmds[i]? = some (.phi t x arms))
    (hchk : Vc.checkGamma P T b arms g = true)
    (hgc : Vc.gammaConstraint? P b t x arms g = some gc) :
    gc.eval (denot P s0) = true := by
  -- destructure the constraint
  unfold Vc.gammaConstraint? at hgc
  split at hgc
  case _ => cases hgc
  rename_i la hlast
  rw [Option.map_eq_some_iff] at hgc
  obtain ⟨eq, heq, rfl⟩ := hgc
  -- basic shape facts
  have hblt : b < P.blocks.length := (List.getElem?_eq_some_iff.mp hB).1
  have harms : phiArmsOK P b arms = true :=
    phiOK_at hwf.phi hB (List.mem_of_getElem? hci)
  have hbne : b ≠ P.entry := by
    have hla : la ∈ arms := List.mem_of_getLast? hlast
    have := phiArm_lt harms (p := la.1) (src := la.2) hla
    have hent := entry_eq_zero hwf.entry
    omega
  rw [Vc.eval_mkImp]
  cases hact : (denot P s0).blks b with
  | false =>
      -- inactive join: the guard is false, the implication vacuous
      simp [Vc.guardOf, hbne, Exp.eval, hact]
  | true =>
      -- active join: both sides select the active predecessor's arm
      have hbA : b ∈ activeList P s0 := mem_activeList.mpr ⟨hblt, hact⟩
      obtain ⟨hentryA, -⟩ := denot_hentry hwf.fwd hwf.uses hbA
      obtain ⟨p, hpact, hplt, hpE⟩ :=
        denot_active_pred hwf.fwd hwf.uses hB hact hbne
      obtain ⟨cond, hedge, -⟩ := hpE.edge_cond
      have hppred : p ∈ predsOf P b := mem_predsOf.mpr ⟨cond, hedge⟩
      have hpA : p ∈ activeList P s0 :=
        mem_activeList.mpr ⟨by omega, hpact⟩
      -- the case walk at the actual predecessor
      unfold Vc.checkGamma at hchk
      rw [hlast] at hchk
      simp only at hchk
      have hwalk := List.all_eq_true.mp hchk p hppred
      -- its claims hold at the fold state
      have hclaims : ∀ rv ∈ valAt T p ++ edgeClaims P p b,
          (denot P s0).regs .bool rv.1 = rv.2 := by
        intro rv hrv
        rcases List.mem_append.mp hrv with hv | he
        · exact val_visited hwf hcl hpA rv hv
        · exact edgeClaims_sound hpE rv he
      -- gamma side
      have hgamma := checkCases_select (t := t) hclaims g.cases hwalk
      -- phi side
      have hguards : ∀ qs ∈ arms,
          (Vc.guardOf P qs.1).eval (denot P s0) = decide (qs.1 = p) := by
        intro qs hqs
        have hqlt : qs.1 < P.blocks.length := by
          have := phiArm_lt harms (p := qs.1) (src := qs.2) hqs
          omega
        rw [guard_eval hentryA (fun q hq => denot_hblk hq) hqlt]
        by_cases hqp : qs.1 = p
        · simp [hqp, hpA]
        · suffices h : qs.1 ∉ activeList P s0 by simp [h, hqp]
          intro hqA
          have hqpred : qs.1 ∈ predsOf P b :=
            phiArm_pred harms (p := qs.1) (src := qs.2) hqs
          exact hqp (visited_amo hwf.fwd hwf.amo (denot_hedge hwf) hblt
            (two_mem_le_length hqpred hppred hqp) hqA hqpred hpA hppred)
      cases arms with
      | nil => cases hlast
      | cons a rest =>
          have hphi : (Vc.phiRhs P t (a :: rest)).eval (denot P s0)
              = (denot P s0).regs t (Vc.armSrcFor (a :: rest) p la.2) := by
            rw [Vc.phiRhs]
            exact phiChain_select a rest hguards (by simp [hlast])
          have hval : (denot P s0).regs t x
              = (Vc.gammaExp t la.2 g.cases).eval (denot P s0) := by
            rw [denot_phi hwf hB (List.mem_of_getElem? hci), hphi, hgamma]
          rw [eqConstraint_eval heq hval]
          simp

/-! ## The checker -/

/-- The gamma-aware site-tagged checker: `checkVCWAnn` with the block's
certified gamma constraints added to its command-bucket anchor pool,
plus the valuation-table closure. -/
def checkVCGAnn (P : Program) (a : Vc.GAnnVC) : Bool :=
  wellFormed P
    && valClosedOK P a.val
    && decide (a.perBlock.length = P.blocks.length)
    && (a.perBlock.zipIdx.all fun (bk, b) =>
          bk.cfg.all (fun c =>
              (Vc.cfgConstraintsFor P b).any (fun x => Vc.weakensFrom x c))
            && (match P.blocks[b]? with
                | some B => bk.cmds.flatten.all (fun c =>
                    ((B.cmds.map (Vc.cmdConstraints P b)).flatten
                        ++ Vc.gammaAnchors P a.val b B bk.gammas).any
                      (fun x => Vc.weakensFrom x c))
                    && bk.maps.all (fun md =>
                        (B.cmds.filterMap (Vc.cmdMapDef? P)).any
                          (fun x => Vc.mapDefFrom x md))
                | none => false))
    && (match Vc.assertSites P with
        | [(aB, _, okReg)] => a.objective.all (fun c =>
            (Vc.objective P aB okReg).any (fun x => Vc.weakensFrom x c))
        | _ => false)

theorem denotSound_of_checkVCGAnn {P : Program} {a : Vc.GAnnVC}
    (hchk : checkVCGAnn P a = true) :
    DenotSound P { constraints := a.flatten, mapDefs := a.mapDefs } := by
  unfold checkVCGAnn at hchk
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    Bool.and_eq_true] at hchk
  obtain ⟨⟨⟨⟨hwfb, hval⟩, hlen⟩, hall⟩, hobj⟩ := hchk
  rw [decide_eq_true_eq] at hlen
  obtain ⟨hwf, -⟩ := wellFormed_iff.mp hwfb
  intro s0 hexit
  have hsat := denot_sat hwf hexit
  obtain ⟨aB, iA, okReg, BA, heqs, hBA, hcA, -⟩ := singleAssert_shape hwf.one
  refine ⟨fun c hc => ?_, fun md hmd => ?_⟩
  · rw [Vc.GAnnVC.flatten, List.mem_append] at hc
    rcases hc with hc | hc
    · rw [List.mem_flatten] at hc
      obtain ⟨L, hL, hcL⟩ := hc
      rw [List.mem_map] at hL
      obtain ⟨bk, hbk, rfl⟩ := hL
      obtain ⟨b, hb⟩ := List.mem_iff_getElem?.mp hbk
      have hbzip : (bk, b) ∈ a.perBlock.zipIdx :=
        List.mem_zipIdx_iff_getElem?.mpr hb
      have hblt : b < P.blocks.length := by
        have := (List.getElem?_eq_some_iff.mp hb).1
        omega
      obtain ⟨hcfgb, hcmdb⟩ := Bool.and_eq_true .. |>.mp
        (List.all_eq_true.mp hall (bk, b) hbzip)
      rw [List.mem_append] at hcL
      rcases hcL with hcfg | hcmds
      · obtain ⟨x, hxmem, hxw⟩ := List.any_eq_true.mp
          (List.all_eq_true.mp hcfgb c hcfg)
        exact Vc.weakensFrom_sound hxw
          (hsat.1 x (mem_expected_of_cfgFor heqs hblt hxmem))
      · have hBb : P.blocks[b]? = some P.blocks[b] :=
          List.getElem?_eq_getElem hblt
        simp only [hBb, Bool.and_eq_true] at hcmdb
        obtain ⟨x, hxmem, hxw⟩ := List.any_eq_true.mp
          (List.all_eq_true.mp hcmdb.1 c hcmds)
        rcases List.mem_append.mp hxmem with hcls | hgam
        · exact Vc.weakensFrom_sound hxw
            (hsat.1 x (mem_expected_of_cmd heqs hBb hcls))
        · obtain ⟨i, t, y, arms, g, hci, hg, hgc⟩ :=
            Vc.mem_gammaAnchors hgam
          exact Vc.weakensFrom_sound hxw
            (denot_gamma hwf hval hBb hci hg hgc)
    · rw [heqs] at hobj
      obtain ⟨x, hxmem, hxw⟩ := List.any_eq_true.mp
        (List.all_eq_true.mp hobj c hc)
      exact Vc.weakensFrom_sound hxw
        (hsat.1 x (mem_expected_of_objective heqs hxmem))
  · rw [Vc.GAnnVC.mapDefs, List.mem_flatten] at hmd
    obtain ⟨L, hL, hmdL⟩ := hmd
    rw [List.mem_map] at hL
    obtain ⟨bk, hbk, rfl⟩ := hL
    obtain ⟨b, hb⟩ := List.mem_iff_getElem?.mp hbk
    have hbzip : (bk, b) ∈ a.perBlock.zipIdx :=
      List.mem_zipIdx_iff_getElem?.mpr hb
    have hblt : b < P.blocks.length := by
      have := (List.getElem?_eq_some_iff.mp hb).1
      omega
    obtain ⟨-, hcmdb⟩ := Bool.and_eq_true .. |>.mp
      (List.all_eq_true.mp hall (bk, b) hbzip)
    have hBb : P.blocks[b]? = some P.blocks[b] :=
      List.getElem?_eq_getElem hblt
    simp only [hBb, Bool.and_eq_true] at hcmdb
    obtain ⟨x, hxmem, hxw⟩ := List.any_eq_true.mp
      (List.all_eq_true.mp hcmdb.2 md hmdL)
    obtain ⟨c, hcmem, hcd⟩ := List.mem_filterMap.mp hxmem
    exact Vc.mapDefFrom_sound hxw
      (denot_mapDef hwf hBb hcmem hcd)

/-- The gamma checker's denotational safety. -/
theorem checkVCGAnn_safe_denot {P : Program} {a : Vc.GAnnVC}
    (hchk : checkVCGAnn P a = true) (hunsat : a.Unsat) : Safe_denot P :=
  safe_denot_of_denotSound (denotSound_of_checkVCGAnn hchk)
    (fun ⟨w, hs⟩ => hunsat ⟨w, hs⟩)

/-- The headline: an accepted, unsatisfiable gamma-annotated VC makes
the program operationally safe. -/
theorem checkVCGAnn_safe {P : Program} {a : Vc.GAnnVC}
    (hchk : checkVCGAnn P a = true) (hunsat : a.Unsat) : P.Safe := by
  have hwf : wellFormed P = true := by
    rw [checkVCGAnn, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
      Bool.and_eq_true] at hchk
    exact hchk.1.1.1.1
  exact safe_of_safe_denot (adequacy hwf) (checkVCGAnn_safe_denot hchk hunsat)

end Ttac
