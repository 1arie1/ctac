import Ttac.VcVal
import Ttac.VcPdom
import Ttac.VcAdequacy

/-!
# Gamma merges: the sea_gate hybrid encoding's value plane, certified

The hybrid sea_gate encoding keeps the whole control plane of bwd0
(block guards, CFG constraints, gated assumes, objective, map
definitions) and changes exactly one constraint family: a scalar phi's
defining equation. Instead of the guard-selected `phiRhs` (an ITE over
predecessor *block guards*), the encoder emits a gamma whose case
guards are boolean expressions over *branch registers* (thin gated-SSA
gates), in one of two shapes:

* **guarded** — `guard(b) ⇒ x = ite(K₁, v₁, … v_tail)`, tail = the
  phi's last arm. Unreached joins are vacuous; the certificate is the
  covers mapping alone.
* **total** (sea_gate's) — `x = ite(K₁, v₁, … phiRhs)`, an unguarded
  definition whose tail is `phiRhs` itself. Unreached joins additionally
  need *forcing* — no case may fire there — certified per case by
  structure (parent gate ∧ oriented branch) against the
  postdominator-to-assert table (`VcPdom`) and, for parent-free
  controllers, the dominator table.

A fresh `undef` fallback, and a total form with a plain last-arm tail,
are both unprovable against the fold state (an active-but-branched-away
predecessor makes `phiRhs` select its arm at an unreached join); the
`phiRhs` tail makes the dead-case value the fold's own term by
construction.

Admission is by certificate, per site (`GammaCert` / `TGammaCert`):
each case carries the predecessors it **covers**, and per real
predecessor `p` a three-valued evaluation (`eval3`) under `p`'s
valuation-table claims plus the arrival edge's own determinations must
show the covering case true and every earlier case false — selecting
the arm `phiRhs` selects for `p`.

The truth lemmas (`denot_gamma`, `denot_tgamma`) show a certified
gamma constraint holds at every (failing, for the total form)
denotational fold state: at an active join the unique active
predecessor (`visited_amo`) selects the same arm on both sides; at an
inactive join the guarded form is vacuous and the total form's cases
are dead by forcing. The checker (`checkVCGAnn`) is `checkVCWAnn` with
the certified gamma constraints added to each block's anchor pool —
everything else is admitted by the same weakening/rewrite tables
against the same per-site generators.
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

/-! ## Total gammas: gates, forcing side conditions, certificates

The guarded form above needs nothing at unreached joins. The
**total** form `x = ite(K₁, v₁, … phiRhs)` (sea_gate's shape) also
needs the *unreached* direction: no case may fire at an inactive join,
else the definition disagrees with the fold's `phiRhs` value. Each
case guard is therefore *structured* — `parent-gate ∧ orient` — so the
checker can verify per case that firing **forces** the join:
controller reached (by the parent gate, inductively, or by dominating
the assert block) and oriented toward successor `s ≤ aB` implies `s`
is on the failing chain, and the join postdominates `s` toward the
assert block (`pdomOf`). The tail is `phiRhs` itself, so with every
case dead the total definition is the fold's own term. -/

/-- One gate case: the parent gate (a table index; `none` ⇒ the
controller must dominate the assert block), the controller block, and
which successor its branch selects. -/
structure GateRow where
  parent : Option Nat
  ctrl : Nat
  side : Bool
deriving Repr, DecidableEq

/-- A materialized gate: the block whose reachability it expresses and
its cases (one per direct controller). -/
structure Gate where
  block : Nat
  rows : List GateRow
deriving Repr, DecidableEq

abbrev GateTable := List Gate

/-- The oriented branch condition of a controller, and the successor
it selects — `none` when the block does not end in a branch. -/
def termOrientExp (side : Bool) : Terminator → Option BExp
  | .ifGoto creg _ _ =>
      some (if side then .var .bool creg else .un .not (.var .bool creg))
  | _ => none

def termOrientTarget (side : Bool) : Terminator → Option Nat
  | .ifGoto _ tb eb => some (if side then tb else eb)
  | _ => none

def orientExp (P : Program) (c : Nat) (side : Bool) : Option BExp :=
  (P.block? c).bind fun B => termOrientExp side B.term

def orientTarget (P : Program) (c : Nat) (side : Bool) : Option Nat :=
  (P.block? c).bind fun B => termOrientTarget side B.term

mutual

/-- Gate and row expressions, fuel-bounded (any cyclic or dangling
reference exhausts the fuel and yields `none` — rejection, never
unsoundness). `gt.length + 1` fuel suffices for any acyclic table. -/
def gateExpGo (P : Program) (gt : GateTable) : Nat → Nat → Option BExp
  | 0, _ => none
  | fuel + 1, i =>
      match gt[i]? with
      | none => none
      | some g => (rowsExp P gt fuel g.rows).map mkOr
termination_by fuel _ => (fuel, 0)

def rowExp (P : Program) (gt : GateTable) : Nat → GateRow → Option BExp
  | fuel, r =>
      match orientExp P r.ctrl r.side with
      | none => none
      | some oe =>
          match r.parent with
          | none => some oe
          | some pi => (gateExpGo P gt fuel pi).map (mkAnd2 · oe)
termination_by fuel _ => (fuel, 1)

def rowsExp (P : Program) (gt : GateTable) :
    Nat → List GateRow → Option (List BExp)
  | _, [] => some []
  | fuel, r :: rest =>
      match rowExp P gt fuel r, rowsExp P gt fuel rest with
      | some re, some res => some (re :: res)
      | _, _ => none
termination_by fuel rows => (fuel, rows.length + 2)

end

/-- The forcing side conditions of one case with target block `tgt`:
the controller branches, the selected successor sits at or before the
assert block and is postdominated (toward it) by `tgt`, and the parent
gate — if any — is the controller's own gate (`none` requires the
controller to dominate the assert block instead). -/
def rowOK (P : Program) (gt : GateTable) (aB tgt : Nat)
    (r : GateRow) : Bool :=
  match orientTarget P r.ctrl r.side with
  | none => false
  | some s =>
      decide (s ≤ aB)
        && (pdomOf P aB s).contains tgt
        && (match r.parent with
            | none => (domOf P aB).contains r.ctrl
            | some pi =>
                match gt[pi]? with
                | some pg => decide (pg.block = r.ctrl)
                | none => false)

/-- Every gate's rows force that gate's own block. -/
def gateTableOK (P : Program) (gt : GateTable) (aB : Nat) : Bool :=
  gt.all fun g => g.rows.all (rowOK P gt aB g.block)

/-- One total-gamma case: its structured guard, the arm it selects,
and the predecessors it covers. -/
structure TGammaCase where
  row : GateRow
  src : Nat
  covers : List Nat
deriving Repr, DecidableEq

structure TGammaCert where
  cases : List TGammaCase
deriving Repr, DecidableEq

/-- A total-gamma case's guard expression. -/
def tcaseExp (P : Program) (gt : GateTable) (c : TGammaCase) : Option BExp :=
  rowExp P gt (gt.length + 1) c.row

/-- The total gamma: ITE chain over the case guards with `phiRhs`
itself as the else-tail — at a join where every case is dead it *is*
the fold's own term. -/
def gammaExpT? (P : Program) (gt : GateTable) (t : Ty) (arms : PhiArms) :
    List TGammaCase → Option (Exp t)
  | [] => some (phiRhs P t arms)
  | c :: rest =>
      match tcaseExp P gt c, gammaExpT? P gt t arms rest with
      | some ge, some restE => some (mkIte ge (.var t c.src) restE)
      | _, _ => none

/-- The case walk for predecessor `p` with expected selection `es`:
as `checkCases`, but falling through is always admissible — the tail
is `phiRhs`, which selects `es` at `p` by construction. -/
def tcheckCases (P : Program) (gt : GateTable) (cl : List (Nat × Bool))
    (p es : Nat) : List TGammaCase → Bool
  | [] => true
  | c :: rest =>
      match tcaseExp P gt c with
      | none => false
      | some ge =>
          if c.covers.contains p then
            decide (c.src = es) && decide (eval3 cl ge = .tt)
          else
            decide (eval3 cl ge = .ff) && tcheckCases P gt cl p es rest

/-- Per-site total-gamma admission: every case forces the join
(`rowOK`), and per real predecessor the walk certifies the selection. -/
def checkTGamma (P : Program) (gt : GateTable) (T : ValTable) (aB b : Nat)
    (arms : PhiArms) (g : TGammaCert) : Bool :=
  g.cases.all (fun c => rowOK P gt aB b c.row)
    && (match arms.getLast? with
        | none => false
        | some la =>
            (predsOf P b).all fun p =>
              tcheckCases P gt (valAt T p ++ edgeClaims P p b) p
                (armSrcFor arms p la.2) g.cases)

/-- The constraint a certified total-gamma site is entitled to emit:
the bare defining equation `x = gammaExpT`. -/
def tgammaConstraint? (P : Program) (gt : GateTable) (t : Ty) (x : Nat)
    (arms : PhiArms) (g : TGammaCert) : Option BExp :=
  (gammaExpT? P gt t arms g.cases).bind (eqConstraint? t x)

def tgammaAnchors (P : Program) (gt : GateTable) (T : ValTable) (aB b : Nat)
    (B : Block) (gs : List (Nat × TGammaCert)) : List BExp :=
  gs.filterMap fun ig =>
    match B.cmds[ig.1]? with
    | some (Cmd.phi t x arms) =>
        if checkTGamma P gt T aB b arms ig.2 then
          tgammaConstraint? P gt t x arms ig.2
        else none
    | _ => none

theorem mem_tgammaAnchors {P : Program} {gt : GateTable} {T : ValTable}
    {aB b : Nat} {B : Block} {gs : List (Nat × TGammaCert)} {c : BExp}
    (h : c ∈ tgammaAnchors P gt T aB b B gs) :
    ∃ (i : Nat) (t : Ty) (x : Nat) (arms : PhiArms) (g : TGammaCert),
      B.cmds[i]? = some (Cmd.phi t x arms)
        ∧ checkTGamma P gt T aB b arms g = true
        ∧ tgammaConstraint? P gt t x arms g = some c := by
  rw [tgammaAnchors, List.mem_filterMap] at h
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
  tgammas : List (Nat × TGammaCert) := []
deriving Repr, DecidableEq

/-- The whole annotated VC: per-block buckets, the objective, and the
certificate data shared by all gamma sites — the valuation table and
the gate table. -/
structure GAnnVC where
  perBlock : List GBlockBucket
  objective : List BExp
  val : ValTable := []
  gates : GateTable := []
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

/-! ## Forcing: a firing case means its target is active

The unreached direction of the total form. `orient_taken` rebuilds the
taken edge from a true oriented condition; `orient_forces` walks it
onto the failing chain (the chain's unique continuation) and through
the postdominator transport; `row_forces`/`gate_forces` close the
recursion through parent gates by fuel induction, grounding
parent-free rows in dominators of the assert block (`dom_visited` —
the dominator certificate's second consumer). -/

theorem orient_taken {P : Program} {σ : State} {c : Nat} {side : Bool}
    {s : Nat} {oe : BExp}
    (hct : Vc.orientTarget P c side = some s)
    (hoe : Vc.orientExp P c side = some oe)
    (hval : oe.eval σ = true) :
    EdgeTaken P σ c s := by
  unfold Vc.orientTarget at hct
  unfold Vc.orientExp at hoe
  cases hB : P.block? c with
  | none => rw [hB] at hct; cases hct
  | some B =>
      rw [hB] at hct hoe
      simp only [Option.bind] at hct hoe
      cases hterm : B.term with
      | halt => rw [hterm] at hct; simp [Vc.termOrientTarget] at hct
      | goto v => rw [hterm] at hct; simp [Vc.termOrientTarget] at hct
      | ifGoto creg tb eb =>
          rw [hterm] at hct hoe
          cases side with
          | true =>
              simp only [Vc.termOrientTarget, Vc.termOrientExp,
                Option.some.injEq] at hct hoe
              subst hct
              subst hoe
              exact ⟨B, hB, Or.inr ⟨creg, tb, eb, hterm,
                Or.inl ⟨rfl, by simpa [Exp.eval] using hval⟩⟩⟩
          | false =>
              simp only [Vc.termOrientTarget, Vc.termOrientExp,
                Bool.false_eq_true, Option.some.injEq] at hct hoe
              subst hct
              subst hoe
              refine ⟨B, hB, Or.inr ⟨creg, tb, eb, hterm, Or.inr ⟨rfl, ?_⟩⟩⟩
              simpa [Exp.eval, UnOp.denote] using hval

theorem orient_forces {P : Program} {s0 : State} (hwf : WellFormed P)
    {aB : Nat} (hpc : pdomClosedOK P aB = true)
    (haB : aB ∈ activeList P s0)
    {c : Nat} {side : Bool} {s tgt : Nat} {oe : BExp}
    (hct : Vc.orientTarget P c side = some s)
    (hoe : Vc.orientExp P c side = some oe)
    (hsle : s ≤ aB) (hpd : tgt ∈ pdomOf P aB s)
    (hcA : c ∈ activeList P s0)
    (hval : oe.eval (denot P s0) = true) :
    tgt ∈ activeList P s0 := by
  have hE : EdgeTaken P (denot P s0) c s := orient_taken hct hoe hval
  have hcs : c < s := hE.lt hwf.fwd
  have hlt : Chained (· < ·) (activeList P s0) :=
    (denot_hedge hwf).imp fun _ _ h => h.lt hwf.fwd
  have hsA : s ∈ activeList P s0 :=
    chained_succ_mem (denot_hedge hwf) hlt hcA haB (by omega) hE
  exact pdom_active hwf hpc hsA haB hsle tgt hpd

theorem row_forces {P : Program} {s0 : State} (hwf : WellFormed P)
    (hdc : domClosedOK P = true) {aB : Nat}
    (hpc : pdomClosedOK P aB = true) {gt : Vc.GateTable}
    (haB : aB ∈ activeList P s0) {fuel : Nat}
    (hIH : ∀ i e, Vc.gateExpGo P gt fuel i = some e →
      e.eval (denot P s0) = true →
      ∀ g, gt[i]? = some g → g.block ∈ activeList P s0)
    {r : Vc.GateRow} {tgt : Nat} (hrow : Vc.rowOK P gt aB tgt r = true)
    {re : BExp} (hre : Vc.rowExp P gt fuel r = some re)
    (hval : re.eval (denot P s0) = true) :
    tgt ∈ activeList P s0 := by
  unfold Vc.rowOK at hrow
  unfold Vc.rowExp at hre
  split at hrow
  case _ => cases hrow
  rename_i s hct
  rw [Bool.and_eq_true, Bool.and_eq_true] at hrow
  obtain ⟨⟨hsle, hpd⟩, hparent⟩ := hrow
  cases hoe : Vc.orientExp P r.ctrl r.side with
  | none => rw [hoe] at hre; cases hre
  | some oe =>
      rw [hoe] at hre
      simp only at hre
      cases hp : r.parent with
      | none =>
          rw [hp] at hre hparent
          simp only at hre hparent
          obtain rfl := Option.some.inj hre
          have hcA : r.ctrl ∈ activeList P s0 := by
            obtain ⟨hentryA, hhead⟩ := denot_hentry hwf.fwd hwf.uses haB
            exact dom_visited hdc hwf.fwd (denot_hedge hwf) hhead aB haB
              r.ctrl (List.contains_iff_mem.mp hparent)
          exact orient_forces hwf hpc haB hct hoe (of_decide_eq_true hsle)
            (List.contains_iff_mem.mp hpd) hcA hval
      | some pi =>
          rw [hp] at hre hparent
          simp only at hre hparent
          rw [Option.map_eq_some_iff] at hre
          obtain ⟨pe, hpe, rfl⟩ := hre
          rw [Vc.eval_mkAnd2, Bool.and_eq_true] at hval
          cases hpg : gt[pi]? with
          | none => rw [hpg] at hparent; cases hparent
          | some pg =>
              rw [hpg] at hparent
              have hctrlA : r.ctrl ∈ activeList P s0 := by
                have := hIH pi pe hpe hval.1 pg hpg
                rwa [of_decide_eq_true hparent] at this
              exact orient_forces hwf hpc haB hct hoe (of_decide_eq_true hsle)
                (List.contains_iff_mem.mp hpd) hctrlA hval.2

theorem rowsExp_mem {P : Program} {gt : Vc.GateTable} {fuel : Nat} :
    ∀ {rows : List Vc.GateRow} {res : List BExp},
      Vc.rowsExp P gt fuel rows = some res →
      ∀ re ∈ res, ∃ r ∈ rows, Vc.rowExp P gt fuel r = some re := by
  intro rows
  induction rows with
  | nil =>
      intro res h re hre
      simp only [Vc.rowsExp, Option.some.injEq] at h
      rw [← h] at hre
      cases hre
  | cons r rest ih =>
      intro res h re hre
      unfold Vc.rowsExp at h
      split at h
      · rename_i re0 res' hre0 hres'
        obtain rfl := Option.some.inj h
        rcases List.mem_cons.mp hre with rfl | hre'
        · exact ⟨r, List.mem_cons_self .., hre0⟩
        · obtain ⟨r', hr', hre''⟩ := ih hres' re hre'
          exact ⟨r', List.mem_cons_of_mem _ hr', hre''⟩
      · cases h

theorem gate_forces {P : Program} {s0 : State} (hwf : WellFormed P)
    (hdc : domClosedOK P = true) {aB : Nat}
    (hpc : pdomClosedOK P aB = true) {gt : Vc.GateTable}
    (hgt : Vc.gateTableOK P gt aB = true)
    (haB : aB ∈ activeList P s0) :
    ∀ (fuel i : Nat) (e : BExp),
      Vc.gateExpGo P gt fuel i = some e →
      e.eval (denot P s0) = true →
      ∀ g, gt[i]? = some g → g.block ∈ activeList P s0 := by
  intro fuel
  induction fuel with
  | zero => intro i e h; simp [Vc.gateExpGo] at h
  | succ fuel ih =>
      intro i e h hval g hg
      unfold Vc.gateExpGo at h
      rw [hg] at h
      simp only at h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨res, hres, rfl⟩ := h
      rw [Vc.eval_mkOr] at hval
      obtain ⟨re, hrem, hretrue⟩ := List.any_eq_true.mp hval
      obtain ⟨r, hr, hre⟩ := rowsExp_mem hres re hrem
      have hrowok : Vc.rowOK P gt aB g.block r = true :=
        List.all_eq_true.mp
          (List.all_eq_true.mp hgt g (List.mem_of_getElem? hg)) r hr
      exact row_forces hwf hdc hpc haB ih hrowok hre hretrue

/-! ## Total-gamma selection and fallthrough -/

theorem tcheckCases_select {P : Program} {gt : Vc.GateTable} {σ : State}
    {cl : List (Nat × Bool)}
    (hcl : ∀ rv ∈ cl, σ.regs .bool rv.1 = rv.2) {t : Ty} {arms : PhiArms}
    {p es : Nat}
    (hphi : (Vc.phiRhs P t arms).eval σ = σ.regs t es) :
    ∀ cs : List Vc.TGammaCase,
      Vc.tcheckCases P gt cl p es cs = true →
      ∀ E : Exp t, Vc.gammaExpT? P gt t arms cs = some E →
        E.eval σ = σ.regs t es := by
  intro cs
  induction cs with
  | nil =>
      intro _ E hE
      simp only [Vc.gammaExpT?, Option.some.injEq] at hE
      rw [← hE]
      exact hphi
  | cons c rest ih =>
      intro h E hE
      unfold Vc.tcheckCases at h
      unfold Vc.gammaExpT? at hE
      cases hge : Vc.tcaseExp P gt c with
      | none => rw [hge] at h; cases h
      | some ge =>
          rw [hge] at h hE
          simp only at h hE
          cases hrest : Vc.gammaExpT? P gt t arms rest with
          | none => rw [hrest] at hE; cases hE
          | some restE =>
              rw [hrest] at hE
              simp only at hE
              obtain rfl := Option.some.inj hE
              rw [Vc.eval_mkIte]
              split at h
              · rw [Bool.and_eq_true, decide_eq_true_eq,
                  decide_eq_true_eq] at h
                rw [eval3_tt hcl h.2]
                simp [Exp.eval, h.1]
              · rw [Bool.and_eq_true, decide_eq_true_eq] at h
                rw [eval3_ff hcl h.1]
                simp only [Bool.false_eq_true, if_false]
                exact ih h.2 restE hrest

theorem gammaExpT_fallthrough {P : Program} {gt : Vc.GateTable} {σ : State}
    {t : Ty} {arms : PhiArms} :
    ∀ (cs : List Vc.TGammaCase) (E : Exp t),
      Vc.gammaExpT? P gt t arms cs = some E →
      (∀ c ∈ cs, ∀ ge, Vc.tcaseExp P gt c = some ge → ge.eval σ = false) →
      E.eval σ = (Vc.phiRhs P t arms).eval σ := by
  intro cs
  induction cs with
  | nil =>
      intro E hE _
      simp only [Vc.gammaExpT?, Option.some.injEq] at hE
      rw [← hE]
  | cons c rest ih =>
      intro E hE hdead
      unfold Vc.gammaExpT? at hE
      cases hge : Vc.tcaseExp P gt c with
      | none => rw [hge] at hE; cases hE
      | some ge =>
          rw [hge] at hE
          try simp only at hE
          cases hrest : Vc.gammaExpT? P gt t arms rest with
          | none => rw [hrest] at hE; cases hE
          | some restE =>
              rw [hrest] at hE
              try simp only at hE
              obtain rfl := Option.some.inj hE
              rw [Vc.eval_mkIte, hdead c (List.mem_cons_self ..) ge hge]
              simp only [Bool.false_eq_true, if_false]
              exact ih restE hrest
                fun c' hc' => hdead c' (List.mem_cons_of_mem _ hc')

/-! ## The total-gamma truth lemma -/

/-- A certified total-gamma constraint holds at every *failing*
denotational fold state: at an active join the walk selects the active
predecessor's arm on both sides; at an inactive join every case is
dead by forcing (a firing case would put the join on the failing
chain) and the gamma falls through to `phiRhs` — the fold's own term.
Unlike the guarded form, this direction genuinely needs the run to
reach the assert block. -/
theorem denot_tgamma {P : Program} {s0 : State} (hwf : WellFormed P)
    (hdc : domClosedOK P = true) (hexit : ReachesExit P s0)
    {T : ValTable} (hcl : valClosedOK P T = true)
    {aB iA okReg : Nat} (heqs : Vc.assertSites P = [(aB, iA, okReg)])
    (hpc : pdomClosedOK P aB = true) {gt : Vc.GateTable}
    (hgt : Vc.gateTableOK P gt aB = true)
    {b : Nat} {B : Block} {i : Nat} {t : Ty} {x : Nat} {arms : PhiArms}
    {g : Vc.TGammaCert} {gc : BExp}
    (hB : P.block? b = some B) (hci : B.cmds[i]? = some (.phi t x arms))
    (hchk : Vc.checkTGamma P gt T aB b arms g = true)
    (hgc : Vc.tgammaConstraint? P gt t x arms g = some gc) :
    gc.eval (denot P s0) = true := by
  unfold Vc.tgammaConstraint? at hgc
  rw [Option.bind_eq_some_iff] at hgc
  obtain ⟨E, hE, heq⟩ := hgc
  unfold Vc.checkTGamma at hchk
  rw [Bool.and_eq_true] at hchk
  obtain ⟨hforce, hsel⟩ := hchk
  have haBA : aB ∈ activeList P s0 := (denot_fail hexit aB iA okReg heqs).1
  have hblt : b < P.blocks.length := (List.getElem?_eq_some_iff.mp hB).1
  have harms : phiArmsOK P b arms = true :=
    phiOK_at hwf.phi hB (List.mem_of_getElem? hci)
  refine eqConstraint_eval heq ?_
  rw [denot_phi hwf hB (List.mem_of_getElem? hci)]
  cases hact : (denot P s0).blks b with
  | false =>
      refine (gammaExpT_fallthrough g.cases E hE fun c hc ge hge => ?_).symm
      cases hv : ge.eval (denot P s0) with
      | false => rfl
      | true =>
          have hrok : Vc.rowOK P gt aB b c.row = true :=
            List.all_eq_true.mp hforce c hc
          have hbA : b ∈ activeList P s0 :=
            row_forces hwf hdc hpc haBA
              (gate_forces hwf hdc hpc hgt haBA (gt.length + 1)) hrok hge hv
          rw [(mem_activeList.mp hbA).2] at hact
          cases hact
  | true =>
      -- the active case: mirror of the guarded form's selection
      cases hlast : arms.getLast? with
      | none => rw [hlast] at hsel; cases hsel
      | some la =>
          rw [hlast] at hsel
          simp only at hsel
          have hbne : b ≠ P.entry := by
            have hla : la ∈ arms := List.mem_of_getLast? hlast
            have := phiArm_lt harms (p := la.1) (src := la.2) hla
            have hent := entry_eq_zero hwf.entry
            omega
          have hbA : b ∈ activeList P s0 := mem_activeList.mpr ⟨hblt, hact⟩
          obtain ⟨hentryA, -⟩ := denot_hentry hwf.fwd hwf.uses hbA
          obtain ⟨p, hpact, hplt, hpE⟩ :=
            denot_active_pred hwf.fwd hwf.uses hB hact hbne
          obtain ⟨cond, hedge, -⟩ := hpE.edge_cond
          have hppred : p ∈ predsOf P b := mem_predsOf.mpr ⟨cond, hedge⟩
          have hpA : p ∈ activeList P s0 :=
            mem_activeList.mpr ⟨by omega, hpact⟩
          have hwalk := List.all_eq_true.mp hsel p hppred
          have hclaims : ∀ rv ∈ valAt T p ++ edgeClaims P p b,
              (denot P s0).regs .bool rv.1 = rv.2 := by
            intro rv hrv
            rcases List.mem_append.mp hrv with hv | he
            · exact val_visited hwf hcl hpA rv hv
            · exact edgeClaims_sound hpE rv he
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
                  = (denot P s0).regs t
                      (Vc.armSrcFor (a :: rest) p la.2) := by
                rw [Vc.phiRhs]
                exact phiChain_select a rest hguards (by simp [hlast])
              rw [hphi]
              exact (tcheckCases_select hclaims hphi g.cases hwalk E hE).symm

/-! ## The checker -/

/-- The checker body at a known single-assert site. -/
def checkVCGAnnAt (P : Program) (a : Vc.GAnnVC) (aB okReg : Nat) : Bool :=
  wellFormed P
    && valClosedOK P a.val
    && pdomClosedOK P aB
    && Vc.gateTableOK P a.gates aB
    && decide (a.perBlock.length = P.blocks.length)
    && (a.perBlock.zipIdx.all fun (bk, b) =>
          bk.cfg.all (fun c =>
              (Vc.cfgConstraintsFor P b).any (fun x => Vc.weakensFrom x c))
            && (match P.blocks[b]? with
                | some B => bk.cmds.flatten.all (fun c =>
                    ((B.cmds.map (Vc.cmdConstraints P b)).flatten
                        ++ Vc.gammaAnchors P a.val b B bk.gammas
                        ++ Vc.tgammaAnchors P a.gates a.val aB b B
                            bk.tgammas).any
                      (fun x => Vc.weakensFrom x c))
                    && bk.maps.all (fun md =>
                        (B.cmds.filterMap (Vc.cmdMapDef? P)).any
                          (fun x => Vc.mapDefFrom x md))
                | none => false))
    && a.objective.all (fun c =>
        (Vc.objective P aB okReg).any (fun x => Vc.weakensFrom x c))

/-- The gamma-aware site-tagged checker: `checkVCWAnn` with each
block's certified gamma constraints — guarded and total — added to its
command-bucket anchor pool, plus the certificate closures (valuation
table, postdominators toward the assert block, gate table). -/
def checkVCGAnn (P : Program) (a : Vc.GAnnVC) : Bool :=
  match Vc.assertSites P with
  | [(aB, _, okReg)] => checkVCGAnnAt P a aB okReg
  | _ => false

theorem checkVCGAnn_shape {P : Program} {a : Vc.GAnnVC}
    (h : checkVCGAnn P a = true) :
    ∃ aB iA okReg, Vc.assertSites P = [(aB, iA, okReg)]
      ∧ checkVCGAnnAt P a aB okReg = true := by
  unfold checkVCGAnn at h
  split at h
  · rename_i aB iA okReg heqs
    exact ⟨aB, iA, okReg, heqs, h⟩
  · cases h

theorem denotSound_of_checkVCGAnn {P : Program} {a : Vc.GAnnVC}
    (hchk : checkVCGAnn P a = true) :
    DenotSound P { constraints := a.flatten, mapDefs := a.mapDefs } := by
  obtain ⟨aB, iA, okReg, heqs, hchk⟩ := checkVCGAnn_shape hchk
  unfold checkVCGAnnAt at hchk
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hchk
  obtain ⟨⟨⟨⟨⟨⟨hwfb, hval⟩, hpc⟩, hgt⟩, hlen⟩, hall⟩, hobj⟩ := hchk
  rw [decide_eq_true_eq] at hlen
  obtain ⟨hwf, hdc⟩ := wellFormed_iff.mp hwfb
  intro s0 hexit
  have hsat := denot_sat hwf hexit
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
        rcases List.mem_append.mp hxmem with hx1 | htg
        · rcases List.mem_append.mp hx1 with hcls | hgam
          · exact Vc.weakensFrom_sound hxw
              (hsat.1 x (mem_expected_of_cmd heqs hBb hcls))
          · obtain ⟨i, t, y, arms, g, hci, hg, hgc⟩ :=
              Vc.mem_gammaAnchors hgam
            exact Vc.weakensFrom_sound hxw
              (denot_gamma hwf hval hBb hci hg hgc)
        · obtain ⟨i, t, y, arms, g, hci, hg, hgc⟩ :=
            Vc.mem_tgammaAnchors htg
          exact Vc.weakensFrom_sound hxw
            (denot_tgamma hwf hdc hexit hval heqs hpc hgt hBb hci hg hgc)
    · obtain ⟨x, hxmem, hxw⟩ := List.any_eq_true.mp
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
    obtain ⟨aB, iA, okReg, -, hchk'⟩ := checkVCGAnn_shape hchk
    unfold checkVCGAnnAt at hchk'
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
      Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hchk'
    exact hchk'.1.1.1.1.1.1
  exact safe_of_safe_denot (adequacy hwf) (checkVCGAnn_safe_denot hchk hunsat)

end Ttac
