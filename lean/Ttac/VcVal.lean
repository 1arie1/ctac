import Ttac.VcDenot

/-!
# The valuation-table certificate: branch-register values "up the CFG"

An untrusted annotator claims, per block `b`, values of boolean
registers that hold *whenever a run visits `b`* — e.g. "any run
visiting `left` has `c = true`". The checker validates the table by a
local per-edge closure (`valClosedOK`): a claim at `b` must, on every
in-edge `q → b`, either be *determined by the edge* (the predecessor
branches on that register toward `b`'s side) or already be claimed at
`q`. The proof transports the claims along the failing run's taken-edge
chain (`val_chain`), the same shape as the dominator-certificate
consumption: a wrong table either fails the closure (rejection) or is
sound anyway.

The consumer is the gamma checker (`VcGamma`): a gamma case's guard is
an ordinary boolean expression over branch registers, and `eval3` — a
three-valued evaluator under a claim list — certifies its value at a
given predecessor. `eval3` abstains (`.uk`) on anything it cannot
justify (unclaimed registers, guard atoms, arithmetic comparisons);
abstention is completeness loss, never unsoundness (`eval3_models`).
-/

namespace Ttac

/-! ## The table and its closure -/

/-- Per-block claims `(bool register, value)`: row `b` lists facts that
hold at the final state of every run that visits block `b`. -/
abbrev ValTable := List (List (Nat × Bool))

def valAt (T : ValTable) (b : Nat) : List (Nat × Bool) :=
  (T[b]?).getD []

/-- The claims a terminator determines on its edge into `b`: a branch
on `c` with `b` on exactly one side pins `c`. -/
def termClaims (b : Nat) : Terminator → List (Nat × Bool)
  | .ifGoto c t e =>
      if b = t ∧ b ≠ e then [(c, true)]
      else if b = e ∧ b ≠ t then [(c, false)]
      else []
  | _ => []

/-- The claims the edge `p → b` itself determines. -/
def edgeClaims (P : Program) (p b : Nat) : List (Nat × Bool) :=
  match P.block? p with
  | some B => termClaims b B.term
  | none => []

/-- The closure check: entry claims nothing (nothing justifies a claim
there), and every claim at a non-entry block is justified on every
in-edge — determined by the edge, or already claimed at the source. -/
def valClosedOK (P : Program) (T : ValTable) : Bool :=
  (valAt T P.entry).isEmpty
    && (List.range P.blocks.length).all fun b =>
        decide (b = P.entry)
          || (valAt T b).all fun rv =>
              (predsOf P b).all fun q =>
                decide (rv ∈ edgeClaims P q b) || decide (rv ∈ valAt T q)

/-! ## Soundness of edge determination -/

theorem edgeClaims_sound {P : Program} {σ : State} {q b : Nat}
    (hE : EdgeTaken P σ q b) :
    ∀ rv ∈ edgeClaims P q b, σ.regs .bool rv.1 = rv.2 := by
  intro rv hrv
  obtain ⟨B, hB, hshape⟩ := hE
  unfold edgeClaims at hrv
  rw [hB] at hrv
  simp only at hrv
  rcases hshape with hgoto | ⟨c, t, e, hif, harm⟩
  · rw [hgoto] at hrv; simp [termClaims] at hrv
  · rw [hif] at hrv
    simp only [termClaims] at hrv
    by_cases h1 : b = t ∧ b ≠ e
    · rw [if_pos h1] at hrv
      obtain rfl := List.mem_singleton.mp hrv
      rcases harm with ⟨ht, hc⟩ | ⟨he, hc⟩
      · exact hc
      · exact absurd he.symm h1.2
    · rw [if_neg h1] at hrv
      by_cases h2 : b = e ∧ b ≠ t
      · rw [if_pos h2] at hrv
        obtain rfl := List.mem_singleton.mp hrv
        rcases harm with ⟨ht, hc⟩ | ⟨he, hc⟩
        · exact absurd ht.symm h2.2
        · exact hc
      · rw [if_neg h2] at hrv
        cases hrv

/-! ## Transport along the taken-edge chain -/

/-- Claims propagate along a taken-edge chain whose head's claims hold:
each step is justified by the edge itself or by the previous block's
claims. -/
theorem val_chain_go {P : Program} {σ : State} {T : ValTable}
    (hcl : valClosedOK P T = true) :
    ∀ {V : List Nat}, Chained (EdgeTaken P σ) V →
      (∀ b ∈ V, b < P.blocks.length) →
      (∀ x, V.head? = some x → ∀ rv ∈ valAt T x, σ.regs .bool rv.1 = rv.2) →
      ∀ b ∈ V, ∀ rv ∈ valAt T b, σ.regs .bool rv.1 = rv.2 := by
  intro V
  induction V with
  | nil => intro _ _ _ b hb; cases hb
  | cons x rest ih =>
      intro hch hlen hhead b hb
      rcases List.mem_cons.mp hb with rfl | hb'
      · exact hhead b rfl
      · cases rest with
        | nil => cases hb'
        | cons y rest' =>
            obtain ⟨hExy, hch'⟩ := chained_destruct hch
            refine ih hch' (fun q hq => hlen q (List.mem_cons_of_mem _ hq))
              (fun z hz rv hrv => ?_) b hb'
            rw [List.head?_cons] at hz
            obtain rfl : y = z := Option.some.inj hz
            -- justify y's claims from the edge x → y and x's claims
            rw [valClosedOK, Bool.and_eq_true] at hcl
            have hylt : y < P.blocks.length :=
              hlen y (List.mem_cons_of_mem _ (List.mem_cons_self ..))
            have hrow := List.all_eq_true.mp hcl.2 y (List.mem_range.mpr hylt)
            rw [Bool.or_eq_true, decide_eq_true_eq] at hrow
            rcases hrow with rfl | hrow
            · -- y is the entry: its claim list is empty
              rw [List.isEmpty_iff.mp hcl.1] at hrv
              cases hrv
            · obtain ⟨cond, hedge, -⟩ := hExy.edge_cond
              have hxpred : x ∈ predsOf P y := mem_predsOf.mpr ⟨cond, hedge⟩
              have hj := List.all_eq_true.mp
                (List.all_eq_true.mp hrow rv hrv) x hxpred
              rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hj
              rcases hj with hdet | hclaim
              · exact edgeClaims_sound hExy rv hdet
              · exact hhead x rfl rv hclaim

/-- Claims of every active block hold at the final denotational state. -/
theorem val_visited {P : Program} {s0 : State} {T : ValTable}
    (hwf : WellFormed P) (hcl : valClosedOK P T = true)
    {b : Nat} (hb : b ∈ activeList P s0) :
    ∀ rv ∈ valAt T b, (denot P s0).regs .bool rv.1 = rv.2 := by
  obtain ⟨hentry, hhead⟩ := denot_hentry hwf.fwd hwf.uses hb
  refine val_chain_go hcl (denot_hedge hwf)
    (fun q hq => (mem_activeList.mp hq).1) (fun x hx rv hrv => ?_) b hb
  obtain rfl : x = P.entry := (Option.some.inj (hhead.symm.trans hx)).symm
  rw [valClosedOK, Bool.and_eq_true] at hcl
  rw [List.isEmpty_iff.mp hcl.1] at hrv
  cases hrv

/-! ## The three-valued evaluator -/

inductive Val3 where
  | tt
  | ff
  | uk
deriving Repr, DecidableEq

namespace Val3

def notV : Val3 → Val3
  | .tt => .ff
  | .ff => .tt
  | .uk => .uk

def andV : Val3 → Val3 → Val3
  | .ff, _ => .ff
  | .tt, b => b
  | .uk, .ff => .ff
  | .uk, _ => .uk

def orV : Val3 → Val3 → Val3
  | .tt, _ => .tt
  | .ff, b => b
  | .uk, .tt => .tt
  | .uk, _ => .uk

def eqV : Val3 → Val3 → Val3
  | .tt, .tt => .tt
  | .ff, .ff => .tt
  | .tt, .ff => .ff
  | .ff, .tt => .ff
  | _, _ => .uk

def iteV : Val3 → Val3 → Val3 → Val3
  | .tt, a, _ => a
  | .ff, _, b => b
  | .uk, _, _ => .uk

/-- The approximation contract: a definite three-valued result names
the boolean; `.uk` claims nothing. -/
def models : Val3 → Bool → Prop
  | .tt, b => b = true
  | .ff, b => b = false
  | .uk, _ => True

theorem notV_models {v : Val3} {b : Bool} (h : v.models b) :
    v.notV.models (!b) := by
  cases v <;> simp_all [models, notV]

theorem andV_models {v₁ v₂ : Val3} {b₁ b₂ : Bool}
    (h₁ : v₁.models b₁) (h₂ : v₂.models b₂) :
    (v₁.andV v₂).models (b₁ && b₂) := by
  cases v₁ <;> cases v₂ <;> simp_all [models, andV]

theorem orV_models {v₁ v₂ : Val3} {b₁ b₂ : Bool}
    (h₁ : v₁.models b₁) (h₂ : v₂.models b₂) :
    (v₁.orV v₂).models (b₁ || b₂) := by
  cases v₁ <;> cases v₂ <;> simp_all [models, orV]

theorem eqV_models {v₁ v₂ : Val3} {b₁ b₂ : Bool}
    (h₁ : v₁.models b₁) (h₂ : v₂.models b₂) :
    (v₁.eqV v₂).models (b₁ == b₂) := by
  cases v₁ <;> cases v₂ <;> simp_all [models, eqV]

theorem iteV_models {vc vt ve : Val3} {bc bt be : Bool}
    (hc : vc.models bc) (ht : vt.models bt) (he : ve.models be) :
    (vc.iteV vt ve).models (if bc then bt else be) := by
  cases vc <;> simp_all [models, iteV]

end Val3

/-- Register lookup in a claim list. Contradictory claims cannot both
hold at any state, so first-match is sound. -/
def claimVal (cl : List (Nat × Bool)) (x : Nat) : Val3 :=
  if (x, true) ∈ cl then .tt
  else if (x, false) ∈ cl then .ff
  else .uk

/-- Three-valued evaluation of a boolean expression under a claim list:
boolean structure is followed, claimed registers are read, and
everything else (guard atoms, arithmetic comparisons) abstains. -/
def eval3 (cl : List (Nat × Bool)) : BExp → Val3
  | .litB b => if b then .tt else .ff
  | .var _ x => claimVal cl x
  | .blk _ => .uk
  | .un .not e => (eval3 cl e).notV
  | .bin .le _ _ => .uk
  | .bin .lt _ _ => .uk
  | .bin .eqI _ _ => .uk
  | .bin .eqB l r => (eval3 cl l).eqV (eval3 cl r)
  | .bin .and l r => (eval3 cl l).andV (eval3 cl r)
  | .bin .or l r => (eval3 cl l).orV (eval3 cl r)
  | .bin .imp l r => (eval3 cl l).notV.orV (eval3 cl r)
  | .ite c th el => (eval3 cl c).iteV (eval3 cl th) (eval3 cl el)

/-- Soundness: under claims that hold at `σ`, a definite `eval3` result
is the expression's value at `σ`. -/
theorem eval3_models {σ : State} {cl : List (Nat × Bool)}
    (hcl : ∀ rv ∈ cl, σ.regs .bool rv.1 = rv.2) :
    ∀ e : BExp, (eval3 cl e).models (e.eval σ)
  | .litB b => by cases b <;> simp [eval3, Exp.eval, Val3.models]
  | .var _ x => by
      simp only [eval3, claimVal]
      split
      · rename_i h
        simpa [Exp.eval, Val3.models] using hcl (x, true) h
      · split
        · rename_i h
          simpa [Exp.eval, Val3.models] using hcl (x, false) h
        · trivial
  | .blk _ => by simp [eval3, Val3.models]
  | .un .not e => by
      simpa [eval3, Exp.eval, UnOp.denote] using
        Val3.notV_models (eval3_models hcl e)
  | .bin .le _ _ => by simp [eval3, Val3.models]
  | .bin .lt _ _ => by simp [eval3, Val3.models]
  | .bin .eqI _ _ => by simp [eval3, Val3.models]
  | .bin .eqB l r => by
      simpa [eval3, Exp.eval, BinOp.denote] using
        Val3.eqV_models (eval3_models hcl l) (eval3_models hcl r)
  | .bin .and l r => by
      simpa [eval3, Exp.eval, BinOp.denote] using
        Val3.andV_models (eval3_models hcl l) (eval3_models hcl r)
  | .bin .or l r => by
      simpa [eval3, Exp.eval, BinOp.denote] using
        Val3.orV_models (eval3_models hcl l) (eval3_models hcl r)
  | .bin .imp l r => by
      simpa [eval3, Exp.eval, BinOp.denote] using
        Val3.orV_models (Val3.notV_models (eval3_models hcl l))
          (eval3_models hcl r)
  | .ite c th el => by
      simpa [eval3, Exp.eval] using
        Val3.iteV_models (eval3_models hcl c) (eval3_models hcl th)
          (eval3_models hcl el)

/-- The definite-true corollary the gamma checker consumes. -/
theorem eval3_tt {σ : State} {cl : List (Nat × Bool)} {e : BExp}
    (hcl : ∀ rv ∈ cl, σ.regs .bool rv.1 = rv.2)
    (h : eval3 cl e = .tt) : e.eval σ = true := by
  have := eval3_models hcl e
  rw [h] at this
  exact this

/-- The definite-false corollary. -/
theorem eval3_ff {σ : State} {cl : List (Nat × Bool)} {e : BExp}
    (hcl : ∀ rv ∈ cl, σ.regs .bool rv.1 = rv.2)
    (h : eval3 cl e = .ff) : e.eval σ = false := by
  have := eval3_models hcl e
  rw [h] at this
  exact this

end Ttac
