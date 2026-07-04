import Mathlib.Data.List.Chain
import Ttac.VcLemmas
import Ttac.VcCheck
import Ttac.Safety

/-!
# Execution-trace structure

The Prop layer over the Bool well-formedness checks, the register
stability lemma (SSA registers keep their value to the final state),
and the `Suffix` abstraction: a failing execution reduced to
final-state facts per visited block.
-/

namespace Ttac

/-! ## Definition sites, Prop layer -/

/-- Register `x` (under def-selector `f`) is defined at `(b, i)`. -/
def IsDefAt (P : Program) (f : Cmd → Option Nat) (x b i : Nat) : Prop :=
  ∃ B c, P.block? b = some B ∧ B.cmds[i]? = some c ∧ f c = some x

theorem mem_defPositions {P : Program} {f : Cmd → Option Nat} {x d j : Nat} :
    ((d, j) : Pos) ∈ defPositions P f x ↔ IsDefAt P f x d j := by
  simp only [defPositions, List.mem_flatten, List.mem_map, IsDefAt]
  constructor
  · rintro ⟨L, ⟨⟨B, b⟩, hmem, rfl⟩, hin⟩
    rw [List.mem_filterMap] at hin
    obtain ⟨⟨c, i⟩, hci, hif⟩ := hin
    by_cases hfc : f c = some x
    · rw [if_pos hfc] at hif
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp (Option.some.inj hif)
      exact ⟨B, c, List.mem_zipIdx_iff_getElem?.mp hmem,
        List.mem_zipIdx_iff_getElem?.mp hci, hfc⟩
    · rw [if_neg hfc] at hif; cases hif
  · rintro ⟨B, c, hB, hc, hfc⟩
    refine ⟨_, ⟨⟨B, d⟩, List.mem_zipIdx_iff_getElem?.mpr hB, rfl⟩, ?_⟩
    rw [List.mem_filterMap]
    exact ⟨(c, j), List.mem_zipIdx_iff_getElem?.mpr hc, by rw [if_pos hfc]⟩

/-- Every definition of `x` sits strictly before position `p`. -/
def DefsBefore (P : Program) (f : Cmd → Option Nat) (x : Nat) (p : Pos) : Prop :=
  ∀ d j, IsDefAt P f x d j → posLt (d, j) p = true

/-! ## Position order -/

theorem posLt_succ {q : Pos} {b i : Nat} (h : posLt q (b, i) = true) :
    posLt q (b, i + 1) = true := by
  simp only [posLt, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at *
  omega

theorem posLt_next_block {q : Pos} {b i b' : Nat} (hb : b < b')
    (h : posLt q (b, i) = true) : posLt q (b', 0) = true := by
  simp only [posLt, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at *
  omega

theorem posLt_irrefl (p : Pos) : posLt p p = false := by
  simp [posLt]

theorem defsBefore_succ {P f x b i} (h : DefsBefore P f x (b, i)) :
    DefsBefore P f x (b, i + 1) :=
  fun d j hd => posLt_succ (h d j hd)

theorem defsBefore_next_block {P f x b i b'} (hb : b < b')
    (h : DefsBefore P f x (b, i)) : DefsBefore P f x (b', 0) :=
  fun d j hd => posLt_next_block hb (h d j hd)

/-! ## Bridges from the Bool well-formedness checks -/

theorem forward_target {P : Program} (hfwd : forwardOK P = true) {b : Nat}
    {B : Block} (hB : P.block? b = some B) {t : Nat}
    (ht : t ∈ termTargets B.term) : b < t ∧ t < P.blocks.length := by
  have h1 := List.all_eq_true.mp hfwd (B, b) (List.mem_zipIdx_iff_getElem?.mpr hB)
  have h2 := List.all_eq_true.mp h1 t ht
  simpa using h2

theorem ssaOK_at {P : Program} (hssa : ssaOK P = true) {b B i c}
    (hB : P.block? b = some B) (hc : B.cmds[i]? = some c) :
    cmdSsaOK P b i c = true :=
  List.all_eq_true.mp
    (List.all_eq_true.mp hssa (B, b) (List.mem_zipIdx_iff_getElem?.mpr hB))
    (c, i) (List.mem_zipIdx_iff_getElem?.mpr hc)

theorem ssa_unique_int {P : Program} (hssa : ssaOK P = true) {x b i}
    (h1 : IsDefAt P cmdIntDef x b i) {d j} (h2 : IsDefAt P cmdIntDef x d j) :
    d = b ∧ j = i := by
  obtain ⟨B, c, hB, hc, hfc⟩ := h1
  have hsite := ssaOK_at hssa hB hc
  rw [cmdSsaOK, Bool.and_eq_true] at hsite
  rw [hfc] at hsite
  have := List.all_eq_true.mp hsite.1 (d, j)
    (by rw [intDefPositions]; exact mem_defPositions.mpr h2)
  have := of_decide_eq_true this
  exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩

theorem ssa_unique_bool {P : Program} (hssa : ssaOK P = true) {x b i}
    (h1 : IsDefAt P cmdBoolDef x b i) {d j} (h2 : IsDefAt P cmdBoolDef x d j) :
    d = b ∧ j = i := by
  obtain ⟨B, c, hB, hc, hfc⟩ := h1
  have hsite := ssaOK_at hssa hB hc
  rw [cmdSsaOK, Bool.and_eq_true] at hsite
  rw [hfc] at hsite
  have := List.all_eq_true.mp hsite.2 (d, j)
    (by rw [boolDefPositions]; exact mem_defPositions.mpr h2)
  have := of_decide_eq_true this
  exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩

/-- A def at `(b, i)` plus all-defs-before `(b, i)` is absurd. -/
theorem defsBefore_no_def_here {P f x b i} (hdef : IsDefAt P f x b i)
    (h : DefsBefore P f x (b, i)) : False := by
  have := h b i hdef
  rw [posLt_irrefl] at this
  cases this

theorem useOK_before {P : Program} {f : Cmd → Option Nat} {r b i : Nat}
    (h : useOK (domTable P) (defPositions P f r) b i = true) :
    DefsBefore P f r (b, i) := by
  intro d j hd
  have := List.all_eq_true.mp h (d, j) (mem_defPositions.mpr hd)
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this
  simp only [posLt, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  omega

theorem intUsesOK_before {P : Program} {b i : Nat} {rs : List Nat}
    (h : intUsesOK P (domTable P) b i rs = true) :
    ∀ r ∈ rs, DefsBefore P cmdIntDef r (b, i) :=
  fun r hr => useOK_before (List.all_eq_true.mp h r hr)

theorem boolUsesOK_before {P : Program} {b i : Nat} {rs : List Nat}
    (h : boolUsesOK P (domTable P) b i rs = true) :
    ∀ r ∈ rs, DefsBefore P cmdBoolDef r (b, i) :=
  fun r hr => useOK_before (List.all_eq_true.mp h r hr)

theorem usesOK_cmd {P : Program} (huse : usesOK P = true) {b B i c}
    (hB : P.block? b = some B) (hc : B.cmds[i]? = some c) :
    cmdUsesOK P (domTable P) b i c = true := by
  have := List.all_eq_true.mp huse (B, b) (List.mem_zipIdx_iff_getElem?.mpr hB)
  rw [Bool.and_eq_true] at this
  exact List.all_eq_true.mp this.1 (c, i) (List.mem_zipIdx_iff_getElem?.mpr hc)

theorem usesOK_term {P : Program} (huse : usesOK P = true) {b B}
    (hB : P.block? b = some B) :
    termUsesOK P (domTable P) b B = true := by
  have := List.all_eq_true.mp huse (B, b) (List.mem_zipIdx_iff_getElem?.mpr hB)
  rw [Bool.and_eq_true] at this
  exact this.2

/-! ## Terminal configurations -/

theorem no_step_done {P : Program} {s : State} {c : Config}
    (h : Step P (.done s) c) : False := nomatch h

theorem no_step_failed {P : Program} {s : State} {c : Config}
    (h : Step P (.failed s) c) : False := nomatch h

theorem steps_failed_eq {P : Program} {s σ : State}
    (h : Steps P (.failed s) (.failed σ)) : s = σ := by
  rcases h.cases_head with heq | ⟨c, hstep, _⟩
  · exact Config.failed.inj heq
  · exact absurd hstep no_step_failed

theorem steps_done_not_failed {P : Program} {s σ : State}
    (h : Steps P (.done s) (.failed σ)) : False := by
  rcases h.cases_head with heq | ⟨c, hstep, _⟩
  · cases heq
  · exact no_step_done hstep

/-! ## Stability

Once a register's every definition lies strictly before the current
position, its value survives to the final state - the execution can
only move forward (forward edges), and SSA means nobody writes it
again. -/

theorem stable_int {P : Program} (hfwd : forwardOK P = true) {σ : State}
    {c : Config} (h : Steps P c (.failed σ)) :
    ∀ {b pc prev s x}, c = .running b pc prev s →
      DefsBefore P cmdIntDef x (b, pc) → σ.ints x = s.ints x := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => intro b pc prev s x heq; cases heq
  | head hstep hrest ih =>
      intro b pc prev s x heq hdefs
      subst heq
      cases hstep with
      | @assignI _ _ _ _ B y e hB hc =>
          have hyx : y ≠ x := fun hyx =>
            defsBefore_no_def_here ⟨B, _, hB, hc, by simp [cmdIntDef, hyx]⟩ hdefs
          rw [ih rfl (defsBefore_succ hdefs)]
          exact State.updI_ints_of_ne s (Ne.symm hyx) _
      | @assignB _ _ _ _ B d e hB hc =>
          rw [ih rfl (defsBefore_succ hdefs), State.updB_ints]
      | @havocI _ _ _ _ B y v hB hc =>
          have hyx : y ≠ x := fun hyx =>
            defsBefore_no_def_here ⟨B, _, hB, hc, by simp [cmdIntDef, hyx]⟩ hdefs
          rw [ih rfl (defsBefore_succ hdefs)]
          exact State.updI_ints_of_ne s (Ne.symm hyx) _
      | @havocB _ _ _ _ B d v hB hc =>
          rw [ih rfl (defsBefore_succ hdefs), State.updB_ints]
      | @phiI _ _ _ _ B y arms src hB hc harm =>
          have hyx : y ≠ x := fun hyx =>
            defsBefore_no_def_here ⟨B, _, hB, hc, by simp [cmdIntDef, hyx]⟩ hdefs
          rw [ih rfl (defsBefore_succ hdefs)]
          exact State.updI_ints_of_ne s (Ne.symm hyx) _
      | @phiB _ _ _ _ B d arms src hB hc harm =>
          rw [ih rfl (defsBefore_succ hdefs), State.updB_ints]
      | assume hB hc hcond =>
          exact ih rfl (defsBefore_succ hdefs)
      | assertTrue hB hc hcond =>
          exact ih rfl (defsBefore_succ hdefs)
      | assertFalse hB hc hcond =>
          rw [steps_failed_eq hrest]
      | halt hB hterm =>
          exact absurd hrest steps_done_not_failed
      | @goto _ _ _ B b' hB hterm =>
          have hlt : b < b' :=
            (forward_target hfwd hB (by rw [hterm]; exact List.mem_singleton.mpr rfl)).1
          exact ih rfl (defsBefore_next_block hlt hdefs)
      | @ifTrue _ _ _ B d t e hB hterm hcond =>
          have hlt : b < t :=
            (forward_target hfwd hB (by rw [hterm]; simp [termTargets])).1
          exact ih rfl (defsBefore_next_block hlt hdefs)
      | @ifFalse _ _ _ B d t e hB hterm hcond =>
          have hlt : b < e :=
            (forward_target hfwd hB (by rw [hterm]; simp [termTargets])).1
          exact ih rfl (defsBefore_next_block hlt hdefs)

theorem stable_bool {P : Program} (hfwd : forwardOK P = true) {σ : State}
    {c : Config} (h : Steps P c (.failed σ)) :
    ∀ {b pc prev s x}, c = .running b pc prev s →
      DefsBefore P cmdBoolDef x (b, pc) → σ.bools x = s.bools x := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => intro b pc prev s x heq; cases heq
  | head hstep hrest ih =>
      intro b pc prev s x heq hdefs
      subst heq
      cases hstep with
      | @assignI _ _ _ _ B y e hB hc =>
          rw [ih rfl (defsBefore_succ hdefs), State.updI_bools]
      | @assignB _ _ _ _ B d e hB hc =>
          have hdx : d ≠ x := fun hdx =>
            defsBefore_no_def_here ⟨B, _, hB, hc, by simp [cmdBoolDef, hdx]⟩ hdefs
          rw [ih rfl (defsBefore_succ hdefs)]
          exact State.updB_bools_of_ne s (Ne.symm hdx) _
      | @havocI _ _ _ _ B y v hB hc =>
          rw [ih rfl (defsBefore_succ hdefs), State.updI_bools]
      | @havocB _ _ _ _ B d v hB hc =>
          have hdx : d ≠ x := fun hdx =>
            defsBefore_no_def_here ⟨B, _, hB, hc, by simp [cmdBoolDef, hdx]⟩ hdefs
          rw [ih rfl (defsBefore_succ hdefs)]
          exact State.updB_bools_of_ne s (Ne.symm hdx) _
      | @phiI _ _ _ _ B y arms src hB hc harm =>
          rw [ih rfl (defsBefore_succ hdefs), State.updI_bools]
      | @phiB _ _ _ _ B d arms src hB hc harm =>
          have hdx : d ≠ x := fun hdx =>
            defsBefore_no_def_here ⟨B, _, hB, hc, by simp [cmdBoolDef, hdx]⟩ hdefs
          rw [ih rfl (defsBefore_succ hdefs)]
          exact State.updB_bools_of_ne s (Ne.symm hdx) _
      | assume hB hc hcond =>
          exact ih rfl (defsBefore_succ hdefs)
      | assertTrue hB hc hcond =>
          exact ih rfl (defsBefore_succ hdefs)
      | assertFalse hB hc hcond =>
          rw [steps_failed_eq hrest]
      | halt hB hterm =>
          exact absurd hrest steps_done_not_failed
      | @goto _ _ _ B b' hB hterm =>
          have hlt : b < b' :=
            (forward_target hfwd hB (by rw [hterm]; exact List.mem_singleton.mpr rfl)).1
          exact ih rfl (defsBefore_next_block hlt hdefs)
      | @ifTrue _ _ _ B d t e hB hterm hcond =>
          have hlt : b < t :=
            (forward_target hfwd hB (by rw [hterm]; simp [termTargets])).1
          exact ih rfl (defsBefore_next_block hlt hdefs)
      | @ifFalse _ _ _ B d t e hB hterm hcond =>
          have hlt : b < e :=
            (forward_target hfwd hB (by rw [hterm]; simp [termTargets])).1
          exact ih rfl (defsBefore_next_block hlt hdefs)

/-- Expressions over stably-defined variables evaluate equally in the
final and current states. -/
theorem stable_evalI {P : Program} (hfwd : forwardOK P = true) {σ : State}
    {b pc prev s} (h : Steps P (.running b pc prev s) (.failed σ)) {e : IExp}
    (hi : ∀ r ∈ e.intVars, DefsBefore P cmdIntDef r (b, pc))
    (hb : ∀ r ∈ e.boolVars, DefsBefore P cmdBoolDef r (b, pc)) :
    evalI σ e = evalI s e :=
  evalI_congr e (fun r hr => stable_int hfwd h rfl (hi r hr))
    (fun r hr => stable_bool hfwd h rfl (hb r hr))

theorem stable_evalB {P : Program} (hfwd : forwardOK P = true) {σ : State}
    {b pc prev s} (h : Steps P (.running b pc prev s) (.failed σ)) {e : BExp}
    (hi : ∀ r ∈ e.intVars, DefsBefore P cmdIntDef r (b, pc))
    (hb : ∀ r ∈ e.boolVars, DefsBefore P cmdBoolDef r (b, pc)) :
    evalB σ e = evalB s e :=
  evalB_congr e (fun r hr => stable_int hfwd h rfl (hi r hr))
    (fun r hr => stable_bool hfwd h rfl (hb r hr))

/-! ## More bridges: phis, asserts, lookups -/

theorem lookup_mem {l : List (Nat × Nat)} {k v : Nat}
    (h : l.lookup k = some v) : (k, v) ∈ l := by
  induction l with
  | nil => simp [List.lookup] at h
  | cons x xs ih =>
      obtain ⟨a, b⟩ := x
      rw [List.lookup] at h
      split at h
      · rename_i heq
        have hk : k = a := by simpa using heq
        have hv : v = b := (Option.some.inj h).symm
        subst hk; subst hv
        exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih h)

theorem phiOK_at {P : Program} (hphi : phiOK P = true) {b B}
    (hB : P.block? b = some B) {c : Cmd} (hc : c ∈ B.cmds) :
    (∀ x arms, c = .phiI x arms → phiArmsOK P b arms = true)
      ∧ (∀ x arms, c = .phiB x arms → phiArmsOK P b arms = true) := by
  have h1 := List.all_eq_true.mp hphi (B, b) (List.mem_zipIdx_iff_getElem?.mpr hB)
  have h2 := List.all_eq_true.mp h1 c hc
  constructor
  · rintro x arms rfl; exact h2
  · rintro x arms rfl; exact h2

theorem phiArm_lt {P : Program} {b : Nat} {arms : PhiArms}
    (h : phiArmsOK P b arms = true) {p src : Nat} (hp : (p, src) ∈ arms) :
    p < b := by
  simp only [phiArmsOK, Bool.and_eq_true] at h
  have := List.all_eq_true.mp h.2 (p, src) hp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact this.1

theorem armUseOK_le {P : Program} {f : Cmd → Option Nat} {src p : Nat}
    (h : armUseOK (domTable P) (defPositions P f src) p = true) :
    ∀ d j, IsDefAt P f src d j → d ≤ p := by
  intro d j hd
  have := List.all_eq_true.mp h (d, j) (mem_defPositions.mpr hd)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact this.1

theorem mem_assertSites {P : Program} {b i c : Nat} :
    ((b, i, c) : Nat × Nat × Nat) ∈ Vc.assertSites P ↔
      ∃ B : Block, P.block? b = some B ∧ B.cmds[i]? = some (.assert c) := by
  simp only [Vc.assertSites, List.mem_flatten, List.mem_map]
  constructor
  · rintro ⟨L, ⟨⟨B, b'⟩, hmem, rfl⟩, hin⟩
    rw [List.mem_filterMap] at hin
    obtain ⟨⟨cmd, i'⟩, hci, hmatch⟩ := hin
    cases cmd <;> simp at hmatch
    case assert r =>
      obtain ⟨rfl, rfl, rfl⟩ := hmatch
      refine ⟨B, ?_, ?_⟩
      · simpa [Program.block?] using List.mem_zipIdx_iff_getElem?.mp hmem
      · simpa using List.mem_zipIdx_iff_getElem?.mp hci
  · rintro ⟨B, hB, hc⟩
    refine ⟨_, ⟨⟨B, b⟩, List.mem_zipIdx_iff_getElem?.mpr hB, rfl⟩, ?_⟩
    rw [List.mem_filterMap]
    exact ⟨(.assert c, i), List.mem_zipIdx_iff_getElem?.mpr hc, rfl⟩

theorem singleAssert_shape {P : Program} (hone : singleAssertOK P = true) :
    ∃ (b i c : Nat) (B : Block), Vc.assertSites P = [(b, i, c)]
      ∧ P.block? b = some B ∧ B.cmds[i]? = some (.assert c)
      ∧ i + 1 = B.cmds.length := by
  rw [singleAssertOK, Bool.and_eq_true] at hone
  obtain ⟨hlen, hall⟩ := hone
  have hlen' : (Vc.assertSites P).length = 1 := by simpa using hlen
  obtain ⟨⟨b, i, c⟩, heq⟩ : ∃ a, Vc.assertSites P = [a] := by
    cases hsig : Vc.assertSites P with
    | nil => rw [hsig] at hlen'; simp at hlen'
    | cons a rest =>
        cases rest with
        | nil => exact ⟨a, rfl⟩
        | cons d rest' => rw [hsig] at hlen'; simp at hlen'
  have hmem : ((b, i, c) : Nat × Nat × Nat) ∈ Vc.assertSites P := by
    rw [heq]; exact List.mem_singleton.mpr rfl
  obtain ⟨B, hB, hc⟩ := mem_assertSites.mp hmem
  refine ⟨b, i, c, B, heq, hB, hc, ?_⟩
  have hsite := List.all_eq_true.mp hall _ hmem
  simp only at hsite
  rw [show P.blocks[b]? = some B from hB] at hsite
  simpa using hsite

theorem singleAssert_unique {P : Program} (hone : singleAssertOK P = true)
    {b i c : Nat} {B : Block} (hB : P.block? b = some B)
    (hc : B.cmds[i]? = some (.assert c))
    {b' i' c' : Nat} {B' : Block} (hB' : P.block? b' = some B')
    (hc' : B'.cmds[i']? = some (.assert c')) :
    b = b' ∧ i = i' ∧ c = c' := by
  obtain ⟨b0, i0, c0, B0, heq, -⟩ := singleAssert_shape hone
  have h1 := mem_assertSites.mpr ⟨B, hB, hc⟩
  have h2 := mem_assertSites.mpr ⟨B', hB', hc'⟩
  rw [heq, List.mem_singleton] at h1 h2
  have h3 := h1.trans h2.symm
  simpa only [Prod.mk.injEq] using h3

/-! ## The Suffix abstraction -/

/-- A failing execution suffix, abstracted to final-state facts:
starting inside block `b` at command index `pc`, entered from `prev`,
execution reaches the failing assert, visiting the blocks `V` (which
starts with `b`). Note there is no constructor for a *passing* assert
or for `halt` - both are impossible on a failing suffix (proved in
`suffix_of_steps`). -/
inductive Suffix (P : Program) (σ : State) :
    Nat → Nat → Option Nat → List Nat → Prop where
  | fail {b pc prev B c} :
      P.block? b = some B → B.cmds[pc]? = some (.assert c) →
      σ.bools c = false →
      Suffix P σ b pc prev [b]
  | assignI {b pc prev V B x e} :
      P.block? b = some B → B.cmds[pc]? = some (.assignI x e) →
      σ.ints x = evalI σ e →
      Suffix P σ b (pc + 1) prev V → Suffix P σ b pc prev V
  | assignB {b pc prev V B c e} :
      P.block? b = some B → B.cmds[pc]? = some (.assignB c e) →
      σ.bools c = evalB σ e →
      Suffix P σ b (pc + 1) prev V → Suffix P σ b pc prev V
  | havocI {b pc prev V B x} :
      P.block? b = some B → B.cmds[pc]? = some (.havocI x) →
      Suffix P σ b (pc + 1) prev V → Suffix P σ b pc prev V
  | havocB {b pc prev V B c} :
      P.block? b = some B → B.cmds[pc]? = some (.havocB c) →
      Suffix P σ b (pc + 1) prev V → Suffix P σ b pc prev V
  | phiI {b pc p V B x arms src} :
      P.block? b = some B → B.cmds[pc]? = some (.phiI x arms) →
      lookupArm arms p = some src → σ.ints x = σ.ints src →
      Suffix P σ b (pc + 1) (some p) V → Suffix P σ b pc (some p) V
  | phiB {b pc p V B c arms src} :
      P.block? b = some B → B.cmds[pc]? = some (.phiB c arms) →
      lookupArm arms p = some src → σ.bools c = σ.bools src →
      Suffix P σ b (pc + 1) (some p) V → Suffix P σ b pc (some p) V
  | assume {b pc prev V B e} :
      P.block? b = some B → B.cmds[pc]? = some (.assume e) →
      evalB σ e = true →
      Suffix P σ b (pc + 1) prev V → Suffix P σ b pc prev V
  | goto {b prev V B b'} :
      P.block? b = some B → B.term = .goto b' →
      Suffix P σ b' 0 (some b) V →
      Suffix P σ b B.cmds.length prev (b :: V)
  | ifTrue {b prev V B c t e} :
      P.block? b = some B → B.term = .ifGoto c t e → σ.bools c = true →
      Suffix P σ t 0 (some b) V →
      Suffix P σ b B.cmds.length prev (b :: V)
  | ifFalse {b prev V B c t e} :
      P.block? b = some B → B.term = .ifGoto c t e → σ.bools c = false →
      Suffix P σ e 0 (some b) V →
      Suffix P σ b B.cmds.length prev (b :: V)

/-- Every failing suffix contains a failing assert. -/
theorem Suffix.fail_fact {P : Program} {σ : State} {b pc prev V}
    (h : Suffix P σ b pc prev V) :
    ∃ (bf i cf : Nat) (Bf : Block), P.block? bf = some Bf
      ∧ Bf.cmds[i]? = some (.assert cf) ∧ σ.bools cf = false := by
  induction h with
  | fail hB hc hfalse => exact ⟨_, _, _, _, hB, hc, hfalse⟩
  | assignI _ _ _ _ ih => exact ih
  | assignB _ _ _ _ ih => exact ih
  | havocI _ _ _ ih => exact ih
  | havocB _ _ _ ih => exact ih
  | phiI _ _ _ _ _ ih => exact ih
  | phiB _ _ _ _ _ ih => exact ih
  | assume _ _ _ _ ih => exact ih
  | goto _ _ _ ih => exact ih
  | ifTrue _ _ _ _ ih => exact ih
  | ifFalse _ _ _ _ ih => exact ih

/-! ## The master abstraction theorem -/

theorem suffix_of_steps {P : Program} (hfwd : forwardOK P = true)
    (hssa : ssaOK P = true) (huse : usesOK P = true)
    (hphi : phiOK P = true) (hone : singleAssertOK P = true) {σ : State}
    {c : Config} (h : Steps P c (.failed σ)) :
    ∀ {b pc prev s}, c = .running b pc prev s → ∃ V, Suffix P σ b pc prev V := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => intro b pc prev s heq; cases heq
  | head hstep hrest ih =>
      intro b pc prev s heq; subst heq
      cases hstep with
      | @assignI _ _ _ _ B y e hB hc =>
          obtain ⟨V, hS⟩ := ih rfl
          have hu := usesOK_cmd huse hB hc
          simp only [cmdUsesOK, Bool.and_eq_true] at hu
          have hIvars := intUsesOK_before hu.1
          have hBvars := boolUsesOK_before hu.2
          have hydef : IsDefAt P cmdIntDef y b pc :=
            ⟨B, _, hB, hc, by simp [cmdIntDef]⟩
          have hσy : σ.ints y = evalI s e := by
            have hy1 : DefsBefore P cmdIntDef y (b, pc + 1) := by
              intro d j hd
              obtain ⟨rfl, rfl⟩ := ssa_unique_int hssa hydef hd
              simp [posLt]
            rw [stable_int hfwd hrest rfl hy1]
            exact State.updI_ints_self ..
          have hne : ∀ r ∈ e.intVars, r ≠ y := fun r hr hry =>
            defsBefore_no_def_here (hry ▸ hydef) (hIvars r hr)
          have heval : evalI σ e = evalI s e := by
            have h1 := stable_evalI hfwd hrest
              (fun r hr => defsBefore_succ (hIvars r hr))
              (fun r hr => defsBefore_succ (hBvars r hr))
            rw [h1]
            exact evalI_congr e
              (fun r hr => State.updI_ints_of_ne s (hne r hr) _)
              (fun r _ => by rw [State.updI_bools])
          exact ⟨V, .assignI hB hc (hσy.trans heval.symm) hS⟩
      | @assignB _ _ _ _ B y e hB hc =>
          obtain ⟨V, hS⟩ := ih rfl
          have hu := usesOK_cmd huse hB hc
          simp only [cmdUsesOK, Bool.and_eq_true] at hu
          have hIvars := intUsesOK_before hu.1
          have hBvars := boolUsesOK_before hu.2
          have hydef : IsDefAt P cmdBoolDef y b pc :=
            ⟨B, _, hB, hc, by simp [cmdBoolDef]⟩
          have hσy : σ.bools y = evalB s e := by
            have hy1 : DefsBefore P cmdBoolDef y (b, pc + 1) := by
              intro d j hd
              obtain ⟨rfl, rfl⟩ := ssa_unique_bool hssa hydef hd
              simp [posLt]
            rw [stable_bool hfwd hrest rfl hy1]
            exact State.updB_bools_self ..
          have hne : ∀ r ∈ e.boolVars, r ≠ y := fun r hr hry =>
            defsBefore_no_def_here (hry ▸ hydef) (hBvars r hr)
          have heval : evalB σ e = evalB s e := by
            have h1 := stable_evalB hfwd hrest
              (fun r hr => defsBefore_succ (hIvars r hr))
              (fun r hr => defsBefore_succ (hBvars r hr))
            rw [h1]
            exact evalB_congr e
              (fun r _ => by rw [State.updB_ints])
              (fun r hr => State.updB_bools_of_ne s (hne r hr) _)
          exact ⟨V, .assignB hB hc (hσy.trans heval.symm) hS⟩
      | havocI v hB hc =>
          obtain ⟨V, hS⟩ := ih rfl
          exact ⟨V, .havocI hB hc hS⟩
      | havocB v hB hc =>
          obtain ⟨V, hS⟩ := ih rfl
          exact ⟨V, .havocB hB hc hS⟩
      | @phiI _ _ _ _ B y arms src hB hc harm =>
          obtain ⟨V, hS⟩ := ih rfl
          have hu := usesOK_cmd huse hB hc
          simp only [cmdUsesOK] at hu
          have harmOK := List.all_eq_true.mp hu (_, src) (lookup_mem harm)
          have hple : ∀ d j, IsDefAt P cmdIntDef src d j → d ≤ _ :=
            armUseOK_le harmOK
          have hplt := phiArm_lt
            ((phiOK_at hphi hB (List.mem_of_getElem? hc)).1 y arms rfl)
            (lookup_mem harm)
          have hydef : IsDefAt P cmdIntDef y b pc :=
            ⟨B, _, hB, hc, by simp [cmdIntDef]⟩
          have hsrc_before : DefsBefore P cmdIntDef src (b, pc + 1) := by
            intro d j hd
            have := hple d j hd
            simp only [posLt, Bool.or_eq_true, Bool.and_eq_true,
              decide_eq_true_eq]
            omega
          have hsrcy : src ≠ y := fun hsy =>
            defsBefore_no_def_here (hsy ▸ hydef) (by
              intro d j hd
              have := hple d j hd
              simp only [posLt, Bool.or_eq_true, Bool.and_eq_true,
                decide_eq_true_eq]
              omega)
          have hσy : σ.ints y = σ.ints src := by
            have hy1 : DefsBefore P cmdIntDef y (b, pc + 1) := by
              intro d j hd
              obtain ⟨rfl, rfl⟩ := ssa_unique_int hssa hydef hd
              simp [posLt]
            rw [stable_int hfwd hrest rfl hy1,
                stable_int hfwd hrest rfl hsrc_before]
            rw [State.updI_ints_self, State.updI_ints_of_ne s hsrcy]
          exact ⟨V, .phiI hB hc harm hσy hS⟩
      | @phiB _ _ _ _ B y arms src hB hc harm =>
          obtain ⟨V, hS⟩ := ih rfl
          have hu := usesOK_cmd huse hB hc
          simp only [cmdUsesOK] at hu
          have harmOK := List.all_eq_true.mp hu (_, src) (lookup_mem harm)
          have hple : ∀ d j, IsDefAt P cmdBoolDef src d j → d ≤ _ :=
            armUseOK_le harmOK
          have hplt := phiArm_lt
            ((phiOK_at hphi hB (List.mem_of_getElem? hc)).2 y arms rfl)
            (lookup_mem harm)
          have hydef : IsDefAt P cmdBoolDef y b pc :=
            ⟨B, _, hB, hc, by simp [cmdBoolDef]⟩
          have hsrc_before : DefsBefore P cmdBoolDef src (b, pc + 1) := by
            intro d j hd
            have := hple d j hd
            simp only [posLt, Bool.or_eq_true, Bool.and_eq_true,
              decide_eq_true_eq]
            omega
          have hsrcy : src ≠ y := fun hsy =>
            defsBefore_no_def_here (hsy ▸ hydef) (by
              intro d j hd
              have := hple d j hd
              simp only [posLt, Bool.or_eq_true, Bool.and_eq_true,
                decide_eq_true_eq]
              omega)
          have hσy : σ.bools y = σ.bools src := by
            have hy1 : DefsBefore P cmdBoolDef y (b, pc + 1) := by
              intro d j hd
              obtain ⟨rfl, rfl⟩ := ssa_unique_bool hssa hydef hd
              simp [posLt]
            rw [stable_bool hfwd hrest rfl hy1,
                stable_bool hfwd hrest rfl hsrc_before]
            rw [State.updB_bools_self, State.updB_bools_of_ne s hsrcy]
          exact ⟨V, .phiB hB hc harm hσy hS⟩
      | @assume _ _ _ _ B e hB hc hcond =>
          obtain ⟨V, hS⟩ := ih rfl
          have hu := usesOK_cmd huse hB hc
          simp only [cmdUsesOK, Bool.and_eq_true] at hu
          have hfact : evalB σ e = true := by
            rw [stable_evalB hfwd hrest
              (fun r hr => defsBefore_succ (intUsesOK_before hu.1 r hr))
              (fun r hr => defsBefore_succ (boolUsesOK_before hu.2 r hr))]
            exact hcond
          exact ⟨V, .assume hB hc hfact hS⟩
      | @assertTrue _ _ _ _ B creg hB hc hcond =>
          obtain ⟨V, hS⟩ := ih rfl
          obtain ⟨bf, if_, cf, Bf, hBf, hcf, hfalse⟩ := hS.fail_fact
          obtain ⟨-, -, hccf⟩ := singleAssert_unique hone hBf hcf hB hc
          have hu := usesOK_cmd huse hB hc
          simp only [cmdUsesOK] at hu
          have := boolUsesOK_before hu creg (List.mem_singleton.mpr rfl)
          have hstable := stable_bool hfwd hrest rfl (defsBefore_succ this)
          rw [hccf, hstable, hcond] at hfalse
          cases hfalse
      | assertFalse hB hc hcond =>
          exact ⟨[b], .fail hB hc (steps_failed_eq hrest ▸ hcond)⟩
      | halt hB hterm =>
          exact absurd hrest steps_done_not_failed
      | @goto _ _ _ B b' hB hterm =>
          obtain ⟨V, hS⟩ := ih rfl
          exact ⟨b :: V, .goto hB hterm hS⟩
      | @ifTrue _ _ _ B creg t e hB hterm hcond =>
          obtain ⟨V, hS⟩ := ih rfl
          have hu := usesOK_term huse hB
          simp only [termUsesOK, hterm] at hu
          have hd := boolUsesOK_before hu creg (List.mem_singleton.mpr rfl)
          have hlt : b < t :=
            (forward_target hfwd hB (by rw [hterm]; simp [termTargets])).1
          have hfact : σ.bools creg = true := by
            rw [stable_bool hfwd hrest rfl (defsBefore_next_block hlt hd)]
            exact hcond
          exact ⟨b :: V, .ifTrue hB hterm hfact hS⟩
      | @ifFalse _ _ _ B creg t e hB hterm hcond =>
          obtain ⟨V, hS⟩ := ih rfl
          have hu := usesOK_term huse hB
          simp only [termUsesOK, hterm] at hu
          have hd := boolUsesOK_before hu creg (List.mem_singleton.mpr rfl)
          have hlt : b < e :=
            (forward_target hfwd hB (by rw [hterm]; simp [termTargets])).1
          have hfact : σ.bools creg = false := by
            rw [stable_bool hfwd hrest rfl (defsBefore_next_block hlt hd)]
            exact hcond
          exact ⟨b :: V, .ifFalse hB hterm hfact hS⟩

/-! ## Consequences of a Suffix derivation -/

/-- Consecutive-pairs predicate over the visited list (self-contained
substitute for mathlib's chain predicates). -/
def Chained (R : Nat → Nat → Prop) : List Nat → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => R a b ∧ Chained R (b :: rest)

/-- The edge the execution took between consecutive visited blocks,
with the branch condition's final value. -/
def EdgeTaken (P : Program) (σ : State) (u v : Nat) : Prop :=
  ∃ B : Block, P.block? u = some B ∧
    (B.term = .goto v ∨
      ∃ c t e, B.term = .ifGoto c t e ∧
        ((t = v ∧ σ.bools c = true) ∨ (e = v ∧ σ.bools c = false)))

theorem Suffix.head {P : Program} {σ : State} {b pc prev V}
    (h : Suffix P σ b pc prev V) : V.head? = some b := by
  induction h <;> simp_all

theorem chained_cons {R : Nat → Nat → Prop} {a : Nat} {V : List Nat}
    (hhead : ∀ v, V.head? = some v → R a v) (hch : Chained R V) :
    Chained R (a :: V) := by
  cases V with
  | nil => trivial
  | cons v V' => exact ⟨hhead v rfl, hch⟩

theorem Chained.imp {R S : Nat → Nat → Prop} (h : ∀ a b, R a b → S a b) :
    ∀ {V : List Nat}, Chained R V → Chained S V
  | [], _ => trivial
  | [_], _ => trivial
  | _ :: _ :: _, ⟨hR, hch⟩ => ⟨h _ _ hR, Chained.imp h hch⟩

theorem Suffix.chain_edge {P : Program} {σ : State} {b pc prev V}
    (h : Suffix P σ b pc prev V) : Chained (EdgeTaken P σ) V := by
  induction h with
  | fail hB hc hfalse => trivial
  | assignI _ _ _ _ ih => exact ih
  | assignB _ _ _ _ ih => exact ih
  | havocI _ _ _ ih => exact ih
  | havocB _ _ _ ih => exact ih
  | phiI _ _ _ _ _ ih => exact ih
  | phiB _ _ _ _ _ ih => exact ih
  | assume _ _ _ _ ih => exact ih
  | goto hB hterm hS ih =>
      refine chained_cons (fun v hv => ?_) ih
      obtain rfl := Option.some.inj (hS.head.symm.trans hv)
      exact ⟨_, hB, Or.inl hterm⟩
  | ifTrue hB hterm hcond hS ih =>
      refine chained_cons (fun v hv => ?_) ih
      obtain rfl := Option.some.inj (hS.head.symm.trans hv)
      exact ⟨_, hB, Or.inr ⟨_, _, _, hterm, Or.inl ⟨rfl, hcond⟩⟩⟩
  | ifFalse hB hterm hcond hS ih =>
      refine chained_cons (fun v hv => ?_) ih
      obtain rfl := Option.some.inj (hS.head.symm.trans hv)
      exact ⟨_, hB, Or.inr ⟨_, _, _, hterm, Or.inr ⟨rfl, hcond⟩⟩⟩

/-! ## Edge and predecessor bridges -/

theorem outEdges_shape {q : Nat} {B : Block} {a s : Nat} {c : BExp}
    (h : (a, s, c) ∈ Vc.outEdges q B) : a = q ∧ s ∈ termTargets B.term := by
  unfold Vc.outEdges at h
  split at h <;> (simp_all [termTargets]; try tauto)

theorem mem_allEdges_intro {P : Program} {u : Nat} {B : Block}
    (hB : P.block? u = some B) {s : Nat} {c : BExp}
    (h : (u, s, c) ∈ Vc.outEdges u B) : (u, s, c) ∈ Vc.allEdges P := by
  simp only [Vc.allEdges, List.mem_flatten, List.mem_map]
  exact ⟨_, ⟨(B, u), List.mem_zipIdx_iff_getElem?.mpr hB, rfl⟩, h⟩

theorem mem_allEdges_elim {P : Program} {p s : Nat} {c : BExp}
    (h : (p, s, c) ∈ Vc.allEdges P) :
    ∃ B : Block, P.block? p = some B ∧ (p, s, c) ∈ Vc.outEdges p B := by
  simp only [Vc.allEdges, List.mem_flatten, List.mem_map] at h
  obtain ⟨L, ⟨⟨B, q⟩, hmem, rfl⟩, hin⟩ := h
  obtain ⟨rfl, -⟩ := outEdges_shape hin
  exact ⟨B, List.mem_zipIdx_iff_getElem?.mp hmem, hin⟩

theorem mem_edgesTo {P : Program} {S p : Nat} {cond : BExp} :
    (p, cond) ∈ Vc.edgesTo P S ↔ (p, S, cond) ∈ Vc.allEdges P := by
  simp only [Vc.edgesTo, List.mem_filterMap]
  constructor
  · rintro ⟨⟨a, s, c⟩, hmem, hif⟩
    by_cases hs : s = S
    · subst hs
      rw [if_pos rfl] at hif
      simp only [Option.some.injEq, Prod.mk.injEq] at hif
      obtain ⟨rfl, rfl⟩ := hif
      exact hmem
    · rw [if_neg hs] at hif; cases hif
  · intro h
    exact ⟨(p, S, cond), h, by rw [if_pos rfl]⟩

theorem mem_predsOf {P : Program} {S p : Nat} :
    p ∈ predsOf P S ↔ ∃ cond, (p, cond) ∈ Vc.edgesTo P S := by
  simp only [predsOf, List.mem_eraseDups, List.mem_map]
  constructor
  · rintro ⟨⟨a, c⟩, hm, rfl⟩; exact ⟨c, hm⟩
  · rintro ⟨c, hm⟩; exact ⟨(p, c), hm, rfl⟩

theorem pred_lt {P : Program} (hfwd : forwardOK P = true) {S p : Nat}
    (hp : p ∈ predsOf P S) : p < S := by
  obtain ⟨cond, hedge⟩ := mem_predsOf.mp hp
  obtain ⟨B, hB, hout⟩ := mem_allEdges_elim (mem_edgesTo.mp hedge)
  exact (forward_target hfwd hB (outEdges_shape hout).2).1

theorem EdgeTaken.edge_cond {P : Program} {σ : State} {u v : Nat}
    (h : EdgeTaken P σ u v) :
    ∃ cond, (u, cond) ∈ Vc.edgesTo P v ∧ evalB σ cond = true := by
  obtain ⟨B, hB, hshape⟩ := h
  rcases hshape with hgoto | ⟨c, t, e, hif, harm⟩
  · refine ⟨.lit true, mem_edgesTo.mpr (mem_allEdges_intro hB ?_), rfl⟩
    simp [Vc.outEdges, hgoto]
  · rcases harm with ⟨rfl, hc⟩ | ⟨rfl, hc⟩
    · refine ⟨.var c, mem_edgesTo.mpr (mem_allEdges_intro hB ?_), by
        simp [evalB, hc]⟩
      simp [Vc.outEdges, hif]
    · refine ⟨.not (.var c), mem_edgesTo.mpr (mem_allEdges_intro hB ?_), by
        simp [evalB, hc]⟩
      simp [Vc.outEdges, hif]

theorem EdgeTaken.lt {P : Program} {σ : State} {u v : Nat}
    (hfwd : forwardOK P = true) (h : EdgeTaken P σ u v) : u < v := by
  obtain ⟨cond, hedge, -⟩ := h.edge_cond
  exact pred_lt hfwd (mem_predsOf.mpr ⟨cond, hedge⟩)

theorem EdgeTaken.mem_succs {P : Program} {σ : State} {u v : Nat}
    (h : EdgeTaken P σ u v) : v ∈ succsOf P u := by
  obtain ⟨B, hB, hshape⟩ := h
  unfold succsOf
  rw [show P.blocks[u]? = some B from hB, List.mem_eraseDups]
  rcases hshape with hgoto | ⟨c, t, e, hif, harm⟩
  · simp [termTargets, hgoto]
  · rcases harm with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp [termTargets, hif]

/-! ## Ordering along the visited chain -/

/-- Definitional destructor for `Chained` on a two-element prefix. -/
theorem chained_destruct {R : Nat → Nat → Prop} {x y : Nat} {rest : List Nat}
    (h : Chained R (x :: y :: rest)) : R x y ∧ Chained R (y :: rest) := h

theorem chained_lt_bound {V : List Nat} (hch : Chained (· < ·) V) {a : Nat}
    (h : V.head? = some a) : ∀ q ∈ V, a ≤ q := by
  induction V generalizing a with
  | nil => cases h
  | cons x rest ih =>
      obtain rfl : x = a := Option.some.inj h
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq'
      · exact Nat.le_refl _
      · cases rest with
        | nil => cases hq'
        | cons y rest' =>
            obtain ⟨hxy, hch'⟩ := chained_destruct hch
            exact Nat.le_of_lt (Nat.lt_of_lt_of_le hxy (ih hch' rfl q hq'))

theorem chained_lt_tail {V : List Nat} (hch : Chained (· < ·) V) {a : Nat}
    (h : V.head? = some a) : ∀ v ∈ V.tail, a < v := by
  cases V with
  | nil => cases h
  | cons x rest =>
      obtain rfl : x = a := Option.some.inj h
      intro v hv
      cases rest with
      | nil => cases hv
      | cons y rest' =>
          obtain ⟨hxy, hch'⟩ := chained_destruct hch
          exact Nat.lt_of_lt_of_le hxy (chained_lt_bound hch' rfl v hv)

/-- Either `p` is the maximum of the chain, or the chain continues from
`p` by a taken edge to `n`, and every chain element is on one side. -/
theorem chained_next {P : Program} {σ : State} {V : List Nat}
    (hedge : Chained (EdgeTaken P σ) V) (hlt : Chained (· < ·) V)
    {p : Nat} (hp : p ∈ V) :
    (∀ q ∈ V, q ≤ p) ∨
      ∃ n, EdgeTaken P σ p n ∧ (∀ q ∈ V, q ≤ p ∨ n ≤ q) := by
  induction V with
  | nil => cases hp
  | cons x rest ih =>
      rcases List.mem_cons.mp hp with rfl | hp'
      · cases rest with
        | nil =>
            refine Or.inl fun q hq => ?_
            obtain rfl := List.mem_singleton.mp hq
            exact Nat.le_refl _
        | cons y rest' =>
            obtain ⟨hExy, hEch⟩ := chained_destruct hedge
            obtain ⟨hLxy, hLch⟩ := chained_destruct hlt
            refine Or.inr ⟨y, hExy, fun q hq => ?_⟩
            rcases List.mem_cons.mp hq with rfl | hq'
            · exact Or.inl (Nat.le_refl _)
            · exact Or.inr (chained_lt_bound hLch rfl q hq')
      · cases rest with
        | nil => cases hp'
        | cons y rest' =>
            obtain ⟨hExy, hEch⟩ := chained_destruct hedge
            obtain ⟨hLxy, hLch⟩ := chained_destruct hlt
            have hxp : x ≤ p := Nat.le_of_lt
              (Nat.lt_of_lt_of_le hLxy (chained_lt_bound hLch rfl p hp'))
            rcases ih hEch hLch hp' with hmax | ⟨n, hE, hsp⟩
            · refine Or.inl fun q hq => ?_
              rcases List.mem_cons.mp hq with rfl | hq'
              · exact hxp
              · exact hmax q hq'
            · refine Or.inr ⟨n, hE, fun q hq => ?_⟩
              rcases List.mem_cons.mp hq with rfl | hq'
              · exact Or.inl hxp
              · exact hsp q hq'

theorem amoSide_at {P : Program} (hamo : amoSideOK P = true) {S : Nat}
    (hS : S < P.blocks.length) (hlen : 2 ≤ (predsOf P S).length) {p : Nat}
    (hp : p ∈ predsOf P S) : succsOf P p = [S] := by
  have h := List.all_eq_true.mp hamo S (List.mem_range.mpr hS)
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · have := of_decide_eq_true h
    omega
  · exact of_decide_eq_true (List.all_eq_true.mp h p hp)

/-- The at-most-one property of the actual execution: with the
critical-edge side condition, no failing run visits two distinct
predecessors of the same multi-predecessor join. -/
theorem visited_amo {P : Program} {σ : State} (hfwd : forwardOK P = true)
    (hamo : amoSideOK P = true) {V : List Nat}
    (hedge : Chained (EdgeTaken P σ) V) {S : Nat}
    (hS : S < P.blocks.length) (hlen : 2 ≤ (predsOf P S).length)
    {p₁ p₂ : Nat} (h1v : p₁ ∈ V) (h1p : p₁ ∈ predsOf P S)
    (h2v : p₂ ∈ V) (h2p : p₂ ∈ predsOf P S) : p₁ = p₂ := by
  have hlt : Chained (· < ·) V := hedge.imp fun a b h => h.lt hfwd
  have key : ∀ {q₁ q₂ : Nat}, q₁ ∈ V → q₁ ∈ predsOf P S → q₂ ∈ V →
      q₂ ∈ predsOf P S → q₁ < q₂ → False := by
    intro q₁ q₂ hv1 hp1 hv2 hp2 h12
    rcases chained_next hedge hlt hv1 with hmax | ⟨n, hE, hsp⟩
    · have := hmax q₂ hv2
      omega
    · have hn : n = S := by
        have hs := hE.mem_succs
        rw [amoSide_at hamo hS hlen hp1] at hs
        exact List.mem_singleton.mp hs
      subst hn
      have hq2S := pred_lt hfwd hp2
      rcases hsp q₂ hv2 with h | h <;> omega
  rcases Nat.lt_trichotomy p₁ p₂ with h | h | h
  · exact (key h1v h1p h2v h2p h).elim
  · exact h
  · exact (key h2v h2p h1v h1p h).elim

/-! ## Command coverage of visited blocks -/

/-- Final-state fact contributed by one executed command; phis keyed to
the block through which control entered. -/
def CmdFact (_P : Program) (σ : State) (prev : Option Nat) : Cmd → Prop
  | .assignI x e => σ.ints x = evalI σ e
  | .assignB c e => σ.bools c = evalB σ e
  | .havocI _ => True
  | .havocB _ => True
  | .phiI x arms => ∃ p src, prev = some p ∧ lookupArm arms p = some src
      ∧ σ.ints x = σ.ints src
  | .phiB c arms => ∃ p src, prev = some p ∧ lookupArm arms p = some src
      ∧ σ.bools c = σ.bools src
  | .assume e => evalB σ e = true
  | .assert c => σ.bools c = false

/-- Every command of the current block from `pc` on has its fact
(the single assert being last makes the coverage total). -/
theorem Suffix.covers {P : Program} {σ : State}
    (hone : singleAssertOK P = true) {b pc prev V}
    (h : Suffix P σ b pc prev V) :
    ∀ B i c', P.block? b = some B → B.cmds[i]? = some c' → pc ≤ i →
      CmdFact P σ prev c' := by
  induction h with
  | fail hB hc hfalse =>
      intro B' i c' hB' hc' hi
      obtain rfl := Option.some.inj (hB'.symm.trans hB)
      obtain ⟨b0, i0, c0, B0, heq, hB0, hc0, hlast⟩ := singleAssert_shape hone
      obtain ⟨rfl, rfl, rfl⟩ := singleAssert_unique hone hB0 hc0 hB hc
      obtain rfl := Option.some.inj (hB0.symm.trans hB)
      have hilen := (List.getElem?_eq_some_iff.mp hc').1
      obtain rfl : i = i0 := by omega
      obtain rfl := Option.some.inj (hc'.symm.trans hc)
      simpa [CmdFact] using hfalse
  | assignI hB hc hfact hS ih =>
      intro B' i c' hB' hc' hi
      obtain rfl := Option.some.inj (hB'.symm.trans hB)
      rcases Nat.eq_or_lt_of_le hi with rfl | hlt
      · obtain rfl := Option.some.inj (hc'.symm.trans hc)
        simpa [CmdFact] using hfact
      · exact ih B' i c' hB' hc' hlt
  | assignB hB hc hfact hS ih =>
      intro B' i c' hB' hc' hi
      obtain rfl := Option.some.inj (hB'.symm.trans hB)
      rcases Nat.eq_or_lt_of_le hi with rfl | hlt
      · obtain rfl := Option.some.inj (hc'.symm.trans hc)
        simpa [CmdFact] using hfact
      · exact ih B' i c' hB' hc' hlt
  | havocI hB hc hS ih =>
      intro B' i c' hB' hc' hi
      obtain rfl := Option.some.inj (hB'.symm.trans hB)
      rcases Nat.eq_or_lt_of_le hi with rfl | hlt
      · obtain rfl := Option.some.inj (hc'.symm.trans hc)
        simp [CmdFact]
      · exact ih B' i c' hB' hc' hlt
  | havocB hB hc hS ih =>
      intro B' i c' hB' hc' hi
      obtain rfl := Option.some.inj (hB'.symm.trans hB)
      rcases Nat.eq_or_lt_of_le hi with rfl | hlt
      · obtain rfl := Option.some.inj (hc'.symm.trans hc)
        simp [CmdFact]
      · exact ih B' i c' hB' hc' hlt
  | phiI hB hc harm hfact hS ih =>
      intro B' i c' hB' hc' hi
      obtain rfl := Option.some.inj (hB'.symm.trans hB)
      rcases Nat.eq_or_lt_of_le hi with rfl | hlt
      · obtain rfl := Option.some.inj (hc'.symm.trans hc)
        exact ⟨_, _, rfl, harm, hfact⟩
      · exact ih B' i c' hB' hc' hlt
  | phiB hB hc harm hfact hS ih =>
      intro B' i c' hB' hc' hi
      obtain rfl := Option.some.inj (hB'.symm.trans hB)
      rcases Nat.eq_or_lt_of_le hi with rfl | hlt
      · obtain rfl := Option.some.inj (hc'.symm.trans hc)
        exact ⟨_, _, rfl, harm, hfact⟩
      · exact ih B' i c' hB' hc' hlt
  | assume hB hc hfact hS ih =>
      intro B' i c' hB' hc' hi
      obtain rfl := Option.some.inj (hB'.symm.trans hB)
      rcases Nat.eq_or_lt_of_le hi with rfl | hlt
      · obtain rfl := Option.some.inj (hc'.symm.trans hc)
        simpa [CmdFact] using hfact
      · exact ih B' i c' hB' hc' hlt
  | goto hB hterm hS ih =>
      intro B' i c' hB' hc' hi
      obtain rfl := Option.some.inj (hB'.symm.trans hB)
      have := (List.getElem?_eq_some_iff.mp hc').1
      omega
  | ifTrue hB hterm hcond hS ih =>
      intro B' i c' hB' hc' hi
      obtain rfl := Option.some.inj (hB'.symm.trans hB)
      have := (List.getElem?_eq_some_iff.mp hc').1
      omega
  | ifFalse hB hterm hcond hS ih =>
      intro B' i c' hB' hc' hi
      obtain rfl := Option.some.inj (hB'.symm.trans hB)
      have := (List.getElem?_eq_some_iff.mp hc').1
      omega

/-- Consecutive visited pairs `(p, v)`: all of `v`'s commands have facts
keyed to predecessor `p`. -/
theorem Suffix.tail_covers {P : Program} {σ : State}
    (hone : singleAssertOK P = true) {b pc prev V}
    (h : Suffix P σ b pc prev V) :
    Chained (fun p v => ∀ (B : Block) (i : Nat) (c' : Cmd),
      P.block? v = some B → B.cmds[i]? = some c' →
      CmdFact P σ (some p) c') V := by
  induction h with
  | fail hB hc hfalse => trivial
  | assignI _ _ _ _ ih => exact ih
  | assignB _ _ _ _ ih => exact ih
  | havocI _ _ _ ih => exact ih
  | havocB _ _ _ ih => exact ih
  | phiI _ _ _ _ _ ih => exact ih
  | phiB _ _ _ _ _ ih => exact ih
  | assume _ _ _ _ ih => exact ih
  | goto hB hterm hS ih =>
      refine chained_cons (fun v hv => ?_) ih
      obtain rfl := Option.some.inj (hS.head.symm.trans hv)
      exact fun B i c' hB' hc' => hS.covers hone B i c' hB' hc' (Nat.zero_le i)
  | ifTrue hB hterm hcond hS ih =>
      refine chained_cons (fun v hv => ?_) ih
      obtain rfl := Option.some.inj (hS.head.symm.trans hv)
      exact fun B i c' hB' hc' => hS.covers hone B i c' hB' hc' (Nat.zero_le i)
  | ifFalse hB hterm hcond hS ih =>
      refine chained_cons (fun v hv => ?_) ih
      obtain rfl := Option.some.inj (hS.head.symm.trans hv)
      exact fun B i c' hB' hc' => hS.covers hone B i c' hB' hc' (Nat.zero_le i)

theorem getLast?_cons_of_some {a x : Nat} {V : List Nat}
    (h : V.getLast? = some x) : (a :: V).getLast? = some x := by
  cases V with
  | nil => cases h
  | cons v V' => rw [List.getLast?_cons_cons]; exact h

/-- The visited list ends at the failing assert's block. -/
theorem Suffix.last_block {P : Program} {σ : State} {b pc prev V}
    (h : Suffix P σ b pc prev V) :
    ∃ (bf : Nat) (Bf : Block) (pcf cf : Nat), V.getLast? = some bf
      ∧ P.block? bf = some Bf ∧ Bf.cmds[pcf]? = some (.assert cf)
      ∧ σ.bools cf = false := by
  induction h with
  | fail hB hc hfalse => exact ⟨_, _, _, _, rfl, hB, hc, hfalse⟩
  | assignI _ _ _ _ ih => exact ih
  | assignB _ _ _ _ ih => exact ih
  | havocI _ _ _ ih => exact ih
  | havocB _ _ _ ih => exact ih
  | phiI _ _ _ _ _ ih => exact ih
  | phiB _ _ _ _ _ ih => exact ih
  | assume _ _ _ _ ih => exact ih
  | goto hB hterm hS ih =>
      obtain ⟨bf, Bf, pcf, cf, hlast, h1, h2, h3⟩ := ih
      exact ⟨bf, Bf, pcf, cf, getLast?_cons_of_some hlast, h1, h2, h3⟩
  | ifTrue hB hterm hcond hS ih =>
      obtain ⟨bf, Bf, pcf, cf, hlast, h1, h2, h3⟩ := ih
      exact ⟨bf, Bf, pcf, cf, getLast?_cons_of_some hlast, h1, h2, h3⟩
  | ifFalse hB hterm hcond hS ih =>
      obtain ⟨bf, Bf, pcf, cf, hlast, h1, h2, h3⟩ := ih
      exact ⟨bf, Bf, pcf, cf, getLast?_cons_of_some hlast, h1, h2, h3⟩

theorem getLast?_mem {V : List Nat} {a : Nat} (h : V.getLast? = some a) :
    a ∈ V := by
  induction V with
  | nil => cases h
  | cons v V' ih =>
      cases V' with
      | nil =>
          have : v = a := by simpa using h
          subst this
          exact List.mem_cons_self ..
      | cons w V'' =>
          rw [List.getLast?_cons_cons] at h
          exact List.mem_cons_of_mem _ (ih h)

/-! ## Dominators of visited blocks are visited -/

def domOf (P : Program) (u : Nat) : List Nat := (domTable P).getD u []

theorem domClosed_entry {P : Program} (hdc : domClosedOK P = true) :
    ∀ d ∈ domOf P P.entry, d = P.entry := by
  rw [domClosedOK, Bool.and_eq_true] at hdc
  intro d hd
  exact of_decide_eq_true (List.all_eq_true.mp hdc.1 d hd)

theorem domClosed_edge {P : Program} (hdc : domClosedOK P = true)
    {p u : Nat} {cond : BExp} (hedge : (p, u, cond) ∈ Vc.allEdges P)
    (hne : u ≠ P.entry) : ∀ d ∈ domOf P u, d = u ∨ d ∈ domOf P p := by
  rw [domClosedOK, Bool.and_eq_true] at hdc
  have h := List.all_eq_true.mp hdc.2 (p, u, cond) hedge
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · exact absurd (of_decide_eq_true h) hne
  · intro d hd
    have h' := List.all_eq_true.mp h d hd
    rw [Bool.or_eq_true] at h'
    rcases h' with h' | h'
    · exact Or.inl (of_decide_eq_true h')
    · exact Or.inr (List.contains_iff_mem.mp h')

theorem EdgeTaken.mem_allEdges {P : Program} {σ : State} {u v : Nat}
    (h : EdgeTaken P σ u v) : ∃ cond, (u, v, cond) ∈ Vc.allEdges P := by
  obtain ⟨cond, hedge, -⟩ := h.edge_cond
  exact ⟨cond, mem_edgesTo.mp hedge⟩

theorem dom_visited_from {P : Program} {σ : State}
    (hdc : domClosedOK P = true) {W : List Nat} :
    ∀ {V : List Nat}, Chained (EdgeTaken P σ) V →
      (∀ v ∈ V, v ∈ W) →
      (∀ h ∈ V.head?, ∀ d ∈ domOf P h, d ∈ W) →
      (∀ v ∈ V.tail, v ≠ P.entry) →
      ∀ u ∈ V, ∀ d ∈ domOf P u, d ∈ W := by
  intro V
  induction V with
  | nil => intro _ _ _ _ u hu; cases hu
  | cons x rest ih =>
      intro hch hsub hhead hne u hu
      rcases List.mem_cons.mp hu with rfl | hu'
      · exact hhead u rfl
      · cases rest with
        | nil => cases hu'
        | cons y rest' =>
            obtain ⟨hExy, hEch⟩ := chained_destruct hch
            refine ih hEch
              (fun v hv => hsub v (List.mem_cons_of_mem _ hv)) ?_
              (fun v hv => hne v (List.mem_cons_of_mem _ hv)) u hu'
            intro h hh d hd
            obtain rfl := Option.some.inj hh
            obtain ⟨cond, hedge⟩ := hExy.mem_allEdges
            have hyne : y ≠ P.entry := hne y (List.mem_cons_self ..)
            rcases domClosed_edge hdc hedge hyne d hd with rfl | hda
            · exact hsub d (List.mem_cons_of_mem _ (List.mem_cons_self ..))
            · exact hhead x rfl d hda

theorem dom_visited {P : Program} {σ : State} (hdc : domClosedOK P = true)
    (hfwd : forwardOK P = true) {V : List Nat}
    (hedge : Chained (EdgeTaken P σ) V) (hhead : V.head? = some P.entry) :
    ∀ u ∈ V, ∀ d ∈ domOf P u, d ∈ V := by
  have hlt : Chained (· < ·) V := hedge.imp fun a b h => h.lt hfwd
  have hentry_mem : P.entry ∈ V := by
    cases V with
    | nil => cases hhead
    | cons v V' =>
        obtain rfl := Option.some.inj hhead
        exact List.mem_cons_self ..
  refine dom_visited_from hdc hedge (fun v hv => hv) ?_ ?_
  · intro h hh d hd
    obtain rfl := Option.some.inj (hhead.symm.trans hh)
    obtain rfl := domClosed_entry hdc d hd
    exact hentry_mem
  · intro v hv
    have := chained_lt_tail hlt hhead v hv
    omega

end Ttac
