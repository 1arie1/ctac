import Mathlib.Data.List.Chain
import Ttac.VcLemmas
import Ttac.VcCheck
import Ttac.Safety

/-!
# Execution-trace structure

The Prop layer over the Bool well-formedness checks: definition sites
and position order, the visited chain (`Chained`/`EdgeTaken` and its
ordering and at-most-one facts), per-command final-state facts
(`CmdFact` and the effect-table law `CmdFact.factB_eval`), the
single-assert shape, and the dominator bridges (`dom_visited`).

Everything is sort-generic: definition sites are `(Ty × Nat)` pairs
read off the effect table `Cmd.def?`, and the per-command content is
one case per command *kind*.
-/

namespace Ttac

/-! ## Definition sites, Prop layer -/

/-- Register `tx = (sort, index)` is defined at `(b, i)`. -/
def IsDefAt (P : Program) (tx : Ty × Nat) (b i : Nat) : Prop :=
  ∃ B c, P.block? b = some B ∧ B.cmds[i]? = some c ∧ c.def? = some tx

theorem mem_defPositions {P : Program} {tx : Ty × Nat} {d j : Nat} :
    ((d, j) : Pos) ∈ defPositions P tx ↔ IsDefAt P tx d j := by
  simp only [defPositions, List.mem_flatten, List.mem_map, IsDefAt]
  constructor
  · rintro ⟨L, ⟨⟨B, b⟩, hmem, rfl⟩, hin⟩
    rw [List.mem_filterMap] at hin
    obtain ⟨⟨c, i⟩, hci, hif⟩ := hin
    by_cases hfc : c.def? = some tx
    · rw [if_pos hfc] at hif
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp (Option.some.inj hif)
      exact ⟨B, c, List.mem_zipIdx_iff_getElem?.mp hmem,
        List.mem_zipIdx_iff_getElem?.mp hci, hfc⟩
    · rw [if_neg hfc] at hif; cases hif
  · rintro ⟨B, c, hB, hc, hfc⟩
    refine ⟨_, ⟨⟨B, d⟩, List.mem_zipIdx_iff_getElem?.mpr hB, rfl⟩, ?_⟩
    rw [List.mem_filterMap]
    exact ⟨(c, j), List.mem_zipIdx_iff_getElem?.mpr hc, by rw [if_pos hfc]⟩

/-- Every definition of `tx` sits strictly before position `p`. -/
def DefsBefore (P : Program) (tx : Ty × Nat) (p : Pos) : Prop :=
  ∀ d j, IsDefAt P tx d j → posLt (d, j) p = true

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

/-- Under SSA every register has a unique definition site. -/
theorem ssa_unique {P : Program} (hssa : ssaOK P = true) {tx : Ty × Nat}
    {b i : Nat} (h1 : IsDefAt P tx b i) {d j : Nat}
    (h2 : IsDefAt P tx d j) : d = b ∧ j = i := by
  obtain ⟨B, c, hB, hc, hfc⟩ := h1
  have hsite := ssaOK_at hssa hB hc
  rw [cmdSsaOK, hfc] at hsite
  have := List.all_eq_true.mp hsite (d, j) (mem_defPositions.mpr h2)
  have := of_decide_eq_true this
  exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩

/-- A def at `(b, i)` plus all-defs-before `(b, i)` is absurd. -/
theorem defsBefore_no_def_here {P : Program} {tx : Ty × Nat} {b i : Nat}
    (hdef : IsDefAt P tx b i) (h : DefsBefore P tx (b, i)) : False := by
  have := h b i hdef
  rw [posLt_irrefl] at this
  cases this

theorem useOK_before {P : Program} {tx : Ty × Nat} {b i : Nat}
    (h : useOK (domTable P) (defPositions P tx) b i = true) :
    DefsBefore P tx (b, i) := by
  intro d j hd
  have := List.all_eq_true.mp h (d, j) (mem_defPositions.mpr hd)
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this
  simp only [posLt, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  omega

theorem expUsesOK_before {P : Program} {b i : Nat} {t : Ty} {e : Exp t}
    (h : expUsesOK P (domTable P) b i e = true) :
    ∀ p ∈ e.vars, DefsBefore P p (b, i) :=
  fun p hp => useOK_before (List.all_eq_true.mp h p hp)

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
    (hB : P.block? b = some B) {t : Ty} {x : Nat} {arms : PhiArms}
    (hc : Cmd.phi t x arms ∈ B.cmds) : phiArmsOK P b arms = true := by
  have h1 := List.all_eq_true.mp hphi (B, b) (List.mem_zipIdx_iff_getElem?.mpr hB)
  exact List.all_eq_true.mp h1 _ hc

theorem phiArm_lt {P : Program} {b : Nat} {arms : PhiArms}
    (h : phiArmsOK P b arms = true) {p src : Nat} (hp : (p, src) ∈ arms) :
    p < b := by
  simp only [phiArmsOK, Bool.and_eq_true] at h
  have := List.all_eq_true.mp h.2 (p, src) hp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact this.1

theorem armUseOK_le {P : Program} {tx : Ty × Nat} {p : Nat}
    (h : armUseOK (domTable P) (defPositions P tx) p = true) :
    ∀ d j, IsDefAt P tx d j → d ≤ p := by
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

/-! ## The visited chain -/

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
        ((t = v ∧ σ.regs .bool c = true) ∨ (e = v ∧ σ.regs .bool c = false)))

theorem Chained.imp {R S : Nat → Nat → Prop} (h : ∀ a b, R a b → S a b) :
    ∀ {V : List Nat}, Chained R V → Chained S V
  | [], _ => trivial
  | [_], _ => trivial
  | _ :: _ :: _, ⟨hR, hch⟩ => ⟨h _ _ hR, Chained.imp h hch⟩

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
    ∃ cond, (u, cond) ∈ Vc.edgesTo P v ∧ cond.eval σ = true := by
  obtain ⟨B, hB, hshape⟩ := h
  rcases hshape with hgoto | ⟨c, t, e, hif, harm⟩
  · refine ⟨.litB true, mem_edgesTo.mpr (mem_allEdges_intro hB ?_), rfl⟩
    simp [Vc.outEdges, hgoto]
  · rcases harm with ⟨rfl, hc⟩ | ⟨rfl, hc⟩
    · refine ⟨.var .bool c, mem_edgesTo.mpr (mem_allEdges_intro hB ?_), by
        simp [Exp.eval, hc]⟩
      simp [Vc.outEdges, hif]
    · refine ⟨.un .not (.var .bool c),
        mem_edgesTo.mpr (mem_allEdges_intro hB ?_), by
          simp [Exp.eval, UnOp.denote, hc]⟩
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
def CmdFact (σ : State) (prev : Option Nat) : Cmd → Prop
  | .assign t x e => σ.regs t x = e.eval σ
  | .havoc _ _ => True
  | .phi t x arms => ∃ p src, prev = some p ∧ lookupArm arms p = some src
      ∧ σ.regs t x = σ.regs t src
  | .assume φ => φ.eval σ = true
  | .assert c => σ.regs .bool c = false

/-- The post-fact law of the effect table: a command's coverage fact
makes its `factB` entry true at σ. This is the single bridge the
guarded-fact robustness case consumes - one proof for every present
and future local instruction. -/
theorem CmdFact.factB_eval {σ : State} {prev : Option Nat} {c : Cmd}
    (h : CmdFact σ prev c) {f : BExp} (hf : c.factB = some f) :
    f.eval σ = true := by
  cases c with
  | assign t x e =>
      simp only [CmdFact] at h
      cases t with
      | int =>
          obtain rfl := Option.some.inj hf
          simp [Exp.eval, BinOp.denote, h]
      | bool =>
          obtain rfl := Option.some.inj hf
          simp [Exp.eval, BinOp.denote, h]
      | map => cases hf
  | assume φ =>
      obtain rfl := Option.some.inj hf
      exact h
  | havoc t x => cases hf
  | phi t x arms => cases hf
  | assert r => cases hf

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
