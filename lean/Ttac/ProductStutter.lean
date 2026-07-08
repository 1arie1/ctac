import Ttac.Product

/-!
# The rw-eq product under CFG surgery (stuttering mode), verified

The lockstep development (`Ttac/Product.lean`) is complete and
deliberately kept simple; this file extends it to CFG surgery — the
rewrite `B` drops blocks of `A` (`ctac cfg-simplify`'s fall-through
elimination), so `A` *stutters* through dropped blocks between
synchronization points. The transfer theorem is proved:

    stutter_transfer :
      WellFormed A → WellFormed B → domClosedOK B →
      surgeryOK A B mt → Safe_denot (productS A B mt) →
      Safe_denot B → Safe_denot A

with `stutter_transfer_safe` as the operational form. Against the
probe-stage conjecture the hypotheses *shrank* twice: `domClosedOK A`
is not needed (A-side dominance is replaced by walking `B`'s closure
facts along the matched projection of `A`'s active path,
`good_of_domB`), and neither is `phiCoversOK B` (the `surgeryOK`
routing check subsumes coverage at every join the transfer inspects).

## The witness

`B`'s blocks are a compacted subsequence of `A`'s, so the
correspondence cannot be positional: the *matching*
`mt : List (Option Nat)` (`mt[a] = some b` iff `A`-block `a` is
`B`-block `b`; `none` marks a stutter block) is untrusted input,
validated by the decidable `surgeryOK` — the Lean-side analog of
rw-eq's `sim_precheck`. Scope of this round, matching what
`cfg-simplify` emits: stutter blocks are single-predecessor `goto`
blocks (linear chains), matched terminators have the same kind, and
each `A`-target *chases* through its chain to a matched block whose
match is `B`'s corresponding target.

## Ownership-routed phis instead of DEST ghosts

The implementation's DEST/IN_DEST flags materialize "After waits for
Before" for the SMT encoding. Denotationally there is no waiting —
both final states just exist — and inside the `WellFormed` fragment
the flags turn out to be unnecessary altogether: the shape that would
genuinely need a committed-destination ghost (two `B`-predecessors of
one join both lying on a single A-path) requires a critical edge — a
branching block feeding a multi-predecessor join — which `amoSideOK`
on `B` forbids, and the chase/kind-matching conditions exclude the
remaining variants. What *does* have to change is arm keying: `B`'s
phi arms name `B`-predecessors in `B`'s compacted index space
(meaningless against the product's guards, which are `A`'s), and `A`
arrives at a join via a chain *tail*, not the divergence point
itself. The product therefore *re-keys* each B-copy phi on `A`'s
CFG: one arm per `A`-predecessor `p` of the join, with source looked
up from `B`'s arm of `matchOf (owner p)` — `owner p` being the
matched block whose stutter chain contains `p` (computable by walking
the single-predecessor chain backwards). Selection then rides `A`'s
at-most-one-active-predecessor exactly as in lockstep, and the DEST
commitment becomes the proof obligation
`matchOf (owner (A's taken pred)) = B's taken pred` instead of
program state.

## Proof shape

The doubled final-state seeding and the deposit/extraction machinery
of the lockstep proof carry over (`prodCmdA_foldS` is again the
identity). The new content: `stutter_origin` walks an active stutter
block back to its active matched owner whose taken edge chases to the
same sync point (forward-only — chain assumes are never needed ahead
of the walk); `proj_chained`/`good_of_domB` replace cross-CFG
dominance by projecting the active path onto `B`'s CFG structurally
and running `B`'s `domClosedOK` facts along it (`dom_in_visited`, a
condition-free `dom_visited`); and `prodCmdBS_step`'s phi case proves
the ownership routing selects, on both sides, the arm of the taken
predecessor's owner.
-/

namespace Ttac

open Vc

/-! ## The matching and its derived maps -/

/-- The match of an `A`-block, if any. -/
def matchOf (mt : List (Option Nat)) (a : Nat) : Option Nat :=
  (mt[a]?).getD none

/-- The owning matched block of a stutter block: walk the (validated:
unique) predecessor chain backwards until a matched block. Fuel-bounded
by the block index (predecessors are strictly smaller under
`forwardOK`); a miscomputed owner is rejected by `surgeryOK`, never
trusted. -/
def ownerGo (A : Program) (mt : List (Option Nat)) : Nat → Nat → Nat
  | 0, a => a
  | fuel + 1, a =>
      if (matchOf mt a).isSome then a
      else match predsOf A a with
        | [q] => ownerGo A mt fuel q
        | _ => a

def owner (A : Program) (mt : List (Option Nat)) (a : Nat) : Nat :=
  ownerGo A mt a a

/-- Chase an `A`-target through its stutter chain to the matched block
it resolves to. -/
def chaseGo (A : Program) (mt : List (Option Nat)) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, a =>
      if (matchOf mt a).isSome then some a
      else match A.block? a with
        | some Ba =>
            match Ba.term with
            | .goto t => chaseGo A mt fuel t
            | _ => none
        | none => none

def chase (A : Program) (mt : List (Option Nat)) (a : Nat) : Option Nat :=
  chaseGo A mt A.blocks.length a

/-! ## The surgical product -/

/-- B-copy emission at a matched block: identical to the lockstep
`prodCmdB` except for phis, which are re-keyed on `A`'s predecessors
with ownership-routed sources (see the module docstring). A failed
lookup falls back to register 0 — junk that `surgeryOK`'s routing
check rules out. -/
def prodCmdBS (A : Program) (mt : List (Option Nat)) (Ba : Block)
    (stride k i : Nat) : Cmd → List Cmd
  | .phi t x arms =>
      [.phi t (pv 1 x) ((predsOf A k).map fun p =>
        (p, pv 1 ((lookupArm arms
          ((matchOf mt (owner A mt p)).getD 0)).getD 0)))]
  | c => prodCmdB A Ba stride k i c

/-- The stutter shape: A-copy only. -/
def stutterBlockS (Ba : Block) : Block where
  cmds := Ba.cmds.flatMap prodCmdA
  term := Ba.term.rename (pv 0)

/-- The matched shape: both copies plus CHKs, as in lockstep. -/
def matchedBlockS (A : Program) (mt : List (Option Nat)) (stride k : Nat)
    (Ba Bb : Block) : Block where
  cmds := Ba.cmds.flatMap prodCmdA
    ++ Bb.cmds.zipIdx.flatMap (fun ci =>
        prodCmdBS A mt Ba stride k ci.2 ci.1)
    ++ prodTermChk stride k Ba Bb
  term := Ba.term.rename (pv 0)

/-- Product block: matched blocks interleave both copies plus CHKs
(as in lockstep); stutter blocks carry the A-copy only. -/
def prodBlockS (A B : Program) (mt : List (Option Nat)) (stride k : Nat)
    (Ba : Block) : Block :=
  match matchOf mt k with
  | none => stutterBlockS Ba
  | some kb =>
      match B.block? kb with
      | none => stutterBlockS Ba
      | some Bb => matchedBlockS A mt stride k Ba Bb

def productS (A B : Program) (mt : List (Option Nat)) : Program where
  blocks := A.blocks.zipIdx.map fun p =>
    prodBlockS A B mt (chkStride B.blocks) p.2 p.1
  entry := A.entry
  exit := A.exit

/-! ## The validator -/

/-- The `A`-target `ta` resolves through its chain to `B`'s target
`tb`. -/
def chaseTargetOK (A B : Program) (mt : List (Option Nat))
    (ta tb : Nat) : Bool :=
  match chase A mt ta with
  | some t' => matchOf mt t' == some tb && tb < B.blocks.length
  | none => false

/-- Matched terminators: same kind, targets correspond through the
chase. Conditions are free to differ (they get the branch CHK). -/
def termSurgeryOK (A B : Program) (mt : List (Option Nat)) :
    Terminator → Terminator → Bool
  | .halt, .halt => true
  | .goto ta, .goto tb => chaseTargetOK A B mt ta tb
  | .ifGoto _ ta ea, .ifGoto _ tb eb =>
      chaseTargetOK A B mt ta tb && chaseTargetOK A B mt ea eb
  | _, _ => false

/-- Round-1 stutter-block discipline: a single-predecessor `goto`
block with no assert (matching `cfg-simplify`'s fall-through shape). -/
def stutterBlockOK (A : Program) (a : Nat) (Ba : Block) : Bool :=
  (match Ba.term with | .goto _ => true | _ => false)
    && decide ((predsOf A a).length = 1)
    && Ba.cmds.all fun c =>
        match c with | .assert _ => false | _ => true

/-- Every `A`-predecessor of a matched phi block routes: its owner is
matched, and `B`'s phi has an arm for the owner's match. -/
def phiRouteOK (A : Program) (mt : List (Option Nat)) (k : Nat)
    (Bb : Block) : Bool :=
  Bb.cmds.all fun c =>
    match c with
    | .phi _ _ arms =>
        (predsOf A k).all fun p =>
          match matchOf mt (owner A mt p) with
          | some ob => (lookupArm arms ob).isSome
          | none => false
    | _ => true

/-- The full witness check — the Lean-side `sim_precheck`. -/
def surgeryOK (A B : Program) (mt : List (Option Nat)) : Bool :=
  decide (mt.length = A.blocks.length)
    && (matchOf mt A.entry == some B.entry)
    && (A.blocks.zipIdx.all fun (Ba, k) =>
        match matchOf mt k with
        | none => stutterBlockOK A k Ba
        | some kb =>
            match B.block? kb with
            | none => false
            | some Bb =>
                termSurgeryOK A B mt Ba.term Bb.term
                  && phiRouteOK A mt k Bb)
    -- the matching is strictly monotone (a subsequence), hence injective
    && ((List.range A.blocks.length).all fun a =>
        (List.range a).all fun a' =>
          match matchOf mt a', matchOf mt a with
          | some b', some b => decide (b' < b)
          | _, _ => true)
    -- the single asserts sit at matched blocks that correspond
    && (match assertSites A, assertSites B with
        | [(aB, _, _)], [(bB, _, _)] => matchOf mt aB == some bB
        | _, _ => false)

/-! ## Witness facts

Everything the proof extracts from `surgeryOK` and the fuel-bounded
maps. Fuel stability turns `ownerGo`/`chaseGo` into their intended
recurrences under `forwardOK`. -/

theorem matchOf_lt {mt : List (Option Nat)} {L : Nat}
    (hlen : mt.length = L) {a b : Nat} (h : matchOf mt a = some b) :
    a < L := by
  unfold matchOf at h
  cases ha : mt[a]? with
  | none => rw [ha] at h; cases h
  | some o =>
      have := (List.getElem?_eq_some_iff.mp ha).1
      omega

theorem matchOf_none_of_ge {mt : List (Option Nat)} {a : Nat}
    (h : mt.length ≤ a) : matchOf mt a = none := by
  unfold matchOf
  rw [List.getElem?_eq_none_iff.mpr h]
  rfl

/-- The strict-monotonicity conjunct of `surgeryOK`, extracted. -/
theorem surgery_mono {A B : Program} {mt : List (Option Nat)}
    (hs : surgeryOK A B mt = true) {a' a b' b : Nat} (hlt : a' < a)
    (ha : a < A.blocks.length)
    (h' : matchOf mt a' = some b') (h : matchOf mt a = some b) :
    b' < b := by
  unfold surgeryOK at hs
  simp only [Bool.and_eq_true] at hs
  have hmono := hs.1.2
  have h1 := List.all_eq_true.mp hmono a (List.mem_range.mpr ha)
  have h2 := List.all_eq_true.mp h1 a' (List.mem_range.mpr hlt)
  rw [h', h] at h2
  exact of_decide_eq_true h2

theorem matchOf_inj {A B : Program} {mt : List (Option Nat)}
    (hs : surgeryOK A B mt = true)
    (hlen : mt.length = A.blocks.length) {a a' b : Nat}
    (h : matchOf mt a = some b) (h' : matchOf mt a' = some b) : a = a' := by
  rcases Nat.lt_trichotomy a a' with hlt | heq | hgt
  · exact absurd (surgery_mono hs hlt (matchOf_lt hlen h') h h')
      (Nat.lt_irrefl b)
  · exact heq
  · exact absurd (surgery_mono hs hgt (matchOf_lt hlen h) h' h)
      (Nat.lt_irrefl b)

/-- The per-block conjunct of `surgeryOK`, extracted. -/
theorem surgery_block {A B : Program} {mt : List (Option Nat)}
    (hs : surgeryOK A B mt = true) {k : Nat} {Ba : Block}
    (hBa : A.block? k = some Ba) :
    (matchOf mt k = none → stutterBlockOK A k Ba = true)
    ∧ (∀ kb, matchOf mt k = some kb → ∃ Bb, B.block? kb = some Bb
        ∧ termSurgeryOK A B mt Ba.term Bb.term = true
        ∧ phiRouteOK A mt k Bb = true) := by
  unfold surgeryOK at hs
  simp only [Bool.and_eq_true] at hs
  have hblocks := hs.1.1.2
  have h1 := List.all_eq_true.mp hblocks (Ba, k)
    (List.mem_zipIdx_iff_getElem?.mpr hBa)
  constructor
  · intro hnone
    rw [hnone] at h1
    exact h1
  · intro kb hkb
    rw [hkb] at h1
    have h2 : (match B.block? kb with
        | none => false
        | some Bb => termSurgeryOK A B mt Ba.term Bb.term
            && phiRouteOK A mt k Bb) = true := h1
    cases hBb : B.block? kb with
    | none => rw [hBb] at h2; cases h2
    | some Bb =>
        rw [hBb] at h2
        have h3 : (termSurgeryOK A B mt Ba.term Bb.term
            && phiRouteOK A mt k Bb) = true := h2
        rw [Bool.and_eq_true] at h3
        exact ⟨Bb, rfl, h3.1, h3.2⟩

theorem surgery_len {A B : Program} {mt : List (Option Nat)}
    (hs : surgeryOK A B mt = true) : mt.length = A.blocks.length := by
  unfold surgeryOK at hs
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
  exact hs.1.1.1.1

theorem surgery_entry {A B : Program} {mt : List (Option Nat)}
    (hs : surgeryOK A B mt = true) :
    matchOf mt A.entry = some B.entry := by
  unfold surgeryOK at hs
  simp only [Bool.and_eq_true] at hs
  exact beq_iff_eq.mp hs.1.1.1.2

theorem surgery_sites {A B : Program} {mt : List (Option Nat)}
    (hs : surgeryOK A B mt = true) {aB iA cA bB iB cB : Nat}
    (hA : Vc.assertSites A = [(aB, iA, cA)])
    (hB : Vc.assertSites B = [(bB, iB, cB)]) :
    matchOf mt aB = some bB := by
  unfold surgeryOK at hs
  simp only [Bool.and_eq_true] at hs
  have := hs.2
  rw [hA, hB] at this
  exact beq_iff_eq.mp this

/-! ## Fuel stability -/

theorem owner_matched {A : Program} {mt : List (Option Nat)} {a : Nat}
    (h : (matchOf mt a).isSome) : owner A mt a = a := by
  unfold owner
  cases a with
  | zero => rfl
  | succ n =>
      show ownerGo A mt (n + 1) (n + 1) = n + 1
      unfold ownerGo
      rw [if_pos h]

theorem ownerGo_stable {A : Program} {mt : List (Option Nat)}
    (hfwd : forwardOK A = true) :
    ∀ (a : Nat), ∀ (f : Nat), a ≤ f →
      ownerGo A mt f a = owner A mt a := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
      intro f hf
      by_cases hm : (matchOf mt a).isSome
      · rw [owner_matched hm]
        cases f with
        | zero => rfl
        | succ g => unfold ownerGo; rw [if_pos hm]
      · cases ha : predsOf A a with
        | nil =>
            cases f with
            | zero =>
                obtain rfl : a = 0 := by omega
                rfl
            | succ g =>
                unfold ownerGo
                rw [if_neg hm, ha]
                unfold owner
                cases a with
                | zero => rfl
                | succ n =>
                    show _ = ownerGo A mt (n + 1) (n + 1)
                    conv_rhs => unfold ownerGo
                    rw [if_neg hm, ha]
        | cons q rest =>
            have hqlt : q < a := pred_lt hfwd (by
              rw [ha]; exact List.mem_cons_self ..)
            cases rest with
            | nil =>
                cases f with
                | zero => omega
                | succ g =>
                    unfold ownerGo
                    rw [if_neg hm, ha]
                    show ownerGo A mt g q = _
                    rw [ih q hqlt g (by omega)]
                    unfold owner
                    cases a with
                    | zero => omega
                    | succ n =>
                        show _ = ownerGo A mt (n + 1) (n + 1)
                        conv_rhs => unfold ownerGo
                        rw [if_neg hm, ha]
                        show _ = ownerGo A mt n q
                        rw [ih q hqlt n (by omega)]
                        rfl
            | cons q' rest' =>
                cases f with
                | zero => omega
                | succ g =>
                    unfold ownerGo
                    rw [if_neg hm, ha]
                    unfold owner
                    cases a with
                    | zero => omega
                    | succ n =>
                        show _ = ownerGo A mt (n + 1) (n + 1)
                        conv_rhs => unfold ownerGo
                        rw [if_neg hm, ha]

theorem chaseGo_stable {A : Program} {mt : List (Option Nat)}
    (hfwd : forwardOK A = true) (hlen : mt.length = A.blocks.length) :
    ∀ (n a f f' : Nat), A.blocks.length - a ≤ n →
      A.blocks.length - a ≤ f → A.blocks.length - a ≤ f' →
      chaseGo A mt f a = chaseGo A mt f' a := by
  intro n
  induction n with
  | zero =>
      intro a f f' hn hf hf'
      have ha : A.blocks.length ≤ a := by omega
      have hm : matchOf mt a = none := matchOf_none_of_ge (by omega)
      have hb : A.block? a = none :=
        List.getElem?_eq_none_iff.mpr (by omega)
      cases f with
      | zero =>
          cases f' with
          | zero => rfl
          | succ g' =>
              show _ = chaseGo A mt (g' + 1) a
              unfold chaseGo
              rw [hm]
              show (none : Option Nat) = _
              simp [hb]
      | succ g =>
          cases f' with
          | zero =>
              show chaseGo A mt (g + 1) a = _
              unfold chaseGo
              rw [hm]
              simp [hb]
          | succ g' =>
              unfold chaseGo
              rw [hm]
              simp [hb]
  | succ n ih =>
      intro a f f' hn hf hf'
      rcases Nat.lt_or_ge a A.blocks.length with halt | hage
      · have hfpos : 0 < f := by omega
        have hf'pos : 0 < f' := by omega
        obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
        obtain ⟨g', rfl⟩ : ∃ g', f' = g' + 1 := ⟨f' - 1, by omega⟩
        have hBa : A.block? a = some A.blocks[a] :=
          List.getElem?_eq_getElem halt
        unfold chaseGo
        by_cases hm : (matchOf mt a).isSome
        · simp only [if_pos hm]
        · simp only [if_neg hm, hBa]
          cases ht : (A.blocks[a]).term with
          | goto t =>
              have htgt := forward_target hfwd hBa (by
                rw [ht]; exact List.mem_singleton.mpr rfl)
              show chaseGo A mt g t = chaseGo A mt g' t
              exact ih t g g' (by omega) (by omega) (by omega)
          | halt => rfl
          | ifGoto c th el => rfl
      · exact ih a f f' (by omega) hf hf'

theorem chase_matched {A : Program} {mt : List (Option Nat)}
    (hpos : 0 < A.blocks.length) {a : Nat}
    (h : (matchOf mt a).isSome) : chase A mt a = some a := by
  unfold chase
  obtain ⟨g, hg⟩ : ∃ g, A.blocks.length = g + 1 :=
    ⟨A.blocks.length - 1, by omega⟩
  rw [hg]
  show (if (matchOf mt a).isSome then some a
    else match A.block? a with
      | some Ba => match Ba.term with
          | .goto t' => chaseGo A mt g t'
          | _ => none
      | none => none) = some a
  rw [if_pos h]

theorem chase_stutter_step {A : Program} {mt : List (Option Nat)}
    (hfwd : forwardOK A = true) (hlen : mt.length = A.blocks.length)
    {p : Nat} (hp : matchOf mt p = none) {Bp : Block}
    (hBp : A.block? p = some Bp) {t : Nat} (ht : Bp.term = .goto t) :
    chase A mt p = chase A mt t := by
  have hplt : p < A.blocks.length := (List.getElem?_eq_some_iff.mp hBp).1
  have htgt := forward_target hfwd hBp (by
    rw [ht]; exact List.mem_singleton.mpr rfl)
  unfold chase
  obtain ⟨g, hg⟩ : ∃ g, A.blocks.length = g + 1 :=
    ⟨A.blocks.length - 1, by omega⟩
  rw [hg]
  have hstep : chaseGo A mt (g + 1) p = chaseGo A mt g t := by
    show (if (matchOf mt p).isSome then some p
      else match A.block? p with
        | some Ba => match Ba.term with
            | .goto t' => chaseGo A mt g t'
            | _ => none
        | none => none) = chaseGo A mt g t
    rw [if_neg (by rw [hp]; simp), hBp]
    show (match Bp.term with
      | .goto t' => chaseGo A mt g t'
      | _ => none) = chaseGo A mt g t
    rw [ht]
  rw [hstep]
  exact chaseGo_stable hfwd hlen (A.blocks.length - t) t g (g + 1)
    (Nat.le_refl _) (by omega) (by omega)

/-! ## The chain-origin fact

An A-active stutter block traces back through its (unique-predecessor)
chain to an active *matched* owner whose taken edge enters the chain —
and the chase from that entry point agrees with the chase from the
stutter block. This is the forward-only replacement for DEST: it never
needs the chain's assumes to hold ahead of the walk. -/

theorem stutter_origin {A B : Program} {mt : List (Option Nat)}
    {s0 : State} (hwfA : WellFormed A)
    (hs : surgeryOK A B mt = true) :
    ∀ (p : Nat), matchOf mt p = none → (denot A s0).blks p = true →
      p < A.blocks.length →
      (matchOf mt (owner A mt p)).isSome
      ∧ (denot A s0).blks (owner A mt p) = true
      ∧ ∃ h, EdgeTaken A (denot A s0) (owner A mt p) h
          ∧ chase A mt h = chase A mt p := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
      intro hpm hpact hplt
      have hBp : A.block? p = some A.blocks[p] :=
        List.getElem?_eq_getElem hplt
      have hpne : p ≠ A.entry := by
        intro heq
        rw [heq, surgery_entry hs] at hpm
        cases hpm
      obtain ⟨q, hqact, hqlt, hqE⟩ :=
        denot_active_pred hwfA.fwd hwfA.uses hBp hpact hpne
      have hstut := (surgery_block hs hBp).1 hpm
      unfold stutterBlockOK at hstut
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hstut
      have hqmem : q ∈ predsOf A p := by
        obtain ⟨cond, hcm, -⟩ := hqE.edge_cond
        exact mem_predsOf.mpr ⟨cond, hcm⟩
      obtain ⟨q', hq'⟩ : ∃ q', predsOf A p = [q'] := by
        cases hpp : predsOf A p with
        | nil => rw [hpp] at hqmem; cases hqmem
        | cons x rest =>
            cases rest with
            | nil => exact ⟨x, rfl⟩
            | cons y rest' =>
                rw [hpp] at hstut
                simp at hstut
      obtain rfl : q = q' := by
        rw [hq'] at hqmem
        exact List.mem_singleton.mp hqmem
      -- owner p = owner q
      have howner : owner A mt p = owner A mt q := by
        obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
        show (if (matchOf mt (n + 1)).isSome then (n + 1)
          else match predsOf A (n + 1) with
            | [q'] => ownerGo A mt n q'
            | _ => (n + 1)) = owner A mt q
        rw [if_neg (by rw [hpm]; simp), hq']
        show ownerGo A mt n q = _
        exact ownerGo_stable hwfA.fwd q n (by omega)
      by_cases hqm : (matchOf mt q).isSome
      · -- the chain head: the taken edge from the matched owner is q → p
        rw [howner, owner_matched hqm]
        exact ⟨hqm, hqact, p, hqE, rfl⟩
      · -- recurse up the chain
        have hqmnone : matchOf mt q = none := by
          cases h : matchOf mt q with
          | none => rfl
          | some b => rw [h] at hqm; simp at hqm
        obtain ⟨ho1, ho2, h, hE, hch⟩ := ih q hqlt hqmnone hqact (by omega)
        rw [howner]
        refine ⟨ho1, ho2, h, hE, ?_⟩
        rw [hch]
        -- chase q = chase p: q's goto is the taken edge into p
        have hBq : A.block? q = some A.blocks[q] :=
          List.getElem?_eq_getElem (by omega)
        have hqstut := (surgery_block hs hBq).1 hqmnone
        unfold stutterBlockOK at hqstut
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hqstut
        obtain ⟨tq, htq⟩ : ∃ tq, (A.blocks[q]).term = .goto tq := by
          cases h' : (A.blocks[q]).term with
          | goto t => exact ⟨t, rfl⟩
          | halt => rw [h'] at hqstut; simp at hqstut
          | ifGoto c th el => rw [h'] at hqstut; simp at hqstut
        obtain rfl : tq = p := by
          obtain ⟨Bq', hBq', hshape⟩ := hqE
          obtain rfl : A.blocks[q] = Bq' :=
            Option.some.inj (hBq.symm.trans hBq')
          rcases hshape with hgoto | ⟨c, th, el, hif, -⟩
          · rw [htq] at hgoto
            exact Terminator.goto.inj hgoto
          · rw [htq] at hif
            cases hif
        exact chase_stutter_step hwfA.fwd (surgery_len hs) hqmnone hBq htq

/-! ## Structural lemmas about the surgical product -/

theorem productS_block? {A B : Program} {mt : List (Option Nat)}
    {k : Nat} {Ba : Block} (hBa : A.block? k = some Ba) :
    (productS A B mt).block? k
      = some (prodBlockS A B mt (chkStride B.blocks) k Ba) := by
  unfold productS Program.block? at *
  rw [List.getElem?_map, List.getElem?_zipIdx, hBa]
  simp

theorem productS_length (A B : Program) (mt : List (Option Nat)) :
    (productS A B mt).blocks.length = A.blocks.length := by
  unfold productS
  simp

theorem productS_entry (A B : Program) (mt : List (Option Nat)) :
    (productS A B mt).entry = A.entry := rfl

/-- The matched shape, exposed. -/
theorem prodBlockS_matched {A B : Program} {mt : List (Option Nat)}
    {stride k kb : Nat} {Ba Bb : Block} (hm : matchOf mt k = some kb)
    (hBb : B.block? kb = some Bb) :
    prodBlockS A B mt stride k Ba = matchedBlockS A mt stride k Ba Bb := by
  unfold prodBlockS
  rw [hm]
  show (match B.block? kb with
    | none => stutterBlockS Ba
    | some Bb => matchedBlockS A mt stride k Ba Bb) = _
  rw [hBb]

theorem prodBlockS_stutter {A B : Program} {mt : List (Option Nat)}
    {stride k : Nat} {Ba : Block} (hm : matchOf mt k = none) :
    prodBlockS A B mt stride k Ba = stutterBlockS Ba := by
  unfold prodBlockS
  rw [hm]

theorem prodBlockS_unmatched {A B : Program} {mt : List (Option Nat)}
    {stride k kb : Nat} {Ba : Block} (hm : matchOf mt k = some kb)
    (hBb : B.block? kb = none) :
    prodBlockS A B mt stride k Ba = stutterBlockS Ba := by
  unfold prodBlockS
  rw [hm]
  show (match B.block? kb with
    | none => stutterBlockS Ba
    | some Bb => matchedBlockS A mt stride k Ba Bb) = _
  rw [hBb]

theorem prodBlockS_term {A B : Program} {mt : List (Option Nat)}
    {stride k : Nat} {Ba : Block} :
    (prodBlockS A B mt stride k Ba).term = Ba.term.rename (pv 0) := by
  cases hm : matchOf mt k with
  | none => rw [prodBlockS_stutter hm]; rfl
  | some kb =>
      cases hBb : B.block? kb with
      | none => rw [prodBlockS_unmatched hm hBb]; rfl
      | some Bb => rw [prodBlockS_matched hm hBb]; rfl

theorem outEdges_prodBlockS {A B : Program} {mt : List (Option Nat)}
    {stride k p : Nat} {Ba : Block} :
    Vc.outEdges p (prodBlockS A B mt stride k Ba)
      = (Vc.outEdges p Ba).map fun e =>
          (e.1, e.2.1, e.2.2.rename (pv 0)) := by
  unfold Vc.outEdges
  rw [prodBlockS_term]
  cases hT : Ba.term <;>
    simp [Terminator.rename, Exp.rename]

theorem mem_edgesTo_productS {A B : Program} {mt : List (Option Nat)}
    {b p : Nat} {cond' : BExp} :
    (p, cond') ∈ Vc.edgesTo (productS A B mt) b ↔
      ∃ cond, (p, cond) ∈ Vc.edgesTo A b ∧ cond' = cond.rename (pv 0) := by
  constructor
  · intro h
    obtain ⟨Bp', hBp', hout⟩ := mem_allEdges_elim (mem_edgesTo.mp h)
    have hplt : p < (productS A B mt).blocks.length :=
      (List.getElem?_eq_some_iff.mp hBp').1
    rw [productS_length] at hplt
    have hBa : A.block? p = some A.blocks[p] := List.getElem?_eq_getElem hplt
    obtain rfl : Bp' = prodBlockS A B mt (chkStride B.blocks) p A.blocks[p] :=
      Option.some.inj (hBp'.symm.trans (productS_block? hBa))
    rw [outEdges_prodBlockS, List.mem_map] at hout
    obtain ⟨⟨q, s', cond⟩, hmem, heq⟩ := hout
    obtain ⟨rfl, -⟩ := outEdges_shape hmem
    simp only [Prod.mk.injEq] at heq
    obtain ⟨-, hs', rfl⟩ := heq
    subst hs'
    exact ⟨cond, mem_edgesTo.mpr (mem_allEdges_intro hBa hmem), rfl⟩
  · rintro ⟨cond, h, rfl⟩
    obtain ⟨Ba, hBa, hout⟩ := mem_allEdges_elim (mem_edgesTo.mp h)
    refine mem_edgesTo.mpr (mem_allEdges_intro (productS_block? hBa) ?_)
    rw [outEdges_prodBlockS, List.mem_map]
    exact ⟨(p, b, cond), hout, rfl⟩

theorem reach_productS {A B : Program} {mt : List (Option Nat)}
    (hfwd : forwardOK A = true) {b : Nat} {R W : State}
    (hv : ∀ t x, R.regs t (pv 0 x) = W.regs t x)
    (hb : ∀ p, p < b → R.blks p = W.blks p) :
    reach (productS A B mt) R b = reach A W b := by
  unfold reach
  rw [productS_entry]
  congr 1
  rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨⟨p, cond'⟩, hmem, hpc⟩
    obtain ⟨cond, hmemA, rfl⟩ := mem_edgesTo_productS.mp hmem
    rw [Bool.and_eq_true] at hpc
    have hplt : p < b := pred_lt hfwd (mem_predsOf.mpr ⟨cond, hmemA⟩)
    refine ⟨(p, cond), hmemA, ?_⟩
    rw [Bool.and_eq_true]
    exact ⟨by rw [← hb p hplt]; exact hpc.1,
      by rw [← edge_cond_rename_eval hmemA hv]; exact hpc.2⟩
  · rintro ⟨⟨p, cond⟩, hmemA, hpc⟩
    rw [Bool.and_eq_true] at hpc
    have hplt : p < b := pred_lt hfwd (mem_predsOf.mpr ⟨cond, hmemA⟩)
    refine ⟨(p, cond.rename (pv 0)), mem_edgesTo_productS.mpr
      ⟨cond, hmemA, rfl⟩, ?_⟩
    rw [Bool.and_eq_true]
    exact ⟨by rw [hb p hplt]; exact hpc.1,
      by rw [edge_cond_rename_eval hmemA hv]; exact hpc.2⟩

/-! ## B-copy emission anatomy -/

/-- Everything `prodCmdBS` emits is a `prodCmdB` emission or the
routed phi. -/
theorem prodCmdBS_cases {A : Program} {mt : List (Option Nat)}
    {Ba : Block} {stride k i : Nat} {c c' : Cmd}
    (hc' : c' ∈ prodCmdBS A mt Ba stride k i c) :
    c' ∈ prodCmdB A Ba stride k i c
      ∨ ∃ t x arms, c = .phi t x arms
          ∧ c' = .phi t (pv 1 x) ((predsOf A k).map fun p =>
              (p, pv 1 ((lookupArm arms
                ((matchOf mt (owner A mt p)).getD 0)).getD 0))) := by
  cases c with
  | phi t x arms =>
      right
      simp only [prodCmdBS, List.mem_singleton] at hc'
      exact ⟨t, x, arms, rfl, hc'⟩
  | assume φ => exact Or.inl hc'
  | assert r => exact Or.inl hc'
  | havoc t x => exact Or.inl hc'
  | assign t x e => exact Or.inl hc'

theorem prodCmdBS_def_target {A : Program} {mt : List (Option Nat)}
    {Ba : Block} {stride k i : Nat} {c c' : Cmd}
    (hc' : c' ∈ prodCmdBS A mt Ba stride k i c)
    {t : Ty} {w : Nat} (hdef : c'.def? = some (t, w)) :
    (∃ x, w = pv 1 x) ∨ w = chkReg stride k i := by
  rcases prodCmdBS_cases hc' with h | ⟨t', x, arms, -, rfl⟩
  · exact prodCmdB_def_target h hdef
  · cases hdef
    exact Or.inl ⟨x, rfl⟩

theorem prodCmdBS_no_assume {A : Program} {mt : List (Option Nat)}
    {Ba : Block} {stride k i : Nat} {c c' : Cmd}
    (hc' : c' ∈ prodCmdBS A mt Ba stride k i c) {φ : BExp}
    (heq : c' = .assume φ) : False := by
  subst heq
  rcases prodCmdBS_cases hc' with h | ⟨t', x, arms, -, habs⟩
  · cases c with
    | assume φ' =>
        simp only [prodCmdB] at h
        rcases List.mem_cons.mp h with h' | h'
        · cases h'
        · rcases List.mem_singleton.mp h' with h'; cases h'
    | assert c'' =>
        simp only [prodCmdB] at h
        rcases List.mem_cons.mp h with h' | h'
        · cases h'
        · rcases List.mem_singleton.mp h' with h'; cases h'
    | havoc t'' x =>
        simp only [prodCmdB] at h
        split at h <;> rcases List.mem_singleton.mp h with h' <;> cases h'
    | assign t'' x e => simp [prodCmdB, Cmd.rename] at h
    | phi t'' x arms' => simp [prodCmdB, Cmd.rename] at h
  · cases habs

/-- Product-block def targets: copies or the block's own CHK window
(width bounded by the matched B-block). -/
theorem prodBlockS_def_target {A B : Program} {mt : List (Option Nat)}
    {stride k : Nat} {Ba : Block}
    {c : Cmd} (hc : c ∈ (prodBlockS A B mt stride k Ba).cmds)
    {t : Ty} {w : Nat} (hdef : c.def? = some (t, w)) :
    (∃ x, w = pv 0 x) ∨ (∃ x, w = pv 1 x)
      ∨ (∃ i kb Bb, matchOf mt k = some kb ∧ B.block? kb = some Bb
          ∧ i ≤ Bb.cmds.length ∧ w = chkReg stride k i) := by
  have hA_case : ∀ {cA : Cmd}, c ∈ prodCmdA cA → (∃ x, w = pv 0 x) := by
    intro cA hcA
    cases cA with
    | assert r => simp [prodCmdA] at hcA
    | assign t' x e =>
        simp only [prodCmdA, List.mem_singleton] at hcA
        subst hcA; cases hdef; exact ⟨x, rfl⟩
    | havoc t' x =>
        simp only [prodCmdA, List.mem_singleton] at hcA
        subst hcA; cases hdef; exact ⟨x, rfl⟩
    | phi t' x arms =>
        simp only [prodCmdA, List.mem_singleton] at hcA
        subst hcA; cases hdef; exact ⟨x, rfl⟩
    | assume φ =>
        simp only [prodCmdA, List.mem_singleton] at hcA
        subst hcA; cases hdef
  cases hm : matchOf mt k with
  | none =>
      rw [prodBlockS_stutter hm] at hc
      obtain ⟨cA, -, hcA⟩ := List.mem_flatMap.mp hc
      exact Or.inl (hA_case hcA)
  | some kb =>
      cases hBb : B.block? kb with
      | none =>
          rw [prodBlockS_unmatched hm hBb] at hc
          obtain ⟨cA, -, hcA⟩ := List.mem_flatMap.mp hc
          exact Or.inl (hA_case hcA)
      | some Bb =>
          rw [prodBlockS_matched hm hBb] at hc
          rcases List.mem_append.mp hc with hc' | hcT
          · rcases List.mem_append.mp hc' with hcA | hcB
            · obtain ⟨cA, -, hcA⟩ := List.mem_flatMap.mp hcA
              exact Or.inl (hA_case hcA)
            · obtain ⟨⟨cB, i⟩, hmem, hcB⟩ := List.mem_flatMap.mp hcB
              have hilen : i < Bb.cmds.length :=
                (List.getElem?_eq_some_iff.mp
                  (List.mem_zipIdx_iff_getElem?.mp hmem)).1
              rcases prodCmdBS_def_target hcB hdef with ⟨x, hx⟩ | hx
              · exact Or.inr (Or.inl ⟨x, hx⟩)
              · exact Or.inr (Or.inr ⟨i, kb, Bb, rfl, hBb, by omega, hx⟩)
          · unfold prodTermChk at hcT
            split at hcT
            · rcases List.mem_cons.mp hcT with rfl | hcT'
              · cases hdef
                exact Or.inr (Or.inr ⟨Bb.cmds.length, kb, Bb, rfl, hBb,
                  Nat.le_refl _, rfl⟩)
              · rcases List.mem_singleton.mp hcT' with rfl
                cases hdef
            · cases hcT

/-- CHK slots of the surgical product are written only inside their
own block's window. -/
theorem productS_chk_defs {A B : Program} {mt : List (Option Nat)}
    {b i : Nat} (hi : i < chkStride B.blocks) {d j : Nat}
    (hd : IsDefAt (productS A B mt)
      (.bool, chkReg (chkStride B.blocks) b i) d j) : d = b := by
  obtain ⟨Bd, c, hBd, hcj, hdef⟩ := hd
  have hdlt : d < A.blocks.length := by
    have := (List.getElem?_eq_some_iff.mp hBd).1
    rwa [productS_length] at this
  have hBa : A.block? d = some A.blocks[d] := List.getElem?_eq_getElem hdlt
  obtain rfl : Bd = prodBlockS A B mt (chkStride B.blocks) d A.blocks[d] :=
    Option.some.inj (hBd.symm.trans (productS_block? hBa))
  rcases prodBlockS_def_target (List.mem_of_getElem? hcj) hdef with
    ⟨x, hx⟩ | ⟨x, hx⟩ | ⟨i', kb, Bb, -, hBb, hi'le, hx⟩
  · unfold chkReg at hx
    exact absurd hx (pv_ne (by omega) (by omega) (by omega) _ _)
  · unfold chkReg at hx
    exact absurd hx (pv_ne (by omega) (by omega) (by omega) _ _)
  · have hi' : i' < chkStride B.blocks :=
      Nat.lt_of_le_of_lt hi'le (lt_chkStride hBb)
    exact ((chkReg_inj hi hi' hx).1).symm

theorem productS_chk_stable {A B : Program} {mt : List (Option Nat)}
    {σ : State} {b i : Nat} (hi : i < chkStride B.blocks)
    (hble : b < A.blocks.length) :
    (denot (productS A B mt) σ).regs .bool (chkReg (chkStride B.blocks) b i)
      = (prefixState (productS A B mt) σ (b + 1)).regs .bool
          (chkReg (chkStride B.blocks) b i) := by
  rw [denot_regs]
  exact prefixState_regs_stable
    (fun d j hd => Nat.lt_succ_of_le (Nat.le_of_eq (productS_chk_defs hi hd)))
    (by rw [productS_length]; omega)

theorem productS_final_blks {A B : Program} {mt : List (Option Nat)}
    {σ : State} {b : Nat} (hblt : b < A.blocks.length) :
    (denot (productS A B mt) σ).blks b
      = (prefixState (productS A B mt) σ (b + 1)).blks b := by
  rw [denot_blks_lt (by rw [productS_length]; omega),
    prefixState_blks_stable (Nat.lt_succ_self b)
      (by rw [productS_length]; omega)]

/-! ## Assume correspondence -/

theorem prodBlockS_assume {A B : Program} {mt : List (Option Nat)}
    {stride k : Nat} {Ba : Block}
    {c : Cmd} (hc : c ∈ (prodBlockS A B mt stride k Ba).cmds)
    {φ : BExp} (heq : c = .assume φ) :
    ∃ ψ : BExp, φ = ψ.rename (pv 0) ∧ .assume ψ ∈ Ba.cmds := by
  subst heq
  have hA_case : ∀ {cA : Cmd}, Cmd.assume φ ∈ prodCmdA cA →
      ∃ ψ : BExp, φ = ψ.rename (pv 0) ∧ .assume ψ ∈ Ba.cmds → True := by
    intro cA _; exact ⟨φ, fun _ => trivial⟩
  cases hm : matchOf mt k with
  | none =>
      rw [prodBlockS_stutter hm] at hc
      obtain ⟨cA, hmemA, hcA⟩ := List.mem_flatMap.mp hc
      cases cA with
      | assume ψ =>
          simp only [prodCmdA, List.mem_singleton, Cmd.rename] at hcA
          exact ⟨ψ, Cmd.assume.inj hcA, hmemA⟩
      | assert r => simp [prodCmdA] at hcA
      | assign t' x e =>
          simp only [prodCmdA, List.mem_singleton, Cmd.rename] at hcA
          cases hcA
      | havoc t' x =>
          simp only [prodCmdA, List.mem_singleton, Cmd.rename] at hcA
          cases hcA
      | phi t' x arms =>
          simp only [prodCmdA, List.mem_singleton, Cmd.rename] at hcA
          cases hcA
  | some kb =>
      cases hBb : B.block? kb with
      | none =>
          rw [prodBlockS_unmatched hm hBb] at hc
          obtain ⟨cA, hmemA, hcA⟩ := List.mem_flatMap.mp hc
          cases cA with
          | assume ψ =>
              simp only [prodCmdA, List.mem_singleton, Cmd.rename] at hcA
              exact ⟨ψ, Cmd.assume.inj hcA, hmemA⟩
          | assert r => simp [prodCmdA] at hcA
          | assign t' x e =>
              simp only [prodCmdA, List.mem_singleton, Cmd.rename] at hcA
              cases hcA
          | havoc t' x =>
              simp only [prodCmdA, List.mem_singleton, Cmd.rename] at hcA
              cases hcA
          | phi t' x arms =>
              simp only [prodCmdA, List.mem_singleton, Cmd.rename] at hcA
              cases hcA
      | some Bb =>
          rw [prodBlockS_matched hm hBb] at hc
          rcases List.mem_append.mp hc with hc' | hcT
          · rcases List.mem_append.mp hc' with hcA | hcB
            · obtain ⟨cA, hmemA, hcA⟩ := List.mem_flatMap.mp hcA
              cases cA with
              | assume ψ =>
                  simp only [prodCmdA, List.mem_singleton, Cmd.rename] at hcA
                  exact ⟨ψ, Cmd.assume.inj hcA, hmemA⟩
              | assert r => simp [prodCmdA] at hcA
              | assign t' x e =>
                  simp only [prodCmdA, List.mem_singleton, Cmd.rename] at hcA
                  cases hcA
              | havoc t' x =>
                  simp only [prodCmdA, List.mem_singleton, Cmd.rename] at hcA
                  cases hcA
              | phi t' x arms =>
                  simp only [prodCmdA, List.mem_singleton, Cmd.rename] at hcA
                  cases hcA
            · obtain ⟨⟨cB, i⟩, -, hcB⟩ := List.mem_flatMap.mp hcB
              exact (prodCmdBS_no_assume hcB rfl).elim
          · exfalso
            unfold prodTermChk at hcT
            split at hcT
            · rcases List.mem_cons.mp hcT with h | h
              · cases h
              · rcases List.mem_singleton.mp h with h; cases h
            · cases hcT

theorem prodBlockS_assume_mem {A B : Program} {mt : List (Option Nat)}
    {stride k : Nat} {Ba : Block}
    {ψ : BExp} (hmem : Cmd.assume ψ ∈ Ba.cmds) :
    Cmd.assume (ψ.rename (pv 0)) ∈ (prodBlockS A B mt stride k Ba).cmds := by
  have hmemA : Cmd.assume (ψ.rename (pv 0)) ∈ Ba.cmds.flatMap prodCmdA :=
    List.mem_flatMap.mpr ⟨.assume ψ, hmem, by simp [prodCmdA, Cmd.rename]⟩
  cases hm : matchOf mt k with
  | none => rw [prodBlockS_stutter hm]; exact hmemA
  | some kb =>
      cases hBb : B.block? kb with
      | none => rw [prodBlockS_unmatched hm hBb]; exact hmemA
      | some Bb =>
          rw [prodBlockS_matched hm hBb]
          exact List.mem_append.mpr (Or.inl (List.mem_append.mpr
            (Or.inl hmemA)))

theorem assumesOK_prodBlockS {A B : Program} {mt : List (Option Nat)}
    (hgf : guardFreeOK A = true)
    {stride b : Nat} {Ba : Block} (hBa : A.block? b = some Ba)
    {R W : State} (hv : ∀ t x, R.regs t (pv 0 x) = W.regs t x) :
    assumesOK R (prodBlockS A B mt stride b Ba) = assumesOK W Ba := by
  have heval : ∀ ψ : BExp, Cmd.assume ψ ∈ Ba.cmds →
      (ψ.rename (pv 0)).eval R = ψ.eval W := by
    intro ψ hmem
    have hgfc := guardFree_at hgf (List.mem_of_getElem? hBa) hmem
    simp only [cmdGuardFree, List.isEmpty_iff] at hgfc
    rw [Exp.eval_rename]
    exact eval_congr ψ (fun q _ => hv q.1 q.2)
      (fun q hq => by rw [hgfc] at hq; cases hq)
  rw [Bool.eq_iff_iff]
  unfold assumesOK
  rw [List.all_eq_true, List.all_eq_true]
  constructor
  · intro h c hc
    cases c with
    | assume ψ =>
        show ψ.eval W = true
        rw [← heval ψ hc]
        exact h _ (prodBlockS_assume_mem hc)
    | assign t x e => trivial
    | havoc t x => trivial
    | phi t x arms => trivial
    | assert r => trivial
  · intro h c hc
    cases c with
    | assume φ =>
        obtain ⟨ψ, rfl, hmemA⟩ := prodBlockS_assume hc rfl
        show (ψ.rename (pv 0)).eval R = true
        rw [heval ψ hmemA]
        exact h _ hmemA
    | assign t x e => trivial
    | havoc t x => trivial
    | phi t x arms => trivial
    | assert r => trivial

/-! ## CHK membership in the matched shape -/

theorem chkS_assume_mem {A B : Program} {mt : List (Option Nat)}
    {stride k kb i : Nat} {Ba Bb : Block} (hm : matchOf mt k = some kb)
    (hBb : B.block? kb = some Bb)
    {φ : BExp} (hi : Bb.cmds[i]? = some (.assume φ)) :
    Cmd.assert (chkReg stride k i)
      ∈ (prodBlockS A B mt stride k Ba).cmds := by
  rw [prodBlockS_matched hm hBb]
  refine List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr
    (List.mem_flatMap.mpr ⟨(Cmd.assume φ, i),
      List.mem_zipIdx_iff_getElem?.mpr hi, ?_⟩))))
  simp [prodCmdBS, prodCmdB]

theorem chkS_assert_mem {A B : Program} {mt : List (Option Nat)}
    {stride k kb i : Nat} {Ba Bb : Block} (hm : matchOf mt k = some kb)
    (hBb : B.block? kb = some Bb)
    {c' : Nat} (hi : Bb.cmds[i]? = some (.assert c')) :
    Cmd.assert (chkReg stride k i)
      ∈ (prodBlockS A B mt stride k Ba).cmds := by
  rw [prodBlockS_matched hm hBb]
  refine List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr
    (List.mem_flatMap.mpr ⟨(Cmd.assert c', i),
      List.mem_zipIdx_iff_getElem?.mpr hi, ?_⟩))))
  cases hreg : Ba.assertReg? <;> simp [prodCmdBS, prodCmdB, hreg]

theorem chkS_branch_mem {A B : Program} {mt : List (Option Nat)}
    {stride k kb : Nat} {Ba Bb : Block} (hm : matchOf mt k = some kb)
    (hBb : B.block? kb = some Bb)
    {cA tA eA cB tB eB : Nat} (hta : Ba.term = .ifGoto cA tA eA)
    (htb : Bb.term = .ifGoto cB tB eB) :
    Cmd.assert (chkReg stride k Bb.cmds.length)
      ∈ (prodBlockS A B mt stride k Ba).cmds := by
  rw [prodBlockS_matched hm hBb]
  refine List.mem_append.mpr (Or.inr ?_)
  unfold prodTermChk
  rw [hta, htb]
  simp

/-! ## Cross-CFG dominance via the projected active path

Lockstep's `domTable A = domTable B` is lost under surgery. The
replacement: `A`'s active path projects (through the matching) onto a
*structural* path in `B`'s CFG — edge existence needs no condition
values, only the chase correspondence — and `B`'s dominance-closure
facts walk along it. -/

/-- Edge existence, conditions ignored. -/
def EdgeIn (P : Program) (u v : Nat) : Prop :=
  ∃ cond, (u, v, cond) ∈ Vc.allEdges P

theorem EdgeIn.lt {P : Program} (hfwd : forwardOK P = true) {u v : Nat}
    (h : EdgeIn P u v) : u < v := by
  obtain ⟨cond, hmem⟩ := h
  obtain ⟨Bu, hBu, hout⟩ := mem_allEdges_elim hmem
  exact (forward_target hfwd hBu (outEdges_shape hout).2).1

theorem edgeIn_of_target {P : Program} {b tb : Nat} {Bb : Block}
    (hBb : P.block? b = some Bb) (ht : tb ∈ termTargets Bb.term) :
    EdgeIn P b tb := by
  cases hT : Bb.term with
  | halt => rw [hT] at ht; cases ht
  | goto t =>
      rw [hT] at ht
      obtain rfl : tb = t := List.mem_singleton.mp ht
      exact ⟨.litB true, mem_allEdges_intro hBb (by
        simp [Vc.outEdges, hT])⟩
  | ifGoto c t e =>
      rw [hT] at ht
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact ⟨.var .bool c, mem_allEdges_intro hBb (by
          simp [Vc.outEdges, hT])⟩
      · obtain rfl : tb = e := List.mem_singleton.mp ht'
        exact ⟨.un .not (.var .bool c), mem_allEdges_intro hBb (by
          simp [Vc.outEdges, hT])⟩

/-- `dom_visited` over structural edges: the proof of the taken-edge
version only consumes edge membership. -/
theorem dom_in_visited_from {P : Program} (hdc : domClosedOK P = true)
    {W : List Nat} :
    ∀ {V : List Nat}, Chained (EdgeIn P) V →
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
            obtain ⟨cond, hedge⟩ := hExy
            have hyne : y ≠ P.entry := hne y (List.mem_cons_self ..)
            rcases domClosed_edge hdc hedge hyne d hd with rfl | hda
            · exact hsub d (List.mem_cons_of_mem _ (List.mem_cons_self ..))
            · exact hhead x rfl d hda

theorem dom_in_visited {P : Program} (hdc : domClosedOK P = true)
    (hfwd : forwardOK P = true) {V : List Nat}
    (hedge : Chained (EdgeIn P) V) (hhead : V.head? = some P.entry) :
    ∀ u ∈ V, ∀ d ∈ domOf P u, d ∈ V := by
  have hlt : Chained (· < ·) V := hedge.imp fun a b h => h.lt hfwd
  have hentry_mem : P.entry ∈ V := by
    cases V with
    | nil => cases hhead
    | cons v V' =>
        obtain rfl := Option.some.inj hhead
        exact List.mem_cons_self ..
  refine dom_in_visited_from hdc hedge (fun v hv => hv) ?_ ?_
  · intro h hh d hd
    obtain rfl := Option.some.inj (hhead.symm.trans hh)
    obtain rfl := domClosed_entry hdc d hd
    exact hentry_mem
  · intro v hv
    have := chained_lt_tail hlt hhead v hv
    omega

/-! ## The projection -/

/-- The first matched block a taken-edge walk reaches is where the
chase lands. -/
theorem chase_first_matched {A B : Program} {mt : List (Option Nat)}
    {s0 : State} (hwfA : WellFormed A) (hs : surgeryOK A B mt = true) :
    ∀ (V : List Nat) (w : Nat),
      Chained (EdgeTaken A (denot A s0)) (w :: V) →
      (∀ v ∈ w :: V, v < A.blocks.length) →
      ∀ b₂, ((w :: V).filterMap (matchOf mt)).head? = some b₂ →
        ∃ m₂, matchOf mt m₂ = some b₂ ∧ chase A mt w = some m₂
  | V, w, hch, hlt, b₂, hhead => by
      have hwlt : w < A.blocks.length := hlt w (List.mem_cons_self ..)
      cases hw : matchOf mt w with
      | some bw =>
          rw [List.filterMap_cons] at hhead
          rw [hw] at hhead
          simp only [List.head?_cons] at hhead
          obtain rfl : bw = b₂ := Option.some.inj hhead
          exact ⟨w, hw, chase_matched (by omega) (by rw [hw]; simp)⟩
      | none =>
          rw [List.filterMap_cons, hw] at hhead
          cases V with
          | nil => simp at hhead
          | cons v₁ V'' =>
              obtain ⟨hE, hch'⟩ := chained_destruct hch
              have hBw : A.block? w = some A.blocks[w] :=
                List.getElem?_eq_getElem hwlt
              have hstut := (surgery_block hs hBw).1 hw
              unfold stutterBlockOK at hstut
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hstut
              obtain ⟨tw, htw⟩ : ∃ tw, (A.blocks[w]).term = .goto tw := by
                cases h' : (A.blocks[w]).term with
                | goto t => exact ⟨t, rfl⟩
                | halt => rw [h'] at hstut; simp at hstut
                | ifGoto c th el => rw [h'] at hstut; simp at hstut
              obtain rfl : tw = v₁ := by
                obtain ⟨Bw', hBw', hshape⟩ := hE
                obtain rfl : A.blocks[w] = Bw' :=
                  Option.some.inj (hBw.symm.trans hBw')
                rcases hshape with hgoto | ⟨c, th, el, hif, -⟩
                · rw [htw] at hgoto
                  exact Terminator.goto.inj hgoto
                · rw [htw] at hif
                  cases hif
              obtain ⟨m₂, hm₂, hchase⟩ := chase_first_matched hwfA hs
                V'' tw hch'
                (fun v hv => hlt v (List.mem_cons_of_mem _ hv)) b₂ hhead
              exact ⟨m₂, hm₂, by
                rw [chase_stutter_step hwfA.fwd (surgery_len hs) hw hBw htw]
                exact hchase⟩

/-- The taken-edge chain's matched projection is a structural path in
`B`'s CFG. -/
theorem proj_chained {A B : Program} {mt : List (Option Nat)}
    {s0 : State} (hwfA : WellFormed A) (hs : surgeryOK A B mt = true) :
    ∀ (V : List Nat),
      Chained (EdgeTaken A (denot A s0)) V →
      (∀ v ∈ V, v < A.blocks.length) →
      Chained (EdgeIn B) (V.filterMap (matchOf mt))
  | [], _, _ => trivial
  | [v], _, _ => by
      rw [List.filterMap_cons]
      cases matchOf mt v <;> simp [Chained]
  | v :: w :: V', hch, hlt => by
      obtain ⟨hE, hch'⟩ := chained_destruct hch
      have htail := proj_chained hwfA hs (w :: V') hch'
        (fun x hx => hlt x (List.mem_cons_of_mem _ hx))
      rw [List.filterMap_cons]
      cases hv : matchOf mt v with
      | none => exact htail
      | some b =>
          cases hproj : ((w :: V').filterMap (matchOf mt)) with
          | nil =>
              show Chained (EdgeIn B) [b]
              trivial
          | cons b₂ rest =>
              rw [hproj] at htail
              show Chained (EdgeIn B) (b :: b₂ :: rest)
              refine ⟨?_, htail⟩
              -- the structural B-edge from b to b₂ via the chase
              obtain ⟨m₂, hm₂, hchase⟩ := chase_first_matched hwfA hs
                V' w hch'
                (fun x hx => hlt x (List.mem_cons_of_mem _ hx)) b₂
                (by rw [hproj]; rfl)
              have hvlt : v < A.blocks.length := hlt v (List.mem_cons_self ..)
              have hBv : A.block? v = some A.blocks[v] :=
                List.getElem?_eq_getElem hvlt
              obtain ⟨Bb, hBb, hterm, -⟩ := (surgery_block hs hBv).2 b hv
              obtain ⟨Bv', hBv', hshape⟩ := hE
              obtain rfl : A.blocks[v] = Bv' :=
                Option.some.inj (hBv.symm.trans hBv')
              -- identify B's arm target for the taken A-arm
              have hchaseT : ∀ tb : Nat, chaseTargetOK A B mt w tb = true →
                  b₂ = tb := by
                intro tb h1
                unfold chaseTargetOK at h1
                rw [hchase] at h1
                have h2 : (matchOf mt m₂ == some tb
                    && decide (tb < B.blocks.length)) = true := h1
                rw [Bool.and_eq_true] at h2
                have htb : matchOf mt m₂ = some tb := beq_iff_eq.mp h2.1
                rw [hm₂] at htb
                exact Option.some.inj htb
              rcases hshape with hgoto | ⟨c, th, el, hif, harm⟩
              · -- goto/goto
                unfold termSurgeryOK at hterm
                rw [hgoto] at hterm
                cases hTb : Bb.term with
                | halt => rw [hTb] at hterm; cases hterm
                | ifGoto cb tb eb => rw [hTb] at hterm; cases hterm
                | goto tb =>
                    rw [hTb] at hterm
                    have hterm' : chaseTargetOK A B mt w tb = true := hterm
                    obtain rfl : b₂ = tb := hchaseT tb hterm'
                    exact edgeIn_of_target hBb (by rw [hTb]; simp [termTargets])
              · -- ifGoto/ifGoto, arm by arm
                unfold termSurgeryOK at hterm
                rw [hif] at hterm
                cases hTb : Bb.term with
                | halt => rw [hTb] at hterm; cases hterm
                | goto tb => rw [hTb] at hterm; cases hterm
                | ifGoto cb tb eb =>
                    rw [hTb] at hterm
                    have hterm' : (chaseTargetOK A B mt th tb
                        && chaseTargetOK A B mt el eb) = true := hterm
                    rw [Bool.and_eq_true] at hterm'
                    rcases harm with ⟨rfl, -⟩ | ⟨rfl, -⟩
                    · obtain rfl : b₂ = tb := hchaseT tb hterm'.1
                      exact edgeIn_of_target hBb
                        (by rw [hTb]; simp [termTargets])
                    · obtain rfl : b₂ = eb := hchaseT eb hterm'.2
                      exact edgeIn_of_target hBb
                        (by rw [hTb]; simp [termTargets])

/-- The payoff: `B`-dominators of an active matched block are matches
of active `A`-blocks. -/
theorem good_of_domB {A B : Program} {mt : List (Option Nat)} {s0 : State}
    (hwfA : WellFormed A) (hwfB : WellFormed B)
    (hs : surgeryOK A B mt = true) (hdcB : domClosedOK B = true)
    {k kb : Nat} (hm : matchOf mt k = some kb)
    (hkact : (denot A s0).blks k = true) (hklt : k < A.blocks.length)
    {d : Nat} (hd : d ∈ domOf B kb) :
    ∃ a, matchOf mt a = some d ∧ (denot A s0).blks a = true := by
  have hkV : k ∈ activeList A s0 := mem_activeList.mpr ⟨hklt, hkact⟩
  have hlts : ∀ v ∈ activeList A s0, v < A.blocks.length :=
    fun v hv => (mem_activeList.mp hv).1
  have hchain := proj_chained (s0 := s0) hwfA hs (activeList A s0)
    (denot_hedge hwfA) hlts
  obtain ⟨hentryV, hheadV⟩ := denot_hentry hwfA.fwd hwfA.uses hkV
  have hhead : ((activeList A s0).filterMap (matchOf mt)).head?
      = some B.entry := by
    cases hV : activeList A s0 with
    | nil => rw [hV] at hheadV; cases hheadV
    | cons v rest =>
        rw [hV] at hheadV
        obtain rfl : v = A.entry := Option.some.inj hheadV
        rw [List.filterMap_cons, surgery_entry hs]
        rfl
  have hkbV : kb ∈ (activeList A s0).filterMap (matchOf mt) :=
    List.mem_filterMap.mpr ⟨k, hkV, hm⟩
  have hdV := dom_in_visited hdcB hwfB.fwd hchain hhead kb hkbV d hd
  obtain ⟨a, haV, ha⟩ := List.mem_filterMap.mp hdV
  exact ⟨a, ha, (mem_activeList.mp haV).2⟩

/-! ## Goodness under surgery -/

def GoodBS (A B : Program) (mt : List (Option Nat)) (s0 : State)
    (t : Ty) (x : Nat) : Prop :=
  ∀ d j, IsDefAt B (t, x) d j →
    (∃ a, matchOf mt a = some d ∧ (denot A s0).blks a = true)
    ∨ ∃ Bd, B.block? d = some Bd ∧ Bd.cmds[j]? = some (Cmd.havoc t x)

def HalfBS (A B : Program) (mt : List (Option Nat)) (s0 : State)
    (R : State) : Prop :=
  ∀ (t : Ty) (x : Nat), GoodBS A B mt s0 t x →
    R.regs t (pv 1 x) = (denot B s0).regs t x

theorem goodS_of_use {A B : Program} {mt : List (Option Nat)} {s0 : State}
    (hwfA : WellFormed A) (hwfB : WellFormed B)
    (hs : surgeryOK A B mt = true) (hdcB : domClosedOK B = true)
    {k kb i : Nat} (hm : matchOf mt k = some kb)
    (hkact : (denot A s0).blks k = true) (hklt : k < A.blocks.length)
    {t : Ty} {x : Nat}
    (hu : useOK (domTable B) (defPositions B (t, x)) kb i = true) :
    GoodBS A B mt s0 t x := by
  intro d j hd
  left
  rcases useOK_dom hu d j hd with rfl | hdom
  · exact ⟨k, hm, hkact⟩
  · exact good_of_domB hwfA hwfB hs hdcB hm hkact hklt hdom

theorem goodS_of_arm {A B : Program} {mt : List (Option Nat)} {s0 : State}
    (hwfA : WellFormed A) (hwfB : WellFormed B)
    (hs : surgeryOK A B mt = true) (hdcB : domClosedOK B = true)
    {o ob : Nat} (hm : matchOf mt o = some ob)
    (hoact : (denot A s0).blks o = true) (holt : o < A.blocks.length)
    {t : Ty} {x : Nat}
    (hu : armUseOK (domTable B) (defPositions B (t, x)) ob = true) :
    GoodBS A B mt s0 t x := by
  intro d j hd
  left
  exact good_of_domB hwfA hwfB hs hdcB hm hoact holt (armUseOK_dom hu d j hd)

/-! ## Step-lemma helpers -/

theorem lookupArm_map_self (f : Nat → Nat) :
    ∀ {l : List Nat} {p : Nat}, p ∈ l →
      lookupArm (l.map fun q => (q, f q)) p = some (f p)
  | [], p, hp => absurd hp List.not_mem_nil
  | q :: l, p, hp => by
      cases hb : (p == q) with
      | true =>
          obtain rfl : p = q := beq_iff_eq.mp hb
          simp only [lookupArm, List.map_cons, List.lookup, hb]
      | false =>
          have hpq : p ≠ q := fun h => by rw [h] at hb; simp at hb
          simp only [lookupArm, List.map_cons, List.lookup, hb]
          have hp' : p ∈ l := by
            rcases List.mem_cons.mp hp with h | h
            · exact absurd h hpq
            · exact h
          exact lookupArm_map_self f hp' 

theorem ownerGo_le {A : Program} {mt : List (Option Nat)}
    (hfwd : forwardOK A = true) :
    ∀ (f a : Nat), ownerGo A mt f a ≤ a := by
  intro f
  induction f with
  | zero => intro a; exact Nat.le_refl a
  | succ g ih =>
      intro a
      unfold ownerGo
      by_cases hm : (matchOf mt a).isSome
      · rw [if_pos hm]
      · rw [if_neg hm]
        cases ha : predsOf A a with
        | nil => exact Nat.le_refl a
        | cons q rest =>
            cases rest with
            | nil =>
                have hqlt : q < a := pred_lt hfwd (by
                  rw [ha]; exact List.mem_cons_self ..)
                exact Nat.le_trans (ih q) (by omega)
            | cons q' rest' => exact Nat.le_refl a

theorem owner_le {A : Program} {mt : List (Option Nat)}
    (hfwd : forwardOK A = true) (a : Nat) : owner A mt a ≤ a :=
  ownerGo_le hfwd a a

/-! ## The A-copy fold over the surgical product (identity) -/

theorem prodCmdA_foldS {A B : Program} {mt : List (Option Nat)}
    {s0 : State} (hwfA : WellFormed A)
    {b : Nat} {Ba : Block} (hBa : A.block? b = some Ba) :
    ∀ (l : List Cmd), (∀ c ∈ l, c ∈ Ba.cmds) →
      ∀ (R : State), HalfA A s0 R →
        (∀ p, p < b → R.blks p = (denot A s0).blks p) →
        (l.flatMap prodCmdA).foldl (denotCmd (productS A B mt)) R = R
  | [], _, R, _, _ => rfl
  | c :: l, hsub, R, hA, hblks => by
      have hcmem : c ∈ Ba.cmds := hsub _ (List.mem_cons_self ..)
      rw [List.flatMap_cons, List.foldl_append]
      have hstep : (prodCmdA c).foldl (denotCmd (productS A B mt)) R = R := by
        cases c with
        | assert r => rfl
        | assume φ => rfl
        | havoc t x => rfl
        | assign t x e =>
            show denotCmd (productS A B mt) R
              (.assign t (pv 0 x) (e.rename (pv 0))) = R
            obtain ⟨i, hci⟩ := List.mem_iff_getElem?.mp hcmem
            have hgfc := guardFree_at hwfA.gf (List.mem_of_getElem? hBa) hcmem
            simp only [cmdGuardFree, List.isEmpty_iff] at hgfc
            have hv : (e.rename (pv 0)).eval R = R.regs t (pv 0 x) :=
              calc (e.rename (pv 0)).eval R
                  = e.eval (R.reindex (pv 0)) := Exp.eval_rename ..
                _ = e.eval (denot A s0) :=
                    eval_congr e (fun p _ => hA p.1 p.2)
                      (fun q hq => by rw [hgfc] at hq; cases hq)
                _ = (denot A s0).regs t x := (denot_assign hwfA hBa hci).symm
                _ = R.regs t (pv 0 x) := (hA t x).symm
            show R.upd t (pv 0 x) ((e.rename (pv 0)).eval R) = R
            rw [hv, State.upd_self]
        | phi t x arms =>
            show denotCmd (productS A B mt) R
              (.phi t (pv 0 x) (arms.map fun a => (a.1, pv 0 a.2))) = R
            have harms := phiOK_at hwfA.phi hBa hcmem
            cases arms with
            | nil => simp [phiArmsOK] at harms
            | cons a rest =>
                have hv : (Vc.phiRhs (productS A B mt) t
                    ((a :: rest).map fun ar => (ar.1, pv 0 ar.2))).eval R
                    = R.regs t (pv 0 x) :=
                  calc (Vc.phiRhs (productS A B mt) t
                        ((a :: rest).map fun ar => (ar.1, pv 0 ar.2))).eval R
                      = (Vc.phiChain (productS A B mt) t (a.1, pv 0 a.2)
                          (rest.map fun ar => (ar.1, pv 0 ar.2))).eval R := by
                        rw [List.map_cons]
                        rfl
                    _ = (Vc.phiChain A t a rest).eval (R.reindex (pv 0)) :=
                        phiChain_rename_eval (P := A) (Q := productS A B mt)
                          rfl (pv 0) R a rest
                    _ = (Vc.phiRhs A t (a :: rest)).eval (R.reindex (pv 0)) :=
                        rfl
                    _ = (Vc.phiRhs A t (a :: rest)).eval (denot A s0) :=
                        eval_congr _ (fun p _ => hA p.1 p.2)
                          (fun q hq => by
                            obtain ⟨s', hqs⟩ := phiRhs_blkVars q hq
                            exact hblks q (phiArm_lt harms hqs))
                    _ = (denot A s0).regs t x :=
                        (denot_phi hwfA hBa hcmem).symm
                    _ = R.regs t (pv 0 x) := (hA t x).symm
                show R.upd t (pv 0 x) _ = R
                rw [hv, State.upd_self]
      rw [hstep]
      exact prodCmdA_foldS hwfA hBa l
        (fun c' hc' => hsub c' (List.mem_cons_of_mem _ hc')) R hA hblks

theorem not_goodBS_of_inactive_def {A B : Program} {mt : List (Option Nat)}
    {s0 : State} (hs : surgeryOK A B mt = true)
    {k kb i : Nat} {Bb : Block} {c : Cmd}
    (hm : matchOf mt k = some kb) (hBb : B.block? kb = some Bb)
    (hci : Bb.cmds[i]? = some c)
    {t : Ty} {x : Nat} (hdef : c.def? = some (t, x))
    (hnothavoc : c ≠ .havoc t x)
    (hinactive : (denot A s0).blks k = false) :
    ¬GoodBS A B mt s0 t x := by
  intro hg
  rcases hg kb i ⟨Bb, c, hBb, hci, hdef⟩ with ⟨a, ha, haact⟩ | ⟨Bd, hBd, hcj⟩
  · obtain rfl : a = k := matchOf_inj hs (surgery_len hs) ha hm
    rw [hinactive] at haact
    cases haact
  · obtain rfl : Bb = Bd := Option.some.inj (hBb.symm.trans hBd)
    exact hnothavoc (Option.some.inj (hci.symm.trans hcj))

/-- One B-side command's emission at a matched block: invariants
preserved, the deposit made; the routed phi is a self-write via the
ownership resolution. -/
theorem prodCmdBS_step {A B : Program} {mt : List (Option Nat)} {s0 : State}
    (hwfA : WellFormed A) (hwfB : WellFormed B)
    (hdcB : domClosedOK B = true) (hs : surgeryOK A B mt = true)
    {k kb : Nat} {Ba Bb : Block}
    (hBa : A.block? k = some Ba) (hBb : B.block? kb = some Bb)
    (hm : matchOf mt k = some kb)
    (hxfer : ∀ a b', a < k → matchOf mt a = some b' →
      (denot A s0).blks a = true → (denot B s0).blks b' = true)
    {c : Cmd} {i : Nat} (hci : Bb.cmds[i]? = some c)
    {R : State} (hA : HalfA A s0 R) (hB : HalfBS A B mt s0 R)
    (hblks : ∀ p, p < k → R.blks p = (denot A s0).blks p) :
    ∀ R', R' = (prodCmdBS A mt Ba (chkStride B.blocks) k i c).foldl
        (denotCmd (productS A B mt)) R →
      HalfA A s0 R' ∧ HalfBS A B mt s0 R' ∧ R'.blks = R.blks
        ∧ DepositAt A B s0 Ba (chkStride B.blocks) k R' (c, i) := by
  intro R' hR'
  have hklt : k < A.blocks.length := (List.getElem?_eq_some_iff.mp hBa).1
  have hkblt : kb < B.blocks.length := (List.getElem?_eq_some_iff.mp hBb).1
  have hcmem : c ∈ Bb.cmds := List.mem_of_getElem? hci
  have husec := usesOK_cmd hwfB.uses hBb hci
  cases c with
  | assume φ =>
      simp only [prodCmdBS, prodCmdB] at hR'
      have hR'' : R' = R.upd .bool (chkReg (chkStride B.blocks) k i)
          ((φ.rename (pv 1)).eval R) := hR'
      subst hR''
      refine ⟨fun t x => ?_, fun t x hg => ?_, rfl, fun hactive => ?_⟩
      · rw [State.upd_regs_of_ne R
          (pv_chk_pair_ne (j := 0) (by omega) (by omega) x _ _ _)]
        exact hA t x
      · rw [State.upd_regs_of_ne R
          (pv_chk_pair_ne (j := 1) (by omega) (by omega) x _ _ _)]
        exact hB t x hg
      · show (R.upd .bool _ _).regs .bool _ = _
        rw [State.upd_regs_self]
        simp only [cmdUsesOK] at husec
        have hgfc := guardFree_at hwfB.gf (List.mem_of_getElem? hBb) hcmem
        simp only [cmdGuardFree, List.isEmpty_iff] at hgfc
        rw [Exp.eval_rename]
        exact eval_congr φ
          (fun p hp => hB p.1 p.2 (goodS_of_use hwfA hwfB hs hdcB hm hactive
            hklt (List.all_eq_true.mp husec p hp)))
          (fun q hq => by rw [hgfc] at hq; cases hq)
  | assert cB' =>
      simp only [prodCmdBS, prodCmdB] at hR'
      cases hreg : Ba.assertReg? with
      | none =>
          rw [hreg] at hR'
          have hR'' : R' = R.upd .bool (chkReg (chkStride B.blocks) k i)
              ((Exp.var .bool (pv 1 cB')).eval R) := hR'
          subst hR''
          refine ⟨fun t x => ?_, fun t x hg => ?_, rfl, fun _ cA hcA => ?_⟩
          · rw [State.upd_regs_of_ne R
              (pv_chk_pair_ne (j := 0) (by omega) (by omega) x _ _ _)]
            exact hA t x
          · rw [State.upd_regs_of_ne R
              (pv_chk_pair_ne (j := 1) (by omega) (by omega) x _ _ _)]
            exact hB t x hg
          · rw [hreg] at hcA
            cases hcA
      | some cA =>
          rw [hreg] at hR'
          have hR'' : R' = R.upd .bool (chkReg (chkStride B.blocks) k i)
              ((Exp.eqB (.var .bool (pv 0 cA)) (.var .bool (pv 1 cB'))).eval R)
            := hR'
          subst hR''
          refine ⟨fun t x => ?_, fun t x hg => ?_, rfl,
            fun hactive cA' hcA' => ?_⟩
          · rw [State.upd_regs_of_ne R
              (pv_chk_pair_ne (j := 0) (by omega) (by omega) x _ _ _)]
            exact hA t x
          · rw [State.upd_regs_of_ne R
              (pv_chk_pair_ne (j := 1) (by omega) (by omega) x _ _ _)]
            exact hB t x hg
          · obtain rfl : cA = cA' := Option.some.inj (hreg.symm.trans hcA')
            show (R.upd .bool _ _).regs .bool _ = _
            rw [State.upd_regs_self]
            show (R.regs .bool (pv 0 cA) == R.regs .bool (pv 1 cB')) = _
            simp only [cmdUsesOK] at husec
            rw [hA .bool cA, hB .bool cB'
              (goodS_of_use hwfA hwfB hs hdcB hm hactive hklt husec)]
  | havoc t' x =>
      simp only [prodCmdBS, prodCmdB] at hR'
      split at hR'
      · rename_i hhav
        have hgood : GoodBS A B mt s0 t' x := fun d j hd => by
          right
          obtain ⟨rfl, rfl⟩ := ssa_unique hwfB.ssa ⟨Bb, _, hBb, hci, rfl⟩ hd
          exact ⟨Bb, hBb, hci⟩
        obtain ⟨dA, BdA, jA, hBdA, hcjA⟩ := hasHavoc_exists hhav
        have hval : R.regs t' (pv 0 x) = (denot B s0).regs t' x := by
          rw [hA t' x, denot_regs_of_havoc_def hwfA.ssa hBdA hcjA,
            ← denot_regs_of_havoc_def hwfB.ssa hBb hci]
        have hR'' : R' = R.upd t' (pv 1 x) (R.regs t' (pv 0 x)) := hR'
        subst hR''
        rw [hval, ← hB t' x hgood, State.upd_self]
        exact ⟨hA, hB, rfl, trivial⟩
      · have hR'' : R' = R := hR'
        subst hR''
        exact ⟨hA, hB, rfl, trivial⟩
  | assign t' x e =>
      simp only [prodCmdBS, prodCmdB, Cmd.rename] at hR'
      have hR'' : R' = R.upd t' (pv 1 x) ((e.rename (pv 1)).eval R) := hR'
      subst hR''
      rcases Bool.eq_false_or_eq_true ((denot A s0).blks k) with hactive | hinact
      · have hgood : GoodBS A B mt s0 t' x := fun d j hd => by
          left
          obtain ⟨rfl, rfl⟩ := ssa_unique hwfB.ssa ⟨Bb, _, hBb, hci, rfl⟩ hd
          exact ⟨k, hm, hactive⟩
        simp only [cmdUsesOK] at husec
        have hgfc := guardFree_at hwfB.gf (List.mem_of_getElem? hBb) hcmem
        simp only [cmdGuardFree, List.isEmpty_iff] at hgfc
        have hval : (e.rename (pv 1)).eval R = R.regs t' (pv 1 x) := by
          rw [Exp.eval_rename,
            eval_congr e (fun p hp => hB p.1 p.2
              (goodS_of_use hwfA hwfB hs hdcB hm hactive hklt
                (List.all_eq_true.mp husec p hp)))
              (fun q hq => by rw [hgfc] at hq; cases hq),
            ← denot_assign hwfB hBb hci, ← hB t' x hgood]
        rw [hval, State.upd_self]
        exact ⟨hA, hB, rfl, trivial⟩
      · have hng := not_goodBS_of_inactive_def hs hm hBb hci rfl
          (by intro h; cases h) hinact
        refine ⟨fun t x' => ?_, fun t x' hg => ?_, rfl, trivial⟩
        · rw [State.upd_regs_of_ne R
            (pv_pair_ne (j := 0) (j' := 1) (by omega) (by omega)
              (by omega) x' x)]
          exact hA t x'
        · have hne : ((t, pv 1 x') : Ty × Nat) ≠ (t', pv 1 x) := by
            intro heq
            obtain ⟨rfl, hx⟩ := Prod.mk.injEq .. |>.mp heq
            obtain rfl : x' = x := ((pv_eq_iff (by omega) (by omega)).mp hx).2
            exact hng hg
          rw [State.upd_regs_of_ne R hne]
          exact hB t x' hg
  | phi t' x arms =>
      simp only [prodCmdBS] at hR'
      have hR'' : R' = R.upd t' (pv 1 x)
          ((Vc.phiRhs (productS A B mt) t'
            ((predsOf A k).map fun p =>
              (p, pv 1 ((lookupArm arms
                ((matchOf mt (owner A mt p)).getD 0)).getD 0)))).eval R)
          := hR'
      subst hR''
      rcases Bool.eq_false_or_eq_true ((denot A s0).blks k) with hactive | hinact
      · -- A-active: routed selection
        have hgood : GoodBS A B mt s0 t' x := fun d j hd => by
          left
          obtain ⟨rfl, rfl⟩ := ssa_unique hwfB.ssa ⟨Bb, _, hBb, hci, rfl⟩ hd
          exact ⟨k, hm, hactive⟩
        have harmsB := phiOK_at hwfB.phi hBb hcmem
        have hkne : k ≠ A.entry := by
          intro heq
          have hkb : kb = B.entry := by
            have := surgery_entry hs
            rw [← heq] at this
            exact Option.some.inj (hm.symm.trans this)
          exact no_phi_in_entry hwfB.phi hwfB.entry
            (by rw [← hkb]; exact hBb) hcmem
        obtain ⟨pstar, hpact, hplt, hpE⟩ :=
          denot_active_pred hwfA.fwd hwfA.uses hBa hactive hkne
        have hpA : pstar ∈ activeList A s0 :=
          mem_activeList.mpr ⟨by omega, hpact⟩
        have hppredA : pstar ∈ predsOf A k := by
          obtain ⟨cond, hcm, -⟩ := hpE.edge_cond
          exact mem_predsOf.mpr ⟨cond, hcm⟩
        -- the owner and its match
        obtain ⟨o, ho_eq, hosome, hoact, hole⟩ :
            ∃ o, owner A mt pstar = o ∧ (matchOf mt o).isSome
              ∧ (denot A s0).blks o = true ∧ o ≤ pstar := by
          by_cases hpm : (matchOf mt pstar).isSome
          · exact ⟨pstar, owner_matched hpm, hpm, hpact, Nat.le_refl _⟩
          · have hpmn : matchOf mt pstar = none := by
              cases h : matchOf mt pstar with
              | none => rfl
              | some b => rw [h] at hpm; simp at hpm
            obtain ⟨h1, h2, -⟩ := stutter_origin hwfA hs pstar hpmn hpact
              (by omega)
            exact ⟨owner A mt pstar, rfl, h1, h2, owner_le hwfA.fwd pstar⟩
        obtain ⟨ob, hob⟩ := Option.isSome_iff_exists.mp hosome
        -- the routing check provides the arm
        obtain ⟨Bb', hBb', -, hroute⟩ := (surgery_block hs hBa).2 kb hm
        obtain rfl : Bb = Bb' := Option.some.inj (hBb.symm.trans hBb')
        have hroute' := List.all_eq_true.mp
          (List.all_eq_true.mp hroute _ hcmem) pstar hppredA
        rw [ho_eq, hob] at hroute'
        have hroute'' : (lookupArm arms ob).isSome = true := hroute'
        obtain ⟨src, hsrc⟩ := Option.isSome_iff_exists.mp hroute'' 
        have hsrcmem : (ob, src) ∈ arms := lookup_mem hsrc
        have hobpredB : ob ∈ predsOf B kb := phiArm_pred harmsB hsrcmem
        -- product-side value: the routed phi selects pstar's arm
        have hval : (Vc.phiRhs (productS A B mt) t'
            ((predsOf A k).map fun p =>
              (p, pv 1 ((lookupArm arms
                ((matchOf mt (owner A mt p)).getD 0)).getD 0)))).eval R
            = R.regs t' (pv 1 src) := by
          have hlk : lookupArm ((predsOf A k).map fun p =>
              (p, pv 1 ((lookupArm arms
                ((matchOf mt (owner A mt p)).getD 0)).getD 0))) pstar
              = some (pv 1 ((lookupArm arms
                ((matchOf mt (owner A mt pstar)).getD 0)).getD 0)) :=
            lookupArm_map_self _ hppredA
          rw [ho_eq, hob] at hlk
          simp only [Option.getD_some, hsrc] at hlk
          cases hpreds : predsOf A k with
          | nil => rw [hpreds] at hppredA; cases hppredA
          | cons p0 prest =>
              rw [List.map_cons]
              rw [hpreds, List.map_cons] at hlk
              refine phiChain_eval_select (p := pstar) (src := pv 1 src)
                _ _ hlk ?_ ?_
              · unfold Vc.guardOf
                rw [productS_entry]
                split
                · rfl
                · show R.blks pstar = true
                  rw [hblks pstar (by omega)]
                  exact hpact
              · intro q s' hqarm hqne
                have hqpred : q ∈ predsOf A k := by
                  have : (q, s') ∈ (predsOf A k).map fun p =>
                      (p, pv 1 ((lookupArm arms
                        ((matchOf mt (owner A mt p)).getD 0)).getD 0)) := by
                    rw [hpreds, List.map_cons]
                    exact hqarm
                  obtain ⟨p', hp'mem, hp'eq⟩ := List.mem_map.mp this
                  obtain rfl : p' = q := congrArg Prod.fst hp'eq
                  exact hp'mem
                have hqlt : q < k := pred_lt hwfA.fwd hqpred
                unfold Vc.guardOf
                rw [productS_entry]
                rw [if_neg (by
                  intro hqe
                  obtain ⟨hentA, -⟩ := denot_hentry hwfA.fwd hwfA.uses hpA
                  exact hqne (active_pred_unique hwfA hklt hpA hppredA
                    (by rw [hqe]; exact hentA) hqpred))]
                show R.blks q = false
                rw [hblks q hqlt]
                rcases Bool.eq_false_or_eq_true ((denot A s0).blks q)
                  with hq | hq
                · exact absurd (active_pred_unique hwfA hklt hpA hppredA
                    (mem_activeList.mpr ⟨by omega, hq⟩) hqpred) hqne
                · exact hq
        -- B's own run selects ob's arm
        have hown : (denot B s0).regs t' x = (denot B s0).regs t' src := by
          rw [denot_phi hwfB hBb hcmem]
          cases arms with
          | nil => cases hsrcmem
          | cons a0 arest =>
              have hobB : (denot B s0).blks ob = true :=
                hxfer o ob (by omega) hob hoact
              have hobBmem : ob ∈ activeList B s0 :=
                mem_activeList.mpr ⟨by
                  exact Nat.lt_of_lt_of_le (pred_lt hwfB.fwd hobpredB)
                    (by omega), hobB⟩
              refine phiChain_eval_select a0 arest hsrc ?_ ?_
              · unfold Vc.guardOf
                split
                · rfl
                · exact hobB
              · intro qb s' hqarm hqne
                have hqpredB := phiArm_pred harmsB hqarm
                unfold Vc.guardOf
                rw [if_neg (by
                  intro hqe
                  obtain ⟨hentB, -⟩ := denot_hentry hwfB.fwd hwfB.uses hobBmem
                  exact hqne (active_pred_unique hwfB hkblt hobBmem hobpredB
                    (by rw [hqe]; exact hentB) hqpredB))]
                show (denot B s0).blks qb = false
                rcases Bool.eq_false_or_eq_true ((denot B s0).blks qb)
                  with hq | hq
                · exact absurd (active_pred_unique hwfB hkblt hobBmem
                    hobpredB (mem_activeList.mpr
                      ⟨Nat.lt_of_lt_of_le (pred_lt hwfB.fwd hqpredB)
                        (by omega), hq⟩) hqpredB) hqne
                · exact hq
        -- the source is Good via arm dominance at ob
        simp only [cmdUsesOK] at husec
        have hsrcGood : GoodBS A B mt s0 t' src := by
          have := List.all_eq_true.mp husec (ob, src) hsrcmem
          exact goodS_of_arm hwfA hwfB hs hdcB hob hoact
            (by omega) this
        rw [hval, hB t' src hsrcGood, ← hown, ← hB t' x hgood,
          State.upd_self]
        exact ⟨hA, hB, rfl, trivial⟩
      · -- A-inactive: junk write onto a non-Good register
        have hng := not_goodBS_of_inactive_def hs hm hBb hci rfl
          (by intro h; cases h) hinact
        refine ⟨fun t x' => ?_, fun t x' hg => ?_, rfl, trivial⟩
        · rw [State.upd_regs_of_ne R
            (pv_pair_ne (j := 0) (j' := 1) (by omega) (by omega)
              (by omega) x' x)]
          exact hA t x'
        · have hne : ((t, pv 1 x') : Ty × Nat) ≠ (t', pv 1 x) := by
            intro heq
            obtain ⟨rfl, hx⟩ := Prod.mk.injEq .. |>.mp heq
            obtain rfl : x' = x := ((pv_eq_iff (by omega) (by omega)).mp hx).2
            exact hng hg
          rw [State.upd_regs_of_ne R hne]
          exact hB t x' hg

/-- The B-copy segment fold at a matched block: invariants, deposits,
survival. -/
theorem prodCmdBS_fold {A B : Program} {mt : List (Option Nat)} {s0 : State}
    (hwfA : WellFormed A) (hwfB : WellFormed B)
    (hdcB : domClosedOK B = true) (hs : surgeryOK A B mt = true)
    {k kb : Nat} {Ba Bb : Block}
    (hBa : A.block? k = some Ba) (hBb : B.block? kb = some Bb)
    (hm : matchOf mt k = some kb)
    (hxfer : ∀ a b', a < k → matchOf mt a = some b' →
      (denot A s0).blks a = true → (denot B s0).blks b' = true) :
    ∀ (l : List (Cmd × Nat)),
      (∀ ci ∈ l, Bb.cmds[ci.2]? = some ci.1) →
      List.Pairwise (fun (ci cj : Cmd × Nat) => ci.2 < cj.2) l →
      ∀ (R : State), HalfA A s0 R → HalfBS A B mt s0 R →
        (∀ p, p < k → R.blks p = (denot A s0).blks p) →
        ∀ R', R' = (l.flatMap fun ci =>
            prodCmdBS A mt Ba (chkStride B.blocks) k ci.2 ci.1).foldl
              (denotCmd (productS A B mt)) R →
          HalfA A s0 R' ∧ HalfBS A B mt s0 R' ∧ R'.blks = R.blks
            ∧ ∀ ci ∈ l, DepositAt A B s0 Ba (chkStride B.blocks) k R' ci
  | [], _, _, R, hA, hB, hblks, R', hR' => by
      subst hR'
      exact ⟨hA, hB, rfl, fun ci hci => absurd hci List.not_mem_nil⟩
  | (c, i) :: l, hsub, hpw, R, hA, hB, hblks, R', hR' => by
      rw [List.flatMap_cons, List.foldl_append] at hR'
      obtain ⟨hA₁, hB₁, hblks₁, hdep₁⟩ := prodCmdBS_step hwfA hwfB hdcB hs
        hBa hBb hm hxfer (hsub _ (List.mem_cons_self ..)) hA hB hblks _ rfl
      obtain ⟨hA', hB', hblks', hdep'⟩ := prodCmdBS_fold hwfA hwfB hdcB hs
        hBa hBb hm hxfer l
        (fun ci hci => hsub ci (List.mem_cons_of_mem _ hci))
        (List.pairwise_cons.mp hpw).2 _ hA₁ hB₁
        (fun p hp => by rw [hblks₁]; exact hblks p hp) R' hR'
      have hilt : i < Bb.cmds.length :=
        (List.getElem?_eq_some_iff.mp (hsub _ (List.mem_cons_self ..))).1
      have histride : i < chkStride B.blocks :=
        Nat.lt_trans hilt (lt_chkStride hBb)
      have hnt : R'.regs .bool (chkReg (chkStride B.blocks) k i)
          = ((prodCmdBS A mt Ba (chkStride B.blocks) k i c).foldl
              (denotCmd (productS A B mt)) R).regs .bool
                (chkReg (chkStride B.blocks) k i) := by
        rw [hR']
        refine cmdsFold_regs_ne (fun c' hc' tx htx => ?_)
        obtain ⟨ci', hci'mem, hc'in⟩ := List.mem_flatMap.mp hc'
        obtain ⟨t', w⟩ := tx
        rcases prodCmdBS_def_target hc'in htx with ⟨x, rfl⟩ | rfl
        · exact pv_chk_pair_ne (by omega) (by omega) x _ _ _
        · intro heq
          have hsnd := congrArg Prod.snd heq
          have hi'lt : ci'.2 < Bb.cmds.length :=
            (List.getElem?_eq_some_iff.mp
              (hsub ci' (List.mem_cons_of_mem _ hci'mem))).1
          have hi'stride : ci'.2 < chkStride B.blocks :=
            Nat.lt_trans hi'lt (lt_chkStride hBb)
          have := (chkReg_inj hi'stride histride hsnd).2
          have hlt := (List.pairwise_cons.mp hpw).1 ci' hci'mem
          omega
      refine ⟨hA', hB', by rw [hblks', hblks₁], fun ci hci => ?_⟩
      rcases List.mem_cons.mp hci with rfl | hci'
      · exact depositAt_congr (c, i) hnt hdep₁
      · exact hdep' ci hci'

/-- The branch CHK at a matched block. -/
theorem prodTermChkS_fold {A B : Program} {mt : List (Option Nat)}
    {s0 : State} (hwfA : WellFormed A) (hwfB : WellFormed B)
    (hdcB : domClosedOK B = true) (hs : surgeryOK A B mt = true)
    {k kb : Nat} {Ba Bb : Block}
    (hBa : A.block? k = some Ba) (hBb : B.block? kb = some Bb)
    (hm : matchOf mt k = some kb)
    {R : State} (hA : HalfA A s0 R) (hB : HalfBS A B mt s0 R) :
    ∀ R', R' = (prodTermChk (chkStride B.blocks) k Ba Bb).foldl
        (denotCmd (productS A B mt)) R →
      HalfA A s0 R' ∧ HalfBS A B mt s0 R' ∧ R'.blks = R.blks
        ∧ (∀ i, i < Bb.cmds.length →
            R'.regs .bool (chkReg (chkStride B.blocks) k i)
              = R.regs .bool (chkReg (chkStride B.blocks) k i))
        ∧ ((denot A s0).blks k = true →
            ∀ cA tA eA cB tB eB, Ba.term = .ifGoto cA tA eA →
              Bb.term = .ifGoto cB tB eB →
              R'.regs .bool (chkReg (chkStride B.blocks) k Bb.cmds.length)
                = ((denot A s0).regs .bool cA
                    == (denot B s0).regs .bool cB)) := by
  intro R' hR'
  have hklt : k < A.blocks.length := (List.getElem?_eq_some_iff.mp hBa).1
  unfold prodTermChk at hR'
  cases hta : Ba.term with
  | ifGoto cA tA eA =>
      cases htb : Bb.term with
      | ifGoto cB tB eB =>
          rw [hta, htb] at hR'
          have hR'' : R' = R.upd .bool
              (chkReg (chkStride B.blocks) k Bb.cmds.length)
              ((Exp.eqB (.var .bool (pv 0 cA))
                (.var .bool (pv 1 cB))).eval R) := hR'
          subst hR''
          refine ⟨fun t x => ?_, fun t x hg => ?_, rfl,
            fun i hi => ?_, fun hactive cA' tA' eA' cB' tB' eB' hta' htb' => ?_⟩
          · rw [State.upd_regs_of_ne R
              (pv_chk_pair_ne (j := 0) (by omega) (by omega) x _ _ _)]
            exact hA t x
          · rw [State.upd_regs_of_ne R
              (pv_chk_pair_ne (j := 1) (by omega) (by omega) x _ _ _)]
            exact hB t x hg
          · rw [State.upd_regs_of_ne R (fun heq => ?_)]
            have hsnd := congrArg Prod.snd heq
            have hstride := lt_chkStride hBb
            have := (chkReg_inj (by omega) (by omega) hsnd).2
            omega
          · obtain ⟨rfl, rfl, rfl⟩ := Terminator.ifGoto.inj hta'
            obtain ⟨rfl, rfl, rfl⟩ := Terminator.ifGoto.inj htb'
            show (R.upd .bool _ _).regs .bool _ = _
            rw [State.upd_regs_self]
            show (R.regs .bool (pv 0 cA) == R.regs .bool (pv 1 cB)) = _
            have hterm_use := usesOK_term hwfB.uses hBb
            simp only [termUsesOK, htb] at hterm_use
            rw [hA .bool cA, hB .bool cB
              (goodS_of_use hwfA hwfB hs hdcB hm hactive hklt hterm_use)]
      | halt =>
          rw [hta, htb] at hR'
          subst hR'
          exact ⟨hA, hB, rfl, fun i hi => rfl,
            fun _ _ _ _ _ _ _ _ htb' => by cases htb'⟩
      | goto tB =>
          rw [hta, htb] at hR'
          subst hR'
          exact ⟨hA, hB, rfl, fun i hi => rfl,
            fun _ _ _ _ _ _ _ _ htb' => by cases htb'⟩
  | halt =>
      rw [hta] at hR'
      subst hR'
      exact ⟨hA, hB, rfl, fun i hi => rfl,
        fun _ _ _ _ _ _ _ hta' => by cases hta'⟩
  | goto tA =>
      rw [hta] at hR'
      subst hR'
      exact ⟨hA, hB, rfl, fun i hi => rfl,
        fun _ _ _ _ _ _ _ hta' => by cases hta'⟩

/-- One surgical-product block, end to end: matched blocks advance both
copies and deposit their CHKs; stutter blocks advance the A-copy only.
Either way the guard lands on A's. -/
theorem prodBlockS_run {A B : Program} {mt : List (Option Nat)} {s0 : State}
    (hwfA : WellFormed A) (hwfB : WellFormed B)
    (hdcB : domClosedOK B = true) (hs : surgeryOK A B mt = true)
    {b : Nat} {Ba : Block} (hBa : A.block? b = some Ba)
    (hxfer : ∀ a b', a < b → matchOf mt a = some b' →
      (denot A s0).blks a = true → (denot B s0).blks b' = true)
    {R : State} (hA : HalfA A s0 R) (hB : HalfBS A B mt s0 R)
    (hblks : ∀ p, p < b → R.blks p = (denot A s0).blks p) :
    ∀ R', R' = denotBlock (productS A B mt) R b →
      HalfA A s0 R' ∧ HalfBS A B mt s0 R'
        ∧ (∀ p, p < b + 1 → R'.blks p = (denot A s0).blks p)
        ∧ (∀ kb Bb, matchOf mt b = some kb → B.block? kb = some Bb →
            (∀ ci : Cmd × Nat, Bb.cmds[ci.2]? = some ci.1 →
              DepositAt A B s0 Ba (chkStride B.blocks) b R' ci)
            ∧ ((denot A s0).blks b = true →
                ∀ cA tA eA cB tB eB, Ba.term = .ifGoto cA tA eA →
                  Bb.term = .ifGoto cB tB eB →
                  R'.regs .bool
                    (chkReg (chkStride B.blocks) b Bb.cmds.length)
                    = ((denot A s0).regs .bool cA
                        == (denot B s0).regs .bool cB))) := by
  intro R' hR'
  unfold denotBlock at hR'
  rw [productS_block? hBa] at hR'
  set Wc := (prodBlockS A B mt (chkStride B.blocks) b Ba).cmds.foldl
    (denotCmd (productS A B mt)) R with hWc
  have hR2 : R' = { regs := Wc.regs, blks := Function.update Wc.blks b (reach (productS A B mt) Wc b && assumesOK Wc (prodBlockS A B mt (chkStride B.blocks) b Ba)) } := hR'
  subst hR2
  -- the command fold, by block shape
  have hfold : HalfA A s0 Wc ∧ HalfBS A B mt s0 Wc ∧ Wc.blks = R.blks
      ∧ (∀ kb Bb, matchOf mt b = some kb → B.block? kb = some Bb →
          (∀ ci : Cmd × Nat, Bb.cmds[ci.2]? = some ci.1 →
            DepositAt A B s0 Ba (chkStride B.blocks) b Wc ci)
          ∧ ((denot A s0).blks b = true →
              ∀ cA tA eA cB tB eB, Ba.term = .ifGoto cA tA eA →
                Bb.term = .ifGoto cB tB eB →
                Wc.regs .bool
                  (chkReg (chkStride B.blocks) b Bb.cmds.length)
                  = ((denot A s0).regs .bool cA
                      == (denot B s0).regs .bool cB))) := by
    cases hm : matchOf mt b with
    | none =>
        have hWc' : Wc = R := by
          rw [hWc, prodBlockS_stutter hm]
          exact prodCmdA_foldS hwfA hBa Ba.cmds (fun c hc => hc) R hA hblks
        rw [hWc']
        exact ⟨hA, hB, rfl, fun kb Bb hkb => by cases hkb⟩
    | some kb =>
        cases hBb : B.block? kb with
        | none =>
            have hWc' : Wc = R := by
              rw [hWc, prodBlockS_unmatched hm hBb]
              exact prodCmdA_foldS hwfA hBa Ba.cmds (fun c hc => hc) R hA
                hblks
            rw [hWc']
            refine ⟨hA, hB, rfl, fun kb' Bb' hkb' hBb' => ?_⟩
            obtain rfl : kb = kb' := Option.some.inj hkb' 
            rw [hBb] at hBb'
            cases hBb'
        | some Bb =>
            set R₂ := (Bb.cmds.zipIdx.flatMap fun ci =>
              prodCmdBS A mt Ba (chkStride B.blocks) b ci.2 ci.1).foldl
              (denotCmd (productS A B mt)) R with hR₂
            have hfoldA : (Ba.cmds.flatMap prodCmdA).foldl
                (denotCmd (productS A B mt)) R = R :=
              prodCmdA_foldS hwfA hBa Ba.cmds (fun c hc => hc) R hA hblks
            have hsplit : Wc = (prodTermChk (chkStride B.blocks) b Ba
                Bb).foldl (denotCmd (productS A B mt)) R₂ := by
              rw [hWc, hR₂, prodBlockS_matched hm hBb]
              show ((Ba.cmds.flatMap prodCmdA
                ++ Bb.cmds.zipIdx.flatMap (fun ci =>
                    prodCmdBS A mt Ba (chkStride B.blocks) b ci.2 ci.1)
                ++ prodTermChk (chkStride B.blocks) b Ba Bb).foldl
                  (denotCmd (productS A B mt)) R) = _
              rw [List.foldl_append, List.foldl_append, hfoldA]
            obtain ⟨hA₂, hB₂, hblks₂, hdeps⟩ := prodCmdBS_fold hwfA hwfB
              hdcB hs hBa hBb hm hxfer Bb.cmds.zipIdx
              (fun ci hci => List.mem_zipIdx_iff_getElem?.mp hci)
              (zipIdx_pairwise Bb.cmds 0) R hA hB hblks R₂ hR₂
            obtain ⟨hA₃, hB₃, hblks₃, hkeep, hbranch⟩ := prodTermChkS_fold
              hwfA hwfB hdcB hs hBa hBb hm hA₂ hB₂ Wc hsplit
            refine ⟨hA₃, hB₃, by rw [hblks₃, hblks₂],
              fun kb' Bb' hkb' hBb' => ?_⟩
            obtain rfl : kb = kb' := Option.some.inj hkb' 
            obtain rfl : Bb = Bb' := Option.some.inj (hBb.symm.trans hBb')
            refine ⟨fun ci hci => ?_, hbranch⟩
            have hilen : ci.2 < Bb.cmds.length :=
              (List.getElem?_eq_some_iff.mp hci).1
            refine depositAt_congr ci (hkeep ci.2 hilen) ?_
            exact hdeps ci (List.mem_zipIdx_iff_getElem?.mpr hci)
  obtain ⟨hAc, hBc, hblksc, hdepsc⟩ := hfold
  have hWcblks : ∀ p, p < b → Wc.blks p = (denot A s0).blks p := by
    intro p hp
    rw [hblksc]
    exact hblks p hp
  have hguard : (reach (productS A B mt) Wc b
      && assumesOK Wc (prodBlockS A B mt (chkStride B.blocks) b Ba))
      = (denot A s0).blks b := by
    rw [reach_productS hwfA.fwd hAc hWcblks,
      assumesOK_prodBlockS hwfA.gf hBa hAc]
    exact (denot_blks_final_char hwfA hBa).symm
  refine ⟨hAc, hBc, fun p hp => ?_, hdepsc⟩
  show Function.update Wc.blks b _ p = _
  by_cases hpb : p = b
  · subst hpb
    rw [Function.update_self]
    exact hguard
  · rw [Function.update_of_ne hpb]
    exact hWcblks p (by omega)

/-! ## The main induction -/

/-- The extracted CHK content of an A-active matched block. -/
abbrev ChkFactsS (A B : Program) (mt : List (Option Nat)) (s0 : State)
    (b : Nat) : Prop :=
  (denot A s0).blks b = true →
    ∀ kb Ba Bb, matchOf mt b = some kb → A.block? b = some Ba →
      B.block? kb = some Bb →
      assumesOK (denot B s0) Bb = true
      ∧ (∀ cA tA eA cB tB eB, Ba.term = .ifGoto cA tA eA →
          Bb.term = .ifGoto cB tB eB →
          (denot A s0).regs .bool cA = (denot B s0).regs .bool cB)
      ∧ (∀ (iB cB' cA' : Nat), Bb.cmds[iB]? = some (Cmd.assert cB') →
          Ba.assertReg? = some cA' →
          (denot A s0).regs .bool cA' = (denot B s0).regs .bool cB')

theorem chkS_extract {A B : Program} {mt : List (Option Nat)} {σ : State}
    (hP : Safe_denot (productS A B mt)) {b i : Nat} {Ba : Block}
    (hBa : A.block? b = some Ba) (hi : i < chkStride B.blocks)
    (hassert : Cmd.assert (chkReg (chkStride B.blocks) b i)
      ∈ (prodBlockS A B mt (chkStride B.blocks) b Ba).cmds)
    (hblkA : (prefixState (productS A B mt) σ (b + 1)).blks b = true) :
    (prefixState (productS A B mt) σ (b + 1)).regs .bool
      (chkReg (chkStride B.blocks) b i) = true := by
  have hblt : b < A.blocks.length := (List.getElem?_eq_some_iff.mp hBa).1
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hassert
  have hsite : (b, j, chkReg (chkStride B.blocks) b i)
      ∈ Vc.assertSites (productS A B mt) :=
    mem_assertSites.mpr ⟨_, productS_block? hBa, hj⟩
  have hfinal := safe_denot_site_true hP σ hsite
    (by rw [productS_length]; omega)
    (by rw [productS_final_blks hblt]; exact hblkA)
  rw [productS_chk_stable hi hblt] at hfinal
  exact hfinal

theorem prodSeed_halfBS (A B : Program) (mt : List (Option Nat))
    (s0 : State) : HalfBS A B mt s0 (prodSeed A B s0) := by
  intro t x _
  show (if pv 1 x % 3 = 1 then _ else _) = _
  rw [if_pos (by unfold pv; omega)]
  unfold pv
  congr 1
  omega

/-- The transfer invariant for the surgical product. -/
theorem transfer_invS {A B : Program} {mt : List (Option Nat)} {s0 : State}
    (hwfA : WellFormed A) (hwfB : WellFormed B)
    (hdcB : domClosedOK B = true) (hs : surgeryOK A B mt = true)
    (hP : Safe_denot (productS A B mt)) :
    ∀ k, k ≤ A.blocks.length →
      HalfA A s0 (prefixState (productS A B mt) (prodSeed A B s0) k)
      ∧ HalfBS A B mt s0 (prefixState (productS A B mt) (prodSeed A B s0) k)
      ∧ (∀ b, b < k →
          (prefixState (productS A B mt) (prodSeed A B s0) k).blks b
            = (denot A s0).blks b)
      ∧ (∀ a b', a < k → matchOf mt a = some b' →
          (denot A s0).blks a = true → (denot B s0).blks b' = true)
      ∧ (∀ b, b < k → ChkFactsS A B mt s0 b)
  | 0, _ => ⟨prodSeed_halfA A B s0, prodSeed_halfBS A B mt s0,
      fun b hb => absurd hb (Nat.not_lt_zero b),
      fun a b' ha => absurd ha (Nat.not_lt_zero a),
      fun b hb => absurd hb (Nat.not_lt_zero b)⟩
  | k + 1, hk1 => by
      obtain ⟨ihA, ihB, ihblks, ihxfer, ihchk⟩ :=
        transfer_invS hwfA hwfB hdcB hs hP k (by omega)
      have hklt : k < A.blocks.length := by omega
      have hBa : A.block? k = some A.blocks[k] := List.getElem?_eq_getElem hklt
      obtain ⟨hA', hB', hblks', hmatched⟩ := prodBlockS_run hwfA hwfB hdcB hs
        hBa (fun a b' ha => ihxfer a b' ha) ihA ihB ihblks
        _ (prefixState_succ (productS A B mt) (prodSeed A B s0) k)
      have hchk_k : ChkFactsS A B mt s0 k := by
        intro hactive kb Ba' Bb hkb hBa' hBb
        obtain rfl : A.blocks[k] = Ba' := Option.some.inj (hBa.symm.trans hBa')
        obtain ⟨hdeps, hbranch⟩ := hmatched kb Bb hkb hBb
        have hblkA : (prefixState (productS A B mt) (prodSeed A B s0)
            (k + 1)).blks k = true := by
          rw [hblks' k (Nat.lt_succ_self k)]
          exact hactive
        refine ⟨?_, ?_, ?_⟩
        · unfold assumesOK
          rw [List.all_eq_true]
          intro c hc
          cases c with
          | assume φ =>
              obtain ⟨i, hci⟩ := List.mem_iff_getElem?.mp hc
              have hilen : i < Bb.cmds.length :=
                (List.getElem?_eq_some_iff.mp hci).1
              have histride : i < chkStride B.blocks :=
                Nat.lt_trans hilen (lt_chkStride hBb)
              have hdep := hdeps (Cmd.assume φ, i) hci hactive
              have hval := chkS_extract hP hBa histride
                (chkS_assume_mem hkb hBb hci) hblkA
              show φ.eval (denot B s0) = true
              rw [← hdep]
              exact hval
          | assign t x e => trivial
          | havoc t x => trivial
          | phi t x arms => trivial
          | assert r => trivial
        · intro cA tA eA cB tB eB hta htb
          have hlenstride : Bb.cmds.length < chkStride B.blocks :=
            lt_chkStride hBb
          have hdep := hbranch hactive cA tA eA cB tB eB hta htb
          have hval := chkS_extract hP hBa hlenstride
            (chkS_branch_mem hkb hBb hta htb) hblkA
          rw [hdep] at hval
          exact beq_iff_eq.mp hval
        · intro iB cB' cA' hiB hreg
          have hilen : iB < Bb.cmds.length :=
            (List.getElem?_eq_some_iff.mp hiB).1
          have histride : iB < chkStride B.blocks :=
            Nat.lt_trans hilen (lt_chkStride hBb)
          have hdep := hdeps (Cmd.assert cB', iB) hiB hactive cA' hreg
          have hval := chkS_extract hP hBa histride
            (chkS_assert_mem hkb hBb hiB) hblkA
          rw [hdep] at hval
          exact beq_iff_eq.mp hval
      have hxfer_k : ∀ kb, matchOf mt k = some kb →
          (denot A s0).blks k = true → (denot B s0).blks kb = true := by
        intro kb hkb hactive
        obtain ⟨Bb, hBb, htermS, -⟩ := (surgery_block hs hBa).2 kb hkb
        obtain ⟨hassumesB, -, -⟩ := hchk_k hactive kb A.blocks[k] Bb hkb
          hBa hBb
        have hkblt : kb < B.blocks.length :=
          (List.getElem?_eq_some_iff.mp hBb).1
        have hreachB : reach B (denot B s0) kb = true := by
          unfold reach
          by_cases hke : k = A.entry
          · rw [Bool.or_eq_true]
            left
            have : kb = B.entry := by
              have hent := surgery_entry hs
              rw [← hke] at hent
              exact Option.some.inj (hkb.symm.trans hent)
            exact decide_eq_true this
          · rw [Bool.or_eq_true]
            right
            obtain ⟨p, hpact, hplt, hpE⟩ :=
              denot_active_pred hwfA.fwd hwfA.uses hBa hactive hke
            -- resolve to the active matched owner with a chase into k
            obtain ⟨o, ob, hob, hoact, hole, h', hoE, hchase⟩ :
                ∃ o ob, matchOf mt o = some ob
                  ∧ (denot A s0).blks o = true ∧ o ≤ p
                  ∧ ∃ h', EdgeTaken A (denot A s0) o h'
                      ∧ chase A mt h' = some k := by
              by_cases hpm : (matchOf mt p).isSome
              · obtain ⟨pb, hpb⟩ := Option.isSome_iff_exists.mp hpm
                exact ⟨p, pb, hpb, hpact, Nat.le_refl _, k, hpE,
                  chase_matched (by omega) (by rw [hkb]; simp)⟩
              · have hpmn : matchOf mt p = none := by
                  cases h : matchOf mt p with
                  | none => rfl
                  | some b => rw [h] at hpm; simp at hpm
                obtain ⟨h1, h2, h', hE', hch⟩ := stutter_origin hwfA hs p
                  hpmn hpact (by omega)
                obtain ⟨ob', hob'⟩ := Option.isSome_iff_exists.mp h1
                refine ⟨owner A mt p, ob', hob', h2, owner_le hwfA.fwd p,
                  h', hE', ?_⟩
                rw [hch]
                -- chase p: p's taken goto edge lands on k
                have hBp : A.block? p = some A.blocks[p] :=
                  List.getElem?_eq_getElem (by omega)
                have hstut := (surgery_block hs hBp).1 hpmn
                unfold stutterBlockOK at hstut
                simp only [Bool.and_eq_true, decide_eq_true_eq] at hstut
                obtain ⟨tp, htp⟩ : ∃ tp, (A.blocks[p]).term = .goto tp := by
                  cases h'' : (A.blocks[p]).term with
                  | goto t => exact ⟨t, rfl⟩
                  | halt => rw [h''] at hstut; simp at hstut
                  | ifGoto c th el => rw [h''] at hstut; simp at hstut
                obtain rfl : tp = k := by
                  obtain ⟨Bp', hBp', hshape⟩ := hpE
                  obtain rfl : A.blocks[p] = Bp' :=
                    Option.some.inj (hBp.symm.trans hBp')
                  rcases hshape with hgoto | ⟨c, th, el, hif, -⟩
                  · rw [htp] at hgoto
                    exact Terminator.goto.inj hgoto
                  · rw [htp] at hif
                    cases hif
                rw [chase_stutter_step hwfA.fwd (surgery_len hs) hpmn
                  hBp htp]
                exact chase_matched (by omega) (by rw [hkb]; simp)
            -- B's edge from the owner's match
            have holt : o < A.blocks.length := by omega
            have hBo : A.block? o = some A.blocks[o] :=
              List.getElem?_eq_getElem holt
            obtain ⟨Bob, hBob, htermO, -⟩ := (surgery_block hs hBo).2 ob hob
            have hobB : (denot B s0).blks ob = true :=
              ihxfer o ob (by omega) hob hoact
            obtain ⟨Bo', hBo', hshapeO⟩ := hoE
            obtain rfl : A.blocks[o] = Bo' :=
              Option.some.inj (hBo.symm.trans hBo')
            have hchaseT : ∀ tb : Nat, chaseTargetOK A B mt h' tb = true →
                kb = tb := by
              intro tb h1
              unfold chaseTargetOK at h1
              rw [hchase] at h1
              have h2 : (matchOf mt k == some tb
                  && decide (tb < B.blocks.length)) = true := h1
              rw [Bool.and_eq_true] at h2
              have htb : matchOf mt k = some tb := beq_iff_eq.mp h2.1
              rw [hkb] at htb
              exact Option.some.inj htb
            have hEB : EdgeTaken B (denot B s0) ob kb := by
              refine ⟨Bob, hBob, ?_⟩
              rcases hshapeO with hgoto | ⟨c, th, el, hif, harm⟩
              · unfold termSurgeryOK at htermO
                rw [hgoto] at htermO
                cases hTb : Bob.term with
                | halt => rw [hTb] at htermO; cases htermO
                | ifGoto cb tb eb => rw [hTb] at htermO; cases htermO
                | goto tb =>
                    rw [hTb] at htermO
                    have htermO' : chaseTargetOK A B mt h' tb = true :=
                      htermO
                    obtain rfl : kb = tb := hchaseT tb htermO'
                    exact Or.inl rfl
              · unfold termSurgeryOK at htermO
                rw [hif] at htermO
                cases hTb : Bob.term with
                | halt => rw [hTb] at htermO; cases htermO
                | goto tb => rw [hTb] at htermO; cases htermO
                | ifGoto cb tb eb =>
                    rw [hTb] at htermO
                    have htermO' : (chaseTargetOK A B mt th tb
                        && chaseTargetOK A B mt el eb) = true := htermO
                    rw [Bool.and_eq_true] at htermO'
                    -- the branch registers agree at the active owner o
                    have hofacts := ihchk o (by omega) hoact ob A.blocks[o]
                      Bob hob hBo hBob
                    have hcval := hofacts.2.1 c th el cb tb eb hif hTb
                    right
                    refine ⟨cb, tb, eb, rfl, ?_⟩
                    rcases harm with ⟨rfl, hc⟩ | ⟨rfl, hc⟩
                    · obtain rfl : kb = tb := hchaseT tb htermO'.1
                      exact Or.inl ⟨rfl, by rw [← hcval]; exact hc⟩
                    · obtain rfl : kb = eb := hchaseT eb htermO'.2
                      exact Or.inr ⟨rfl, by rw [← hcval]; exact hc⟩
            obtain ⟨cond, hcm, hcv⟩ := hEB.edge_cond
            refine List.any_eq_true.mpr ⟨(ob, cond), hcm, ?_⟩
            rw [Bool.and_eq_true]
            exact ⟨hobB, hcv⟩
        rw [denot_blks_final_char hwfB hBb, Bool.and_eq_true]
        exact ⟨hreachB, hassumesB⟩
      refine ⟨hA', hB', hblks', fun a b' ha hb' => ?_, fun b hb => ?_⟩
      · rcases Nat.lt_or_ge a k with hak | hak
        · exact ihxfer a b' hak hb'
        · obtain rfl : a = k := by omega
          exact hxfer_k b' hb'
      · rcases Nat.lt_or_ge b k with hbk | hbk
        · exact ihchk b hbk
        · obtain rfl : b = k := by omega
          exact hchk_k

/-! ## The theorem

The conjecture strengthened twice over its probe form: neither
`domClosedOK A` nor `phiCoversOK B` is needed. A-side dominance was
replaced by walking `B`'s closure facts along the projected active
path (`good_of_domB`), and the routing check subsumes phi coverage at
every join the transfer inspects. -/

theorem stutter_transfer {A B : Program} {mt : List (Option Nat)}
    (hwfA : WellFormed A) (hwfB : WellFormed B)
    (hdcB : domClosedOK B = true) (hs : surgeryOK A B mt = true)
    (hP : Safe_denot (productS A B mt)) (hB : Safe_denot B) :
    Safe_denot A := by
  intro s0
  rcases Bool.eq_false_or_eq_true ((denot A s0).blks A.blocks.length)
    with hexit | hsafe
  case inr => exact hsafe
  case inl =>
  exfalso
  have hexit' : ReachesExit A s0 := hexit
  obtain ⟨aB, iA, okA, BA, hsitesA, hBA, hcA, -⟩ :=
    singleAssert_shape hwfA.one
  obtain ⟨haBact, hokA⟩ := denot_fail hexit' aB iA okA hsitesA
  obtain ⟨bB, iB, okB, BB, hsitesB, hBB, hcB, -⟩ :=
    singleAssert_shape hwfB.one
  have hmatch : matchOf mt aB = some bB := surgery_sites hs hsitesA hsitesB
  obtain ⟨-, -, -, hxfer, hchk⟩ := transfer_invS (s0 := s0) hwfA hwfB hdcB
    hs hP A.blocks.length (Nat.le_refl _)
  have haBlt : aB < A.blocks.length := (List.getElem?_eq_some_iff.mp hBA).1
  have haBactA : (denot A s0).blks aB = true := (mem_activeList.mp haBact).2
  have hreg : BA.assertReg? = some okA := by
    refine assertReg?_eq (List.mem_of_getElem? hcA) (fun r hr => ?_)
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hr
    have hmem := mem_assertSites.mpr ⟨BA, hBA, hj⟩
    rw [hsitesA, List.mem_singleton] at hmem
    exact congrArg (·.2.2) hmem
  obtain ⟨-, -, hassertpair⟩ := hchk aB haBlt haBactA bB BA BB hmatch hBA hBB
  have hokBval : (denot B s0).regs .bool okB = false := by
    rw [← hassertpair iB okB okA hcB hreg]
    exact hokA
  have haBltB : bB < B.blocks.length := (List.getElem?_eq_some_iff.mp hBB).1
  have hexitB : (denot B s0).blks B.blocks.length = true := by
    rw [denot_blks_exit]
    unfold reachExit
    rw [hsitesB]
    refine List.any_eq_true.mpr ⟨(bB, iB, okB), List.mem_singleton.mpr rfl, ?_⟩
    rw [Bool.and_eq_true]
    constructor
    · show (prefixState B s0 B.blocks.length).blks bB = true
      rw [← denot_blks_lt haBltB]
      exact hxfer aB bB haBlt hmatch haBactA
    · show (!(prefixState B s0 B.blocks.length).regs .bool okB) = true
      have hv : (prefixState B s0 B.blocks.length).regs .bool okB = false := by
        rw [← denot_regs]
        exact hokBval
      rw [hv]
      rfl
  exact Bool.false_ne_true ((hB s0).symm.trans hexitB)

/-- The operational form. -/
theorem stutter_transfer_safe {A B : Program} {mt : List (Option Nat)}
    (hwfA : wellFormed A = true) (hwfB : wellFormed B = true)
    (hcovA : phiCoversOK A = true) (hcovB : phiCoversOK B = true)
    (hs : surgeryOK A B mt = true)
    (hP : Safe_denot (productS A B mt)) (hB : B.Safe) : A.Safe := by
  obtain ⟨hwfA', -⟩ := wellFormed_iff.mp hwfA
  obtain ⟨hwfB', hdcB⟩ := wellFormed_iff.mp hwfB
  exact (safe_iff_safe_denot hwfA hcovA).mpr
    (stutter_transfer hwfA' hwfB' hdcB hs hP
      ((safe_iff_safe_denot hwfB hcovB).mp hB))

end Ttac
