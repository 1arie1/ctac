import Ttac.VcAdequacy

/-!
# Converse adequacy: a denotational EXIT-run replays operationally

`VcAdequacy` proves the operational→denotational direction. Here the
converse: a seed whose denotational fold reaches EXIT induces a real
operational execution ending in `.failed` — under `wellFormed` plus one
extra decidable check, `phiCoversOK` (every predecessor of a phi block
has an arm). Coverage is genuinely necessary: at an uncovered taken
predecessor the operational machine is *stuck* at the phi (no `Step`
rule) while the fold falls through to `phiChain`'s unguarded last arm
and may still reach EXIT — the denotational semantics strictly
over-approximates there. `phiCoversOK` is deliberately NOT part of
`wellFormed`: the checkers' soundness direction never needs it.

The construction mirrors adequacy's seed trick in reverse: run the
machine from `W := denot P s0` itself. Every write then writes the
value already present — assigns by `denot_assign`, phis by `denot_phi`
+ `phiChain_eval_select` (the taken predecessor is the unique active
one, by `visited_amo`), havocs by choosing the current value — so the
state is *constant along the run* and each `upd` collapses by
`State.upd_self`. No register-agreement invariant, and — unlike
adequacy — no dominance: `domClosedOK` is never consumed.

Together with `adequacy` this closes the loop:
`safe_iff_safe_denot : P.Safe ↔ Safe_denot P`.
-/

namespace Ttac

open Vc

/-! ## Phi-arm coverage -/

/-- Every predecessor of a phi's block has an arm. `phiOK` gives only
arms ⊆ preds; the operational `Step.phi` needs the taken predecessor to
be covered. -/
def phiCoversOK (P : Program) : Bool :=
  P.blocks.zipIdx.all fun (B, b) =>
    B.cmds.all fun c =>
      match c with
      | .phi _ _ arms => (predsOf P b).all fun p => (arms.map (·.1)).contains p
      | _ => true

theorem phiCovers_at {P : Program} (hcov : phiCoversOK P = true) {b : Nat}
    {B : Block} (hB : P.block? b = some B) {t : Ty} {x : Nat}
    {arms : PhiArms} (hc : Cmd.phi t x arms ∈ B.cmds) {p : Nat}
    (hp : p ∈ predsOf P b) : p ∈ arms.map (·.1) := by
  have h1 := List.all_eq_true.mp hcov (B, b) (List.mem_zipIdx_iff_getElem?.mpr hB)
  have h2 := List.all_eq_true.mp h1 _ hc
  have h3 := List.all_eq_true.mp h2 p hp
  exact List.contains_iff_mem.mp h3

/-! ## Small helpers -/

/-- `phiOK` forbids phis in the entry block: arms are nonempty and each
arm's predecessor is strictly below its block, but entry is block 0. -/
theorem no_phi_in_entry {P : Program} (hphi : phiOK P = true)
    (hentry : entryOK P = true) {B : Block}
    (hB : P.block? P.entry = some B) {t : Ty} {x : Nat} {arms : PhiArms}
    (hc : Cmd.phi t x arms ∈ B.cmds) : False := by
  have harms := phiOK_at hphi hB hc
  simp only [phiArmsOK, Bool.and_eq_true] at harms
  obtain ⟨⟨hne, -⟩, hall⟩ := harms
  cases arms with
  | nil => simp at hne
  | cons a rest =>
      have := List.all_eq_true.mp hall a (List.mem_cons_self ..)
      obtain ⟨p, s⟩ := a
      simp only [Bool.and_eq_true, decide_eq_true_eq] at this
      have h0 := entry_eq_zero hentry
      rw [h0] at this
      exact absurd this.1 (Nat.not_lt_zero p)

theorem chained_of_pairwise {L : List Nat}
    (h : List.Pairwise (· < ·) L) : Chained (· < ·) L := by
  induction L with
  | nil => trivial
  | cons a rest ih =>
      cases rest with
      | nil => trivial
      | cons b rest' =>
          rw [List.pairwise_cons] at h
          exact ⟨h.1 b (List.mem_cons_self ..), ih h.2⟩

/-- Key-nodup arms look up any member arm exactly. -/
theorem lookup_of_mem_nodup {arms : PhiArms} {p src : Nat}
    (hmem : (p, src) ∈ arms) (hnd : (arms.map (·.1)).Nodup) :
    lookupArm arms p = some src := by
  induction arms with
  | nil => cases hmem
  | cons a rest ih =>
      obtain ⟨q, s⟩ := a
      rw [List.map_cons, List.nodup_cons] at hnd
      cases hb : (p == q) with
      | true =>
          have hpq : p = q := beq_iff_eq.mp hb
          subst hpq
          rcases List.mem_cons.mp hmem with heq | hrest
          · obtain ⟨-, rfl⟩ := Prod.mk.injEq .. |>.mp heq
            simp only [lookupArm, List.lookup, hb]
          · exact absurd (List.mem_map.mpr ⟨(p, src), hrest, rfl⟩) hnd.1
      | false =>
          have hpq : p ≠ q := fun h => by rw [h] at hb; simp at hb
          rcases List.mem_cons.mp hmem with heq | hrest
          · exact absurd (congrArg Prod.fst heq) hpq
          · simpa only [lookupArm, List.lookup, hb] using ih hrest hnd.2

/-! ## Guard evaluation at the denotational state -/

theorem active_guard_true {P : Program} {s0 : State} {p : Nat}
    (hp : p ∈ activeList P s0) :
    (Vc.guardOf P p).eval (denot P s0) = true := by
  unfold Vc.guardOf
  split
  · rfl
  · exact (mem_activeList.mp hp).2

theorem inactive_guard_false {P : Program} {s0 : State} {q : Nat}
    (hq : q ∉ activeList P s0) (hqe : q ≠ P.entry)
    (hqlen : q < P.blocks.length) :
    (Vc.guardOf P q).eval (denot P s0) = false := by
  unfold Vc.guardOf
  rw [if_neg hqe]
  show (denot P s0).blks q = false
  rw [denot_hblk hqlen]
  exact decide_eq_false hq

/-- The active predecessor of any block is unique: two would violate
the at-most-one-visited-predecessor fact of the taken-edge chain. -/
theorem active_pred_unique {P : Program} {s0 : State}
    (hwf : WellFormed P) {v : Nat} (hv : v < P.blocks.length) {p q : Nat}
    (hpA : p ∈ activeList P s0) (hpp : p ∈ predsOf P v)
    (hqA : q ∈ activeList P s0) (hqp : q ∈ predsOf P v) : q = p := by
  by_cases hqp' : q = p
  · exact hqp'
  · exact visited_amo hwf.fwd hwf.amo (denot_hedge hwf) hv
      (two_mem_le_length hqp hpp hqp') hqA hqp hpA hpp

/-! ## The phi step: the taken predecessor's arm carries the fold value -/

/-- At an active phi block whose taken predecessor is `p`, coverage
gives `p` an arm, and the fold's `phiRhs` selects exactly that arm's
source (the taken predecessor is the unique active one). So the
operational `Step.phi` write is a self-write. -/
theorem phi_step_value {P : Program} {s0 : State}
    (hwf : WellFormed P) (hcov : phiCoversOK P = true)
    {v : Nat} {B : Block} (hB : P.block? v = some B)
    (hvA : v ∈ activeList P s0)
    {t : Ty} {x : Nat} {arms : PhiArms}
    (hc : Cmd.phi t x arms ∈ B.cmds)
    {p : Nat} (hpA : p ∈ activeList P s0)
    (hpv : EdgeTaken P (denot P s0) p v) :
    ∃ src, lookupArm arms p = some src
      ∧ (denot P s0).regs t x = (denot P s0).regs t src := by
  have harms := phiOK_at hwf.phi hB hc
  obtain ⟨cond, hcondmem, -⟩ := hpv.edge_cond
  have hppred : p ∈ predsOf P v := mem_predsOf.mpr ⟨cond, hcondmem⟩
  have hpm : p ∈ arms.map (·.1) := phiCovers_at hcov hB hc hppred
  obtain ⟨⟨p', src⟩, hmem', hfst⟩ := List.mem_map.mp hpm
  have hmem : (p, src) ∈ arms := by
    have hp' : p' = p := hfst
    rw [← hp']
    exact hmem'
  have hnd : (arms.map (·.1)).Nodup := by
    simp only [phiArmsOK, Bool.and_eq_true] at harms
    exact of_decide_eq_true harms.1.2
  have hlk := lookup_of_mem_nodup hmem hnd
  refine ⟨src, hlk, ?_⟩
  have hdp := denot_phi (s0 := s0) hwf hB hc
  have hvlen := (mem_activeList.mp hvA).1
  have hgp := active_guard_true hpA
  have hgq : ∀ q s', (q, s') ∈ arms → q ≠ p →
      (Vc.guardOf P q).eval (denot P s0) = false := by
    intro q s' hqarm hqne
    have hqpred := phiArm_pred harms hqarm
    have hqA : q ∉ activeList P s0 := fun hqA =>
      hqne (active_pred_unique hwf hvlen hpA hppred hqA hqpred)
    have hqe : q ≠ P.entry := fun h => by
      obtain ⟨he, -⟩ := denot_hentry hwf.fwd hwf.uses hvA
      exact hqA (h ▸ he)
    exact inactive_guard_false hqA hqe
      (Nat.lt_trans (pred_lt hwf.fwd hqpred) hvlen)
  cases arms with
  | nil => cases hmem
  | cons a rest =>
      rw [hdp]
      exact phiChain_eval_select a rest hlk hgp hgq

/-- The phi-resolution invariant threaded through the walk: at entry
there is no predecessor to resolve (`phiOK` forbids entry phis);
elsewhere `prev` is the taken-edge active predecessor. -/
abbrev PrevOK (P : Program) (s0 : State) (prev : Option Nat) (v : Nat) : Prop :=
  v = P.entry ∨ ∃ p, prev = some p ∧ p ∈ activeList P s0
    ∧ EdgeTaken P (denot P s0) p v

/-! ## The command walk: every write is a self-write -/

/-- Fuel-carrying core of `cmds_run`. -/
theorem cmds_run_go {P : Program} {s0 : State}
    (hwf : WellFormed P) (hcov : phiCoversOK P = true)
    {v : Nat} {B : Block} (hB : P.block? v = some B)
    (hvA : v ∈ activeList P s0) {prev : Option Nat}
    (hprev : PrevOK P s0 prev v)
    {k : Nat} (hk : k ≤ B.cmds.length)
    (hnoassert : ∀ (i : Nat) (c : Cmd), B.cmds[i]? = some c → i < k →
      ∀ r, c ≠ .assert r) :
    ∀ (n j : Nat), k ≤ j + n → j ≤ k →
      Steps P (.running v j prev (denot P s0))
        (.running v k prev (denot P s0)) := by
  intro n
  induction n with
  | zero =>
      intro j h1 h2
      obtain rfl : j = k := Nat.le_antisymm h2 (by omega)
      exact Relation.ReflTransGen.refl
  | succ n ih =>
      intro j h1 h2
      by_cases hjk : j = k
      · subst hjk; exact Relation.ReflTransGen.refl
      have hjlt : j < k := Nat.lt_of_le_of_ne h2 hjk
      have hjlen : j < B.cmds.length := by omega
      obtain ⟨c, hcj⟩ : ∃ c, B.cmds[j]? = some c :=
        ⟨_, List.getElem?_eq_getElem hjlen⟩
      have hrest : Steps P (.running v (j + 1) prev (denot P s0))
          (.running v k prev (denot P s0)) := ih (j + 1) (by omega) (by omega)
      cases c with
      | assign t x e =>
          have hself : (denot P s0).upd t x (e.eval (denot P s0))
              = denot P s0 := by
            rw [← denot_assign hwf hB hcj]
            exact State.upd_self ..
          have step : Step P (.running v j prev (denot P s0))
              (.running v (j + 1) prev (denot P s0)) := by
            have h := Step.assign (P := P) (prev := prev) (s := denot P s0) hB hcj
            rwa [hself] at h
          exact Relation.ReflTransGen.head step hrest
      | havoc t x =>
          have step : Step P (.running v j prev (denot P s0))
              (.running v (j + 1) prev (denot P s0)) := by
            have h := Step.havoc (P := P) (prev := prev) (s := denot P s0)
              ((denot P s0).regs t x) hB hcj
            rwa [State.upd_self] at h
          exact Relation.ReflTransGen.head step hrest
      | phi t x arms =>
          rcases hprev with hve | ⟨p, hpeq, hpA, hpv⟩
          · exact (no_phi_in_entry hwf.phi hwf.entry (hve ▸ hB)
              (List.mem_of_getElem? hcj)).elim
          · obtain ⟨src, hlk, hval⟩ := phi_step_value hwf hcov hB hvA (List.mem_of_getElem? hcj) hpA hpv
            subst hpeq
            have step : Step P (.running v j (some p) (denot P s0))
                (.running v (j + 1) (some p) (denot P s0)) := by
              have h := Step.phi (P := P) (s := denot P s0) hB hcj hlk
              rwa [← hval, State.upd_self] at h
            exact Relation.ReflTransGen.head step hrest
      | «assume» φ =>
          have hev := denot_assume hwf.uses hwf.gf hB hcj (mem_activeList.mp hvA).2
          exact Relation.ReflTransGen.head (Step.assume hB hcj hev) hrest
      | assert r =>
          exact (hnoassert j _ hcj hjlt r rfl).elim

/-- Walk an active block's commands from `j` up to `k` (no asserts in
`[0, k)`): each step writes the value the state already holds, so the
state is `denot P s0` throughout. -/
theorem cmds_run {P : Program} {s0 : State}
    (hwf : WellFormed P) (hcov : phiCoversOK P = true)
    {v : Nat} {B : Block} (hB : P.block? v = some B)
    (hvA : v ∈ activeList P s0) {prev : Option Nat}
    (hprev : PrevOK P s0 prev v)
    {k : Nat} (hk : k ≤ B.cmds.length)
    (hnoassert : ∀ (i : Nat) (c : Cmd), B.cmds[i]? = some c → i < k →
      ∀ r, c ≠ .assert r)
    {j : Nat} (hj : j ≤ k) :
    Steps P (.running v j prev (denot P s0))
      (.running v k prev (denot P s0)) :=
  cmds_run_go hwf hcov hB hvA hprev hk hnoassert k j (by omega) hj

/-- The failing assert site, packaged: the single assert's block/index/
condition register, the site facts, and the two denotational failure
facts (`ok_false`, `active`). Built once in `coadequacy_of_wf` from
`singleAssert_shape` + `denot_fail`, then threaded through the walk. -/
structure FailSite (P : Program) (s0 : State) where
  blk : Nat
  idx : Nat
  reg : Nat
  B : Block
  sites : Vc.assertSites P = [(blk, idx, reg)]
  hB : P.block? blk = some B
  cmd : B.cmds[idx]? = some (.assert reg)
  last : idx + 1 = B.cmds.length
  ok_false : (denot P s0).regs .bool reg = false
  active : blk ∈ activeList P s0

/-- The assert block itself: walk to the assert and fire `assertFalse`. -/
theorem assert_block_run {P : Program} {s0 : State}
    (hwf : WellFormed P) (hcov : phiCoversOK P = true)
    (F : FailSite P s0) (prev : Option Nat)
    (hprev : PrevOK P s0 prev F.blk) :
    Steps P (.running F.blk 0 prev (denot P s0)) (.failed (denot P s0)) := by
  obtain ⟨aB, iA, okReg, Bf, hsites, hBf, hcf, hlenA, hok, hvA⟩ := F
  have hnoassert : ∀ (i : Nat) (c : Cmd), Bf.cmds[i]? = some c → i < iA →
      ∀ r, c ≠ .assert r := by
    intro i c hci hilt r hceq
    subst hceq
    have hmem : (aB, i, r) ∈ Vc.assertSites P :=
      mem_assertSites.mpr ⟨Bf, hBf, hci⟩
    rw [hsites] at hmem
    have h := List.mem_singleton.mp hmem
    simp only [Prod.mk.injEq] at h
    omega
  have hrun0 := cmds_run hwf hcov
    hBf hvA hprev (by omega) hnoassert (j := 0) (Nat.zero_le _)
  exact hrun0.tail (Step.assertFalse hBf hcf hok)

/-! ## The chain walk: follow the taken edges down to the assert block -/

/-- Fuel-carrying core of `chain_run`. -/
theorem chain_run_go {P : Program} {s0 : State}
    (hwf : WellFormed P) (hcov : phiCoversOK P = true)
    (F : FailSite P s0) :
    ∀ (n v : Nat), F.blk - v ≤ n → v ∈ activeList P s0 → v ≤ F.blk →
      ∀ (prev : Option Nat), PrevOK P s0 prev v →
        Steps P (.running v 0 prev (denot P s0)) (.failed (denot P s0)) := by
  obtain ⟨aB, iA, okReg, Bf, hsites, hBf, hcf, hlenA, hok, haBA⟩ := F
  dsimp only
  intro n
  induction n with
  | zero =>
      intro v hfuel hvA hvle prev hprev
      obtain rfl : v = aB := by omega
      exact assert_block_run hwf hcov
        ⟨v, iA, okReg, Bf, hsites, hBf, hcf, hlenA, hok, hvA⟩ prev hprev
  | succ n ih =>
      intro v hfuel hvA hvle prev hprev
      by_cases hveq : v = aB
      · subst hveq
        exact assert_block_run hwf hcov
          ⟨v, iA, okReg, Bf, hsites, hBf, hcf, hlenA, hok, hvA⟩ prev hprev
      have hvlt : v < aB := Nat.lt_of_le_of_ne hvle hveq
      have hvlen := (mem_activeList.mp hvA).1
      obtain ⟨B, hB⟩ : ∃ B, P.block? v = some B :=
        ⟨_, List.getElem?_eq_getElem hvlen⟩
      have hnoassert : ∀ (i : Nat) (c : Cmd), B.cmds[i]? = some c →
          i < B.cmds.length → ∀ r, c ≠ .assert r := by
        intro i c hci _ r hceq
        subst hceq
        have hmem : (v, i, r) ∈ Vc.assertSites P :=
          mem_assertSites.mpr ⟨B, hB, hci⟩
        rw [hsites] at hmem
        have h := List.mem_singleton.mp hmem
        simp only [Prod.mk.injEq] at h
        exact hveq h.1
      have hrun0 := cmds_run hwf hcov
        hB hvA hprev le_rfl hnoassert (j := 0) (Nat.zero_le _)
      have hchain := denot_hedge (s0 := s0) hwf
      have hlt := chained_of_pairwise (activeList_pairwise P s0)
      obtain ⟨z, hz⟩ : ∃ z, (activeList P s0).getLast? = some z := by
        cases hz : (activeList P s0).getLast? with
        | some z => exact ⟨z, rfl⟩
        | none =>
            rw [List.getLast?_eq_none_iff] at hz
            rw [hz] at hvA
            cases hvA
      have hvz : v ≠ z := by
        have hle := chained_le_getLast hlt hz aB haBA
        omega
      obtain ⟨n', hn'A, hedge_vn'⟩ := chained_next_mem hchain hz hvA hvz
      have hn'le : n' ≤ aB := by
        rcases chained_next hchain hlt hvA with hmax | ⟨m, hm, hbound⟩
        · exact absurd (hmax aB haBA) (by omega)
        · have hmn : m = n' := edgeTaken_unique hm hedge_vn'
          rcases hbound aB haBA with h | h
          · omega
          · omega
      have hvn' : v < n' := EdgeTaken.lt hwf.fwd hedge_vn'
      have hstep : Step P (.running v B.cmds.length prev (denot P s0))
          (.running n' 0 (some v) (denot P s0)) := by
        obtain ⟨B', hB', hterm⟩ := hedge_vn'
        obtain rfl : B' = B := by
          have h := hB.symm.trans hB'
          exact (Option.some.inj h).symm
        rcases hterm with hgoto | ⟨c, tt, ee, hif, hcase⟩
        · exact Step.goto hB hgoto
        · rcases hcase with ⟨rfl, hc⟩ | ⟨rfl, hc⟩
          · exact Step.ifTrue hB hif hc
          · exact Step.ifFalse hB hif hc
      have hrest := ih n' (by omega) hn'A hn'le (some v)
        (Or.inr ⟨v, rfl, hvA, hedge_vn'⟩)
      exact (hrun0.tail hstep).trans hrest

/-- From any active block at or below the failing one, the run reaches
`.failed`: at the assert block walk the commands and fire
`assertFalse`; below it, walk the commands, take the chain's out-edge
(which cannot overshoot the assert block), recurse. -/
theorem chain_run {P : Program} {s0 : State}
    (hwf : WellFormed P) (hcov : phiCoversOK P = true)
    (F : FailSite P s0) {v : Nat} (hvA : v ∈ activeList P s0)
    (hvle : v ≤ F.blk) (prev : Option Nat) (hprev : PrevOK P s0 prev v) :
    Steps P (.running v 0 prev (denot P s0)) (.failed (denot P s0)) :=
  chain_run_go hwf hcov F F.blk v (by omega) hvA hvle prev hprev

/-! ## Assembly: the converse, and the completed equivalence -/

theorem coadequacy_of_wf {P : Program} (hwf : WellFormed P)
    (hcov : phiCoversOK P = true) {s0 : State}
    (hexit : (denot P s0).blks P.blocks.length = true) : P.Unsafe := by
  obtain ⟨aB, iA, okReg, Bf, hsites, hBf, hcf, hlenA⟩ := singleAssert_shape hwf.one
  obtain ⟨haBA, hok⟩ := denot_fail hexit aB iA okReg hsites
  obtain ⟨hentryA, hheadA⟩ := denot_hentry hwf.fwd hwf.uses haBA
  have hElt := chained_of_pairwise (activeList_pairwise P s0)
  have hEle : P.entry ≤ aB := chained_lt_bound hElt hheadA aB haBA
  have hrun := chain_run hwf hcov
    ⟨aB, iA, okReg, Bf, hsites, hBf, hcf, hlenA, hok, haBA⟩
    hentryA hEle none (Or.inl rfl)
  exact ⟨denot P s0, denot P s0, hrun⟩

/-- Converse adequacy: a seed reaching EXIT denotationally exhibits a
real failing execution. Note: dominance (`domClosedOK`) is not needed —
the run is seeded with the fold's own final state, so every write is a
self-write and no cross-state agreement is ever argued. -/
theorem unsafe_of_seed {P : Program} (hwf : wellFormed P = true)
    (hcov : phiCoversOK P = true) (s0 : State)
    (hexit : (denot P s0).blks P.blocks.length = true) : P.Unsafe := by
  obtain ⟨hw, -⟩ := wellFormed_iff.mp hwf
  exact coadequacy_of_wf hw hcov hexit

/-- The complete correspondence: operational unsafety is EXIT
reachability of the denotational fold. `→` is `adequacy`, `←` is the
converse above. -/
theorem unsafe_iff_exit {P : Program} (hwf : wellFormed P = true)
    (hcov : phiCoversOK P = true) :
    P.Unsafe ↔ ∃ s0 : State, (denot P s0).blks P.blocks.length = true :=
  ⟨adequacy hwf, fun ⟨s0, h⟩ => unsafe_of_seed hwf hcov s0 h⟩

/-- The complete formal picture: the operational and denotational
notions of safety coincide. -/
theorem safe_iff_safe_denot {P : Program} (hwf : wellFormed P = true)
    (hcov : phiCoversOK P = true) : P.Safe ↔ Safe_denot P := by
  constructor
  · intro hsafe s0
    cases hb : (denot P s0).blks P.blocks.length with
    | false => rfl
    | true => exact absurd (unsafe_of_seed hwf hcov s0 hb) hsafe
  · exact safe_of_safe_denot (adequacy hwf)

end Ttac
