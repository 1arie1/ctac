import Ttac.VcFacts

/-!
# A prefix (forward-induction) soundness proof

The operational-facts producer and the annotated VC.

`forwardTrace`/`forwardStructural` reduce a failing execution, by one
forward induction over the prefix, to structural facts: the visited
list in execution order, the taken-edge chain, and each executed
command's `CmdFact` at the final state. A formula, once established,
stays true because the only cell a step writes is *fresh* (SSA: its
unique definition site is the current position) — a local, per-step
freeze, no global stability lemma. `VcAdequacy` consumes these facts to
seed the denotational fold.

The `Vc.AnnVC` structure is the site-tagged VC the untrusted annotator
emits (per-block buckets, objective, map definitions); `VcWeaken`'s
`checkVCWAnn` validates it per site against the weakening table.
-/

namespace Ttac

/-- The register state underlying a configuration. -/
def Config.state : Config → State
  | .running _ _ _ s => s
  | .done s => s
  | .failed s => s

/-- Extend a chain by one element at the *end*: the forward induction builds
the visited list in execution order (block entry appends), whereas `Suffix`
prepends. The new last edge must connect the old last element to `x`. -/
theorem chained_append_single {R : Nat → Nat → Prop} :
    ∀ {V : List Nat} {x : Nat}, Chained R V →
      (∀ z, V.getLast? = some z → R z x) → Chained R (V ++ [x])
  | [], _, _, _ => trivial
  | [a], x, _, hlast => by
      simpa [Chained] using hlast a rfl
  | a :: b :: rest, x, hch, hlast => by
      obtain ⟨hab, hch'⟩ := hch
      refine ⟨hab, chained_append_single hch' (fun z hz => hlast z ?_)⟩
      rw [List.getLast?_cons_cons] at *
      exact hz

/-- A register whose definitions all lie before position `(v, i+1)` is not the
cell written at a strictly-later position `(b, pc)`. -/
theorem write_ne_of_before {P : Program} {p : Ty × Nat} {v i b pc : Nat}
    (hlt : posLt (v, i) (b, pc) = true)
    (hp : ∀ d j, IsDefAt P p d j → posLt (d, j) (v, i + 1) = true)
    {t : Ty} {y : Nat} (hydef : IsDefAt P (t, y) b pc) : p ≠ (t, y) := by
  intro heq; subst heq
  have hc := hp b pc hydef
  simp only [posLt, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hlt hc
  omega

/-- A command's coverage fact is unaffected by a write at a strictly-later
position: target and read registers are defined at-or-before the command, so
SSA keeps them distinct from the fresh cell. One case per command kind. -/
theorem cmdFact_freeze {P : Program} (hssa : ssaOK P = true)
    (huse : usesOK P = true) (hphi : phiOK P = true) {v i : Nat} {Bv : Block}
    {c' : Cmd} (hBv : P.block? v = some Bv) (hci : Bv.cmds[i]? = some c')
    {b pc : Nat} (hlt : posLt (v, i) (b, pc) = true)
    {t : Ty} {y : Nat} (hydef : IsDefAt P (t, y) b pc) (val : t.denote)
    {s : State} {prev : Option Nat} (hcf : CmdFact s prev c') :
    CmdFact (s.upd t y val) prev c' := by
  have hu := usesOK_cmd huse hBv hci
  simp only [cmdUsesOK] at hu
  cases c' with
  | assign t' y' e' =>
      simp only [CmdFact] at hcf ⊢
      have hy'ne : (t', y') ≠ (t, y) :=
        write_ne_of_before hlt (fun d j hdj => by
          obtain ⟨rfl, rfl⟩ := ssa_unique hssa ⟨Bv, _, hBv, hci, rfl⟩ hdj
          simp [posLt]) hydef
      have hev : e'.eval (s.upd t y val) = e'.eval s :=
        eval_congr e' (fun p hp => State.upd_regs_of_ne s
          (write_ne_of_before hlt
            (fun d j hdj => posLt_succ (expUsesOK_before hu p hp d j hdj)) hydef) val)
          (fun q _ => by rw [State.upd_blks])
      rw [State.upd_regs_of_ne s hy'ne val, hev]; exact hcf
  | havoc t' y' => trivial
  | phi t' y' arms =>
      simp only [CmdFact] at hcf ⊢
      obtain ⟨p, src, hprev, harm, heq⟩ := hcf
      have harms : phiArmsOK P v arms := phiOK_at hphi hBv (List.mem_of_getElem? hci)
      have hy'ne : (t', y') ≠ (t, y) :=
        write_ne_of_before hlt (fun d j hdj => by
          obtain ⟨rfl, rfl⟩ := ssa_unique hssa ⟨Bv, _, hBv, hci, rfl⟩ hdj
          simp [posLt]) hydef
      have hsrcne : (t', src) ≠ (t, y) :=
        write_ne_of_before hlt (fun d j hdj => by
          have hdp := armUseOK_le (List.all_eq_true.mp hu (p, src) (lookup_mem harm)) d j hdj
          have hpv := phiArm_lt harms (lookup_mem harm)
          simp only [posLt, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
          omega) hydef
      exact ⟨p, src, hprev, harm, by
        rw [State.upd_regs_of_ne s hy'ne val, State.upd_regs_of_ne s hsrcne val]; exact heq⟩
  | assume φ =>
      simp only [CmdFact] at hcf ⊢
      rw [eval_congr φ (fun p hp => State.upd_regs_of_ne s
        (write_ne_of_before hlt
          (fun d j hdj => posLt_succ (expUsesOK_before hu p hp d j hdj)) hydef) val)
        (fun q _ => by rw [State.upd_blks])]
      exact hcf
  | assert r =>
      simp only [CmdFact] at hcf ⊢
      rw [State.upd_regs_of_ne s (write_ne_of_before hlt
        (fun d j hdj => posLt_succ (useOK_before hu d j hdj)) hydef) val]
      exact hcf

/-- A taken edge whose source block is strictly before `b` survives a write at
`(b, pc)`: the branch register is read at the source's terminator, hence
defined earlier, hence distinct from the fresh cell. -/
theorem edgeTaken_freeze {P : Program}
    (huse : usesOK P = true) {s : State} {u w : Nat} (hE : EdgeTaken P s u w)
    {b pc : Nat} (hub : u < b) {t : Ty} {y : Nat}
    (hydef : IsDefAt P (t, y) b pc) (val : t.denote) :
    EdgeTaken P (s.upd t y val) u w := by
  obtain ⟨B, hB, hshape⟩ := hE
  refine ⟨B, hB, ?_⟩
  rcases hshape with hgoto | ⟨c, th, el, hif, harm⟩
  · exact Or.inl hgoto
  · have hut := usesOK_term huse hB
    rw [termUsesOK, hif] at hut
    have hcne : (Ty.bool, c) ≠ (t, y) :=
      write_ne_of_before (show posLt (u, B.cmds.length) (b, pc) = true by
        simp only [posLt, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]; omega)
        (fun d j hdj => posLt_succ (useOK_before hut d j hdj)) hydef
    refine Or.inr ⟨c, th, el, hif, ?_⟩
    rw [State.upd_regs_of_ne s hcne val]; exact harm

/-- The whole taken-edge chain survives a write: every edge source is a
non-last block, hence `< b`. -/
theorem chained_edgeTaken_upd {P : Program}
    (huse : usesOK P = true) (hfwd : forwardOK P = true) {s : State}
    {t : Ty} {y : Nat} {b pc : Nat} (hydef : IsDefAt P (t, y) b pc)
    (val : t.denote) :
    ∀ {V : List Nat}, (∀ q ∈ V, q ≤ b) → Chained (EdgeTaken P s) V →
      Chained (EdgeTaken P (s.upd t y val)) V
  | [], _, _ => trivial
  | [_], _, _ => trivial
  | a :: w :: rest, hmax, ⟨hE, hch⟩ => by
      have haw : a < w := hE.lt hfwd
      have hwb : w ≤ b := hmax w (by simp)
      exact ⟨edgeTaken_freeze huse hE (Nat.lt_of_lt_of_le haw hwb) hydef val,
        chained_edgeTaken_upd huse hfwd hydef val
          (fun q hq => hmax q (List.mem_cons_of_mem _ hq)) hch⟩

/-- The visited list, in execution order and strictly increasing (from the
edge chain), has the entry block (= block 0) as its head. -/
theorem head_eq_entry {P : Program} {σ : State} (hentry : entryOK P = true)
    (hfwd : forwardOK P = true) {V : List Nat}
    (hedge : Chained (EdgeTaken P σ) V) (hentryV : P.entry ∈ V) :
    V.head? = some P.entry := by
  have h0 : P.entry = 0 := by
    simp only [entryOK, Bool.and_eq_true, decide_eq_true_eq] at hentry; exact hentry.1
  have hltc : Chained (· < ·) V := hedge.imp fun a b h => h.lt hfwd
  cases V with
  | nil => simp at hentryV
  | cons hd tl =>
      have hle := chained_lt_bound hltc (a := hd) rfl P.entry hentryV
      rw [h0] at hle
      simp only [List.head?_cons, Option.some.injEq]
      omega

/-- The forward *write step*, factored once: given the trace facts before a
register write at `(b, pc)` and the new command's own coverage fact `hnew`,
the trace facts hold after it. All the preservation — the edge chain
(`chained_edgeTaken_upd`), the current-block entry edge, and every earlier
command's fact (`cmdFact_freeze`) — happens here, so the `assign`/`havoc`/`phi`
cases only supply `hnew`. This is "the step is simple," made literal. -/
theorem forwardTrace_write {P : Program} (hssa : ssaOK P = true)
    (huse : usesOK P = true) (hfwd : forwardOK P = true) (hphi : phiOK P = true)
    {b pc : Nat} {prev : Option Nat} {s : State} {B : Block} {t : Ty} {y : Nat}
    {cmd0 : Cmd} (v : t.denote)
    (hB : P.block? b = some B) (hc0 : B.cmds[pc]? = some cmd0)
    (hydef : IsDefAt P (t, y) b pc)
    {V : List Nat} (hentV : P.entry ∈ V) (hgl : V.getLast? = some b)
    (hmax : ∀ q ∈ V, q ≤ b) (hedge : Chained (EdgeTaken P s) V)
    (hpe : ∀ p, prev = some p → p ∈ V ∧ EdgeTaken P s p b)
    (hfacts : ∀ v' i Bv c', P.block? v' = some Bv → Bv.cmds[i]? = some c' →
      v' ∈ V → posLt (v', i) (b, pc) = true → (∀ r, c' ≠ .assert r) →
      ∃ prevv, CmdFact s prevv c'
        ∧ ∀ p, prevv = some p → p ∈ V ∧ EdgeTaken P s p v')
    (hnew : CmdFact (s.upd t y v) prev cmd0) :
    ∃ V' : List Nat, P.entry ∈ V' ∧ V'.getLast? = some b ∧ (∀ q ∈ V', q ≤ b)
      ∧ Chained (EdgeTaken P (s.upd t y v)) V'
      ∧ (∀ p, prev = some p → p ∈ V' ∧ EdgeTaken P (s.upd t y v) p b)
      ∧ (∀ v' i Bv c', P.block? v' = some Bv → Bv.cmds[i]? = some c' →
          v' ∈ V' → posLt (v', i) (b, pc + 1) = true → (∀ r, c' ≠ .assert r) →
          ∃ prevv, CmdFact (s.upd t y v) prevv c'
            ∧ ∀ p, prevv = some p → p ∈ V' ∧ EdgeTaken P (s.upd t y v) p v') := by
  have hpe' : ∀ p, prev = some p → p ∈ V ∧ EdgeTaken P (s.upd t y v) p b :=
    fun p hp => ⟨(hpe p hp).1,
      edgeTaken_freeze huse (hpe p hp).2 ((hpe p hp).2.lt hfwd) hydef _⟩
  refine ⟨V, hentV, hgl, hmax,
    chained_edgeTaken_upd huse hfwd hydef _ hmax hedge, hpe', ?_⟩
  intro v' i Bv c' hBv hci hvV hlt hna
  rcases show posLt (v', i) (b, pc) = true ∨ (v' = b ∧ i = pc) by
    simp only [posLt, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hlt ⊢
    omega with hold | ⟨rfl, rfl⟩
  · obtain ⟨prevv, hcf, hec⟩ := hfacts v' i Bv c' hBv hci hvV hold hna
    exact ⟨prevv, cmdFact_freeze hssa huse hphi hBv hci hold hydef _ hcf,
      fun p hp => ⟨(hec p hp).1, edgeTaken_freeze huse (hec p hp).2
        (Nat.lt_of_lt_of_le ((hec p hp).2.lt hfwd) (hmax v' hvV)) hydef _⟩⟩
  · obtain rfl := Option.some.inj (hBv.symm.trans hB)
    obtain rfl := Option.some.inj (hci.symm.trans hc0)
    exact ⟨prev, hnew, hpe'⟩

/-- The forward *block-entry step*, factored once: taking the edge `b → tgt`
appends `tgt` to the visited list, extends the chain, and re-files the earlier
facts. The `goto`/`ifTrue`/`ifFalse` cases only supply the edge. -/
theorem forwardTrace_enter {P : Program}
    {b tgt : Nat} {s : State} {B : Block}
    (hB : P.block? b = some B) (hlt' : b < tgt) (hEdge : EdgeTaken P s b tgt)
    {V : List Nat} (hentV : P.entry ∈ V) (hgl : V.getLast? = some b)
    (hmax : ∀ q ∈ V, q ≤ b) (hedge : Chained (EdgeTaken P s) V)
    (hfacts : ∀ v' i Bv c', P.block? v' = some Bv → Bv.cmds[i]? = some c' →
      v' ∈ V → posLt (v', i) (b, B.cmds.length) = true → (∀ r, c' ≠ .assert r) →
      ∃ prevv, CmdFact s prevv c'
        ∧ ∀ p, prevv = some p → p ∈ V ∧ EdgeTaken P s p v') :
    ∃ V' : List Nat, P.entry ∈ V' ∧ V'.getLast? = some tgt ∧ (∀ q ∈ V', q ≤ tgt)
      ∧ Chained (EdgeTaken P s) V'
      ∧ (∀ p, some b = some p → p ∈ V' ∧ EdgeTaken P s p tgt)
      ∧ (∀ v' i Bv c', P.block? v' = some Bv → Bv.cmds[i]? = some c' →
          v' ∈ V' → posLt (v', i) (tgt, 0) = true → (∀ r, c' ≠ .assert r) →
          ∃ prevv, CmdFact s prevv c'
            ∧ ∀ p, prevv = some p → p ∈ V' ∧ EdgeTaken P s p v') := by
  refine ⟨V ++ [tgt], List.mem_append.mpr (Or.inl hentV), by simp,
    fun q hq => (List.mem_append.mp hq).elim
      (fun h => Nat.le_of_lt (Nat.lt_of_le_of_lt (hmax q h) hlt'))
      (fun h => Nat.le_of_eq (List.mem_singleton.mp h)),
    chained_append_single hedge (fun z hz => by
      obtain rfl : z = b := Option.some.inj (hz.symm.trans hgl); exact hEdge),
    ?_, ?_⟩
  · intro q hq
    obtain rfl := Option.some.inj hq
    exact ⟨List.mem_append.mpr (Or.inl (List.mem_of_getLast? hgl)), hEdge⟩
  · intro v' i Bv c' hBv hci hvV hlt hna
    have hlt2 : v' < tgt := by
      simp only [posLt, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hlt; omega
    have hv'V : v' ∈ V := (List.mem_append.mp hvV).elim id (fun h => by
      simp only [List.mem_singleton] at h; exact absurd (h ▸ hlt2) (Nat.lt_irrefl _))
    have hile : i < Bv.cmds.length := (List.getElem?_eq_some_iff.mp hci).1
    have hv'b : v' ≤ b := hmax v' hv'V
    have hpos : posLt (v', i) (b, B.cmds.length) = true := by
      have hBvB : v' = b → Bv = B := fun hh => by
        rw [hh] at hBv; exact Option.some.inj (hBv.symm.trans hB)
      simp only [posLt, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      rcases Nat.lt_or_eq_of_le hv'b with hh | rfl
      · exact Or.inl hh
      · exact Or.inr ⟨rfl, by rw [hBvB rfl] at hile; exact hile⟩
    obtain ⟨prevv, hcf, hec⟩ := hfacts v' i Bv c' hBv hci hv'V hpos hna
    exact ⟨prevv, hcf,
      fun p hp => ⟨List.mem_append.mpr (Or.inl (hec p hp).1), (hec p hp).2⟩⟩

/-! ## The forward trace: structural facts by prefix induction

The forward replacement for `suffix_of_steps` + `chain_edge` +
`facts_of_suffix`: at every reachable running configuration, a visited list
`V` (in execution order, so the edge chain reads forward), the current block
last in `V`, the taken-edge chain, the current block's entry connection, and
every executed non-assert command's `CmdFact` with its edge-connected
predecessor. Each step establishes its own new fact and freezes the earlier
ones; block entry appends to `V` and extends the chain. -/

theorem forwardTrace {P : Program} (hssa : ssaOK P = true)
    (huse : usesOK P = true) (hfwd : forwardOK P = true) (hphi : phiOK P = true)
    {s0 : State} {c : Config} (h : Steps P (Config.init P s0) c) :
    ∀ {b pc prev s}, c = .running b pc prev s →
      ∃ V : List Nat, P.entry ∈ V ∧ V.getLast? = some b ∧ (∀ q ∈ V, q ≤ b)
        ∧ Chained (EdgeTaken P s) V
        ∧ (∀ p, prev = some p → p ∈ V ∧ EdgeTaken P s p b)
        ∧ (∀ v i Bv c', P.block? v = some Bv → Bv.cmds[i]? = some c' →
            v ∈ V → posLt (v, i) (b, pc) = true → (∀ r, c' ≠ .assert r) →
            ∃ prevv, CmdFact s prevv c'
              ∧ ∀ p, prevv = some p → p ∈ V ∧ EdgeTaken P s p v) := by
  induction h with
  | refl =>
      intro b pc prev s heq
      rw [Config.init] at heq
      obtain ⟨rfl, rfl, rfl, rfl⟩ := Config.running.inj heq
      refine ⟨[P.entry], List.mem_singleton.mpr rfl, rfl,
        fun q hq => by rw [List.mem_singleton.mp hq], trivial,
        fun p hp => by simp at hp, ?_⟩
      intro v i Bv c' hBv hci hvV hlt hna
      obtain rfl := List.mem_singleton.mp hvV
      simp [posLt] at hlt
  | @tail c1 c2 hpath hstep ih =>
      cases hstep with
      | @assign b pc prev s B t y e hB hc =>
          intro b2 pc2 prev2 s2 heq
          obtain ⟨rfl, rfl, rfl, rfl⟩ := Config.running.inj heq
          obtain ⟨V, hentV, hgl, hmax, hedge, hpe, hfacts⟩ := ih rfl
          have hydef : IsDefAt P (t, y) b pc := ⟨B, _, hB, hc, rfl⟩
          refine forwardTrace_write hssa huse hfwd hphi (e.eval s) hB hc hydef
            hentV hgl hmax hedge hpe hfacts ?_
          have hu := usesOK_cmd huse hB hc
          simp only [cmdUsesOK] at hu
          have hev : e.eval (s.upd t y (e.eval s)) = e.eval s :=
            eval_congr e (fun p hp => State.upd_regs_of_ne s (fun heqp => by
              obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp heqp
              exact defsBefore_no_def_here hydef (expUsesOK_before hu _ hp)) _)
              (fun q _ => by rw [State.upd_blks])
          simp only [CmdFact, State.upd_regs_self, hev]
      | @havoc b pc prev s B t y v hB hc =>
          intro b2 pc2 prev2 s2 heq
          obtain ⟨rfl, rfl, rfl, rfl⟩ := Config.running.inj heq
          obtain ⟨V, hentV, hgl, hmax, hedge, hpe, hfacts⟩ := ih rfl
          exact forwardTrace_write hssa huse hfwd hphi v hB hc
            ⟨B, _, hB, hc, rfl⟩ hentV hgl hmax hedge hpe hfacts trivial
      | @phi b pc p s B t y arms src hB hc harm =>
          intro b2 pc2 prev2 s2 heq
          obtain ⟨rfl, rfl, rfl, rfl⟩ := Config.running.inj heq
          obtain ⟨V, hentV, hgl, hmax, hedge, hpe, hfacts⟩ := ih rfl
          have hydef : IsDefAt P (t, y) b pc := ⟨B, _, hB, hc, rfl⟩
          refine forwardTrace_write hssa huse hfwd hphi (s.regs t src) hB hc hydef
            hentV hgl hmax hedge hpe hfacts ?_
          have hu := usesOK_cmd huse hB hc
          simp only [cmdUsesOK] at hu
          have harms := phiOK_at hphi hB (List.mem_of_getElem? hc)
          have hsrcne : (t, src) ≠ (t, y) := by
            rintro heqp
            obtain ⟨-, rfl⟩ := Prod.mk.injEq .. |>.mp heqp
            have hle := armUseOK_le
              (List.all_eq_true.mp hu (p, src) (lookup_mem harm)) _ _ hydef
            have hpv := phiArm_lt harms (lookup_mem harm)
            omega
          simp only [CmdFact]
          exact ⟨p, src, rfl, harm, by
            rw [State.upd_regs_self, State.upd_regs_of_ne s hsrcne]⟩
      | @assume b pc prev s B φ hB hc hcond =>
          intro b2 pc2 prev2 s2 heq
          obtain ⟨rfl, rfl, rfl, rfl⟩ := Config.running.inj heq
          obtain ⟨V, hentV, hgl, hmax, hedge, hpe, hfacts⟩ := ih rfl
          refine ⟨V, hentV, hgl, hmax, hedge, hpe, ?_⟩
          intro v' i Bv c' hBv hci hvV hlt hna
          rcases show posLt (v', i) (b, pc) = true ∨ (v' = b ∧ i = pc) by
            simp only [posLt, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hlt ⊢
            omega with hold | ⟨rfl, rfl⟩
          · exact hfacts v' i Bv c' hBv hci hvV hold hna
          · obtain rfl := Option.some.inj (hBv.symm.trans hB)
            obtain rfl := Option.some.inj (hci.symm.trans hc)
            exact ⟨prev, hcond, hpe⟩
      | @assertTrue b pc prev s B r hB hc hcond =>
          intro b2 pc2 prev2 s2 heq
          obtain ⟨rfl, rfl, rfl, rfl⟩ := Config.running.inj heq
          obtain ⟨V, hentV, hgl, hmax, hedge, hpe, hfacts⟩ := ih rfl
          refine ⟨V, hentV, hgl, hmax, hedge, hpe, ?_⟩
          intro v' i Bv c' hBv hci hvV hlt hna
          rcases show posLt (v', i) (b, pc) = true ∨ (v' = b ∧ i = pc) by
            simp only [posLt, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hlt ⊢
            omega with hold | ⟨rfl, rfl⟩
          · exact hfacts v' i Bv c' hBv hci hvV hold hna
          · obtain rfl := Option.some.inj (hBv.symm.trans hB)
            exact absurd (Option.some.inj (hci.symm.trans hc)) (hna r)
      | @assertFalse b pc prev s B r hB hc hcond =>
          intro b2 pc2 prev2 s2 heq; nomatch heq
      | @halt b prev s B hB hterm =>
          intro b2 pc2 prev2 s2 heq; nomatch heq
      | @goto b prev s B tgt hB hterm =>
          intro b2 pc2 prev2 s2 heq
          obtain ⟨hbeq, rfl, rfl, rfl⟩ := Config.running.inj heq
          subst b2
          obtain ⟨V, hentV, hgl, hmax, hedge, -, hfacts⟩ := ih rfl
          exact forwardTrace_enter hB
            (forward_target hfwd hB (by rw [hterm]; exact List.mem_singleton.mpr rfl)).1
            ⟨B, hB, Or.inl hterm⟩ hentV hgl hmax hedge hfacts
      | @ifTrue b prev s B r tgt el hB hterm hcond =>
          intro b2 pc2 prev2 s2 heq
          obtain ⟨hbeq, rfl, rfl, rfl⟩ := Config.running.inj heq
          subst b2
          obtain ⟨V, hentV, hgl, hmax, hedge, -, hfacts⟩ := ih rfl
          exact forwardTrace_enter hB
            (forward_target hfwd hB (by rw [hterm]; simp [termTargets])).1
            ⟨B, hB, Or.inr ⟨r, tgt, el, hterm, Or.inl ⟨rfl, hcond⟩⟩⟩
            hentV hgl hmax hedge hfacts
      | @ifFalse b prev s B r th tgt hB hterm hcond =>
          intro b2 pc2 prev2 s2 heq
          obtain ⟨hbeq, rfl, rfl, rfl⟩ := Config.running.inj heq
          subst b2
          obtain ⟨V, hentV, hgl, hmax, hedge, -, hfacts⟩ := ih rfl
          exact forwardTrace_enter hB
            (forward_target hfwd hB (by rw [hterm]; simp [termTargets])).1
            ⟨B, hB, Or.inr ⟨r, th, tgt, hterm, Or.inr ⟨rfl, hcond⟩⟩⟩
            hentV hgl hmax hedge hfacts

/-- **From a failing execution to the structural facts**, forward. Splits off
the final `assertFalse` step and runs `forwardTrace` on the prefix, packaging
its output into exactly the shape the encoding-generic soundness leaves
consume: the visited list (head = entry), the taken-edge chain, per-command
`CmdFact`s (the assert's `cond = false` comes from the fail step), and the
failing-block record. The forward replacement for `suffix_of_steps` +
`Suffix.chain_edge` + `Suffix.head` + `facts_of_suffix` + `Suffix.last_block`. -/
theorem forwardStructural {P : Program} (hone : singleAssertOK P = true)
    (hssa : ssaOK P = true) (huse : usesOK P = true) (hfwd : forwardOK P = true)
    (hphi : phiOK P = true) (hentry : entryOK P = true)
    {s0 σ : State} (hrun : Steps P (Config.init P s0) (.failed σ)) :
    ∃ V : List Nat, P.entry ∈ V ∧ V.head? = some P.entry
      ∧ Chained (EdgeTaken P σ) V
      ∧ (∀ v ∈ V, ∀ (B : Block) (i : Nat) (c' : Cmd),
          P.block? v = some B → B.cmds[i]? = some c' →
          ∃ prev : Option Nat, CmdFact σ prev c'
            ∧ ∀ p, prev = some p → p ∈ V ∧ EdgeTaken P σ p v)
      ∧ (∃ (bf : Nat) (Bf : Block) (pcf cf : Nat), V.getLast? = some bf
          ∧ P.block? bf = some Bf ∧ Bf.cmds[pcf]? = some (.assert cf)
          ∧ σ.regs .bool cf = false) := by
  rcases hrun.cases_tail with h | ⟨cmid, hpre, hstep⟩
  · exact absurd h.symm (by simp [Config.init])
  · cases hstep with
    | @assertFalse bf pcf prev s Bf cf hBf hcf hfalse =>
        obtain ⟨V, hentV, hgl, hmax, hedge, hpe, hfacts⟩ :=
          forwardTrace hssa huse hfwd hphi hpre rfl
        refine ⟨V, hentV, head_eq_entry hentry hfwd hedge hentV, hedge, ?_,
          ⟨bf, Bf, pcf, cf, hgl, hBf, hcf, hfalse⟩⟩
        intro v hvV B i c' hB hci
        by_cases hass : ∃ r, c' = .assert r
        · obtain ⟨r, rfl⟩ := hass
          obtain ⟨rfl, rfl, rfl⟩ := singleAssert_unique hone hB hci hBf hcf
          exact ⟨prev, by simp only [CmdFact]; exact hfalse, hpe⟩
        · have hna : ∀ r, c' ≠ .assert r := fun r hr => hass ⟨r, hr⟩
          have hpos : posLt (v, i) (bf, pcf) = true := by
            rcases Nat.lt_or_eq_of_le (hmax v hvV) with hh | rfl
            · simp only [posLt, Bool.or_eq_true, decide_eq_true_eq]; exact Or.inl hh
            · have hipcf : i < pcf := by
                obtain ⟨aB, iA, okReg, BA, heqs, hBA, hcA, hlastA⟩ := singleAssert_shape hone
                obtain ⟨hba, hpi, -⟩ := singleAssert_unique hone hBf hcf hBA hcA
                have hBBf : B = Bf := Option.some.inj (hB.symm.trans hBf)
                have hBABf : BA = Bf := by
                  rw [← hba] at hBA; exact Option.some.inj (hBA.symm.trans hBf)
                have hipc : i ≠ pcf := fun hh => by
                  rw [hh, hBBf] at hci; exact hna cf (Option.some.inj (hci.symm.trans hcf))
                have hilen : i < B.cmds.length := (List.getElem?_eq_some_iff.mp hci).1
                rw [hBBf] at hilen; rw [hBABf] at hlastA
                omega
              simp [posLt, hipcf]
          exact hfacts v i B c' hB hci hvV hpos hna

/-! ## The annotated VC

An untrusted, pre-bucketed VC: per block, its CFG constraints, its
per-command constraints, and its map definitions; plus the objective.
Blocks are listed in program (topological) order, index `= ` block
index. The checker validates each bucket *locally* against the tagged
site's own generators, so the soundness proof consumes the structure
rather than searching for the site that produced each entry. -/

namespace Vc

/-- The CFG constraints the encoder emits for a single block `S` — the body of
`cfgConstraints`'s map, factored so it can serve as the per-block spec. -/
def cfgConstraintsFor (P : Program) (S : Nat) : List BExp :=
  if S = P.entry then []
  else
    let ins := edgesTo P S
    let gS := guardOf P S
    let edgeTerms := ins.map fun (p, cond) => mkAnd2 (guardOf P p) cond
    let predTerms := ins.map fun (p, _) => guardOf P p
    mkImp gS (mkOr edgeTerms)
      :: mkImp gS (mkOr predTerms)
      :: (amoClauses predTerms).map (mkImp gS)

theorem cfgConstraints_eq (P : Program) :
    cfgConstraints P =
      ((List.range P.blocks.length).map (cfgConstraintsFor P)).flatten := rfl

/-- One block's annotated buckets: its CFG constraints, per command that
command's constraints, and the block's map definitions. -/
structure BlockBucket where
  cfg : List BExp
  cmds : List (List BExp)
  maps : List (Nat × MExp)
deriving Repr, DecidableEq

/-- The whole annotated VC: per-block buckets (in block-index order) and
the objective. Map definitions live in their blocks' buckets. -/
structure AnnVC where
  perBlock : List BlockBucket
  objective : List BExp
deriving Repr, DecidableEq

/-- The plain constraint list an annotated VC denotes (buckets flattened, then
the objective). The map definitions stay separate, as in `Vc.VC`. -/
def AnnVC.flatten (a : AnnVC) : List BExp :=
  (a.perBlock.map fun bk => bk.cfg ++ bk.cmds.flatten).flatten ++ a.objective

/-- The flat map-definition list an annotated VC denotes. -/
def AnnVC.mapDefs (a : AnnVC) : List (Nat × MExp) :=
  (a.perBlock.map (·.maps)).flatten

/-- Satisfaction: every flattened constraint is true and every map definition
holds as a `Prop`-level function equality. -/
def AnnVC.Sat (w : State) (a : AnnVC) : Prop :=
  (∀ c ∈ a.flatten, c.eval w = true)
    ∧ ∀ md ∈ a.mapDefs, w.regs .map md.1 = md.2.eval w

def AnnVC.Unsat (a : AnnVC) : Prop := ¬∃ w, a.Sat w

end Vc

end Ttac
