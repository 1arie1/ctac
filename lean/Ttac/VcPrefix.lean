import Ttac.VcTrace
import Ttac.VcReplay
import Ttac.DefExt
import Ttac.VcSound

/-!
# A prefix (forward-induction) soundness proof

An experiment, parallel to the suffix-oriented `checkVC_sound`: re-prove that
a validated VC implies `Program.Safe`, but by *forward* induction that carries
the state along the execution. Two levers keep the proof close to the shape of
execution:

* the VC read as a **stepping accumulator** — constraints accumulated in
  buckets as the program steps, with the invariant "the current state
  satisfies the current accumulation." A formula, once established, stays true
  because the only cell a step writes is *fresh* (SSA: its unique definition
  site is the current position), so it is not among any already-collected
  constraint's variables — a local, per-step freeze, no final-state stability;
* an **annotated VC** produced by untrusted code and validated locally, so the
  trusted proof consumes structure (which block/command a constraint comes
  from) rather than reconstructing it.

This does not replace the suffix proof; the existing `Vc.VC` / `checkVC`
pipeline is untouched.
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
          have hpe' : ∀ p, prev = some p →
              p ∈ V ∧ EdgeTaken P (s.upd t y (e.eval s)) p b := fun p hp =>
            ⟨(hpe p hp).1, edgeTaken_freeze huse (hpe p hp).2 ((hpe p hp).2.lt hfwd) hydef _⟩
          refine ⟨V, hentV, hgl, hmax,
            chained_edgeTaken_upd huse hfwd hydef _ hmax hedge, hpe', ?_⟩
          intro v i Bv c' hBv hci hvV hlt hna
          rcases show posLt (v, i) (b, pc) = true ∨ (v = b ∧ i = pc) by
            simp only [posLt, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hlt ⊢
            omega with hold | ⟨rfl, rfl⟩
          · obtain ⟨prevv, hcf, hec⟩ := hfacts v i Bv c' hBv hci hvV hold hna
            exact ⟨prevv, cmdFact_freeze hssa huse hphi hBv hci hold hydef _ hcf,
              fun p hp => ⟨(hec p hp).1, edgeTaken_freeze huse (hec p hp).2
                (Nat.lt_of_lt_of_le ((hec p hp).2.lt hfwd) (hmax v hvV)) hydef _⟩⟩
          · obtain rfl := Option.some.inj (hBv.symm.trans hB)
            obtain rfl := Option.some.inj (hci.symm.trans hc)
            refine ⟨prev, ?_, hpe'⟩
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
          have hydef : IsDefAt P (t, y) b pc := ⟨B, _, hB, hc, rfl⟩
          have hpe' : ∀ p, prev = some p → p ∈ V ∧ EdgeTaken P (s.upd t y v) p b :=
            fun p hp => ⟨(hpe p hp).1, edgeTaken_freeze huse (hpe p hp).2
              ((hpe p hp).2.lt hfwd) hydef _⟩
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
            obtain rfl := Option.some.inj (hci.symm.trans hc)
            exact ⟨prev, trivial, hpe'⟩
      | @phi b pc p s B t y arms src hB hc harm =>
          intro b2 pc2 prev2 s2 heq
          obtain ⟨rfl, rfl, rfl, rfl⟩ := Config.running.inj heq
          obtain ⟨V, hentV, hgl, hmax, hedge, hpe, hfacts⟩ := ih rfl
          have hydef : IsDefAt P (t, y) b pc := ⟨B, _, hB, hc, rfl⟩
          have hpe' : ∀ q, (some p) = some q →
              q ∈ V ∧ EdgeTaken P (s.upd t y (s.regs t src)) q b := fun q hq =>
            ⟨(hpe q hq).1, edgeTaken_freeze huse (hpe q hq).2 ((hpe q hq).2.lt hfwd) hydef _⟩
          refine ⟨V, hentV, hgl, hmax,
            chained_edgeTaken_upd huse hfwd hydef _ hmax hedge, hpe', ?_⟩
          intro v' i Bv c' hBv hci hvV hlt hna
          rcases show posLt (v', i) (b, pc) = true ∨ (v' = b ∧ i = pc) by
            simp only [posLt, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hlt ⊢
            omega with hold | ⟨rfl, rfl⟩
          · obtain ⟨prevv, hcf, hec⟩ := hfacts v' i Bv c' hBv hci hvV hold hna
            exact ⟨prevv, cmdFact_freeze hssa huse hphi hBv hci hold hydef _ hcf,
              fun q hq => ⟨(hec q hq).1, edgeTaken_freeze huse (hec q hq).2
                (Nat.lt_of_lt_of_le ((hec q hq).2.lt hfwd) (hmax v' hvV)) hydef _⟩⟩
          · obtain rfl := Option.some.inj (hBv.symm.trans hB)
            obtain rfl := Option.some.inj (hci.symm.trans hc)
            refine ⟨some p, ?_, hpe'⟩
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
          obtain ⟨V, hentV, hgl, hmax, hedge, hpe, hfacts⟩ := ih rfl
          have hlt' : b < tgt :=
            (forward_target hfwd hB (by rw [hterm]; exact List.mem_singleton.mpr rfl)).1
          have hEdge : EdgeTaken P s b tgt := ⟨B, hB, Or.inl hterm⟩
          refine ⟨V ++ [tgt], List.mem_append.mpr (Or.inl hentV), ?_, ?_, ?_, ?_, ?_⟩
          · simp
          · intro q hq
            rcases List.mem_append.mp hq with h | h
            · exact Nat.le_of_lt (Nat.lt_of_le_of_lt (hmax q h) hlt')
            · exact Nat.le_of_eq (List.mem_singleton.mp h)
          · exact chained_append_single hedge (fun z hz => by
              obtain rfl : z = b := Option.some.inj (hz.symm.trans hgl); exact hEdge)
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
      | @ifTrue b prev s B r tgt el hB hterm hcond =>
          intro b2 pc2 prev2 s2 heq
          obtain ⟨hbeq, rfl, rfl, rfl⟩ := Config.running.inj heq
          subst b2
          obtain ⟨V, hentV, hgl, hmax, hedge, hpe, hfacts⟩ := ih rfl
          have hlt' : b < tgt :=
            (forward_target hfwd hB (by rw [hterm]; simp [termTargets])).1
          have hEdge : EdgeTaken P s b tgt :=
            ⟨B, hB, Or.inr ⟨r, tgt, el, hterm, Or.inl ⟨rfl, hcond⟩⟩⟩
          refine ⟨V ++ [tgt], List.mem_append.mpr (Or.inl hentV), ?_, ?_, ?_, ?_, ?_⟩
          · simp
          · intro q hq
            rcases List.mem_append.mp hq with h | h
            · exact Nat.le_of_lt (Nat.lt_of_le_of_lt (hmax q h) hlt')
            · exact Nat.le_of_eq (List.mem_singleton.mp h)
          · exact chained_append_single hedge (fun z hz => by
              obtain rfl : z = b := Option.some.inj (hz.symm.trans hgl); exact hEdge)
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
      | @ifFalse b prev s B r th tgt hB hterm hcond =>
          intro b2 pc2 prev2 s2 heq
          obtain ⟨hbeq, rfl, rfl, rfl⟩ := Config.running.inj heq
          subst b2
          obtain ⟨V, hentV, hgl, hmax, hedge, hpe, hfacts⟩ := ih rfl
          have hlt' : b < tgt :=
            (forward_target hfwd hB (by rw [hterm]; simp [termTargets])).1
          have hEdge : EdgeTaken P s b tgt :=
            ⟨B, hB, Or.inr ⟨r, th, tgt, hterm, Or.inr ⟨rfl, hcond⟩⟩⟩
          refine ⟨V ++ [tgt], List.mem_append.mpr (Or.inl hentV), ?_, ?_, ?_, ?_, ?_⟩
          · simp
          · intro q hq
            rcases List.mem_append.mp hq with h | h
            · exact Nat.le_of_lt (Nat.lt_of_le_of_lt (hmax q h) hlt')
            · exact Nat.le_of_eq (List.mem_singleton.mp h)
          · exact chained_append_single hedge (fun z hz => by
              obtain rfl : z = b := Option.some.inj (hz.symm.trans hgl); exact hEdge)
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

/-- The map-definition half, over the forward structural facts. No `hlast`
(map definitions have no objective row); shares `visited_phi_defHolds`. -/
theorem annExpectedMapDefs_robust_or_def {P : Program} {σ : State} {V : List Nat}
    (hssa : ssaOK P = true) (hfwd : forwardOK P = true) (hphi : phiOK P = true)
    (hamo : amoSideOK P = true) (hgf : guardFreeOK P = true)
    (hdc : domClosedOK P = true) (huse : usesOK P = true)
    (hentryV : P.entry ∈ V) (hhead : V.head? = some P.entry)
    (hedge : Chained (EdgeTaken P σ) V)
    (hfacts : ∀ v ∈ V, ∀ (B : Block) (i : Nat) (c' : Cmd),
      P.block? v = some B → B.cmds[i]? = some c' →
      ∃ prev : Option Nat, CmdFact σ prev c'
        ∧ ∀ p, prev = some p → p ∈ V ∧ EdgeTaken P σ p v) :
    ∀ md ∈ Vc.expectedMapDefs P,
      DefExt.RobustDef
          (fun t x => (t, x) ∈ DefExt.targets (witnessDefs P V))
          (setBlockVars P V σ) ⟨.map, md.1, md.2⟩
        ∨ (⟨.map, md.1, md.2⟩ : DefExt.Def) ∈ witnessDefs P V := by
  have hdomV := dom_visited hdc hfwd hedge hhead
  intro md hmd
  obtain ⟨b, B, i, c, hB, hci, hcd⟩ := mem_expectedMapDefs hmd
  have hblt : b < P.blocks.length := (List.getElem?_eq_some_iff.mp hB).1
  by_cases hbV : b ∈ V
  · refine Or.inl (robustDef_intro hentryV hdomV
      fun w' hblk _hexit _hguard hag hdom => ?_)
    obtain ⟨x, rhs⟩ := md
    rcases cmdMapDef?_eq_some hcd with ⟨e, rfl, rfl⟩ | ⟨arms, rfl, rfl⟩
    · obtain ⟨prev, hfact, -⟩ := hfacts b hbV B i _ hB hci
      simp only [CmdFact] at hfact
      have hu := usesOK_cmd huse hB hci
      simp only [cmdUsesOK] at hu
      have hgfc := guardFree_at hgf (List.mem_of_getElem? hB)
        (List.mem_of_getElem? hci)
      simp only [cmdGuardFree, List.isEmpty_iff] at hgfc
      have hwx : w'.regs .map x = σ.regs .map x := by
        refine hag .map x fun d j hdj => ?_
        obtain ⟨rfl, -⟩ := ssa_unique hssa
          ⟨B, _, hB, hci, by simp [Cmd.def?]⟩ hdj
        exact hbV
      have hevals : (Vc.lower e).eval w' = (Vc.lower e).eval σ := by
        refine eval_congr _ ?_ ?_
        · intro p hp
          exact hdom b hbV p.1 p.2
            (useOK_dom (List.all_eq_true.mp hu p (lower_vars e p hp)))
        · intro q hq
          have := lower_blkVars e q hq
          rw [hgfc] at this
          cases this
      show w'.regs .map x = (Vc.lower e).eval w'
      rw [hwx, hevals, Vc.eval_lower]
      exact hfact
    · exact visited_phi_defHolds hssa hfwd hphi hamo huse hedge hentryV
        hdomV hfacts hbV hB hci hblt hblk hag
  · exact Or.inr (witnessDefAt_mem_witnessDefs
      ⟨B, c, hB, hci, Vc.cmdMapDef?_unguarded hcd⟩ hbV)

/-! ## The annotated VC

An untrusted, pre-bucketed VC: per block, its CFG constraints and its
per-command constraints; plus the objective and the map definitions. Blocks
are listed in program (topological) order, index `= ` block index. The checker
validates each bucket *locally* against the encoder's own generators
(`cfgConstraintsFor` / `cmdConstraints` / `objective` / `expectedMapDefs`) — a
decidable per-site equality — so the soundness proof consumes the structure
rather than searching for the site that produced each constraint. -/

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

/-- One block's annotated buckets: its CFG constraints and, per command, that
command's constraints. -/
structure BlockBucket where
  cfg : List BExp
  cmds : List (List BExp)
deriving Repr, DecidableEq

/-- The whole annotated VC: per-block buckets (in block-index order), the
objective, and the map definitions. -/
structure AnnVC where
  perBlock : List BlockBucket
  objective : List BExp
  mapDefs : List (Nat × MExp)
deriving Repr, DecidableEq

/-- The plain constraint list an annotated VC denotes (buckets flattened, then
the objective). The map definitions stay separate, as in `Vc.VC`. -/
def AnnVC.flatten (a : AnnVC) : List BExp :=
  (a.perBlock.map fun bk => bk.cfg ++ bk.cmds.flatten).flatten ++ a.objective

/-- Satisfaction: every flattened constraint is true and every map definition
holds as a `Prop`-level function equality. -/
def AnnVC.Sat (w : State) (a : AnnVC) : Prop :=
  (∀ c ∈ a.flatten, c.eval w = true)
    ∧ ∀ md ∈ a.mapDefs, w.regs .map md.1 = md.2.eval w

def AnnVC.Unsat (a : AnnVC) : Prop := ¬∃ w, a.Sat w

/-- Local per-site validation: the program is well-formed and every constraint
filed under a block is one that block's generators actually emit (per-bucket
*subset*, mirroring the flat `checkVC`'s subset check — real `ttac vcgen`
output drops trivially-true terms). This validates the annotation's
block-attribution; a mis-filed constraint fails the cheap local check — a
completeness loss, never unsound. -/
def checkVCAnn (P : Program) (a : AnnVC) : Bool :=
  wellFormed P
    && decide (a.perBlock.length = P.blocks.length)
    && (a.perBlock.zipIdx.all fun (bk, b) =>
          bk.cfg.all (fun c => decide (c ∈ cfgConstraintsFor P b))
            && (match P.blocks[b]? with
                | some B => bk.cmds.flatten.all
                    (fun c => decide (c ∈ (B.cmds.map (cmdConstraints P b)).flatten))
                | none => false))
    && (match assertSites P with
        | [(aB, _, okReg)] =>
            a.objective.all (fun c => decide (c ∈ objective P aB okReg))
        | _ => false)
    && a.mapDefs.all (fun md => decide (md ∈ expectedMapDefs P))

/-- What a passing `checkVCAnn` guarantees, decoded from the `&&` chain: each
bucket is a subset of its block's generators, the objective a subset of the
objective, the map defs a subset of the expected ones. -/
theorem checkVCAnn_true {P : Program} {a : AnnVC} (h : checkVCAnn P a = true) :
    wellFormed P = true
    ∧ a.perBlock.length = P.blocks.length
    ∧ (∀ bk b, (bk, b) ∈ a.perBlock.zipIdx →
        (∀ c ∈ bk.cfg, c ∈ cfgConstraintsFor P b) ∧
        ∃ B, P.block? b = some B ∧
          ∀ c ∈ bk.cmds.flatten, c ∈ (B.cmds.map (cmdConstraints P b)).flatten)
    ∧ (∃ aB iA okReg, assertSites P = [(aB, iA, okReg)]
        ∧ ∀ c ∈ a.objective, c ∈ objective P aB okReg)
    ∧ (∀ md ∈ a.mapDefs, md ∈ expectedMapDefs P) := by
  unfold checkVCAnn at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hwf, hlen⟩, hall⟩, hobj⟩, hmap⟩ := h
  rw [decide_eq_true_eq] at hlen
  refine ⟨hwf, hlen, ?_, ?_,
    fun md hmd => of_decide_eq_true (List.all_eq_true.mp hmap md hmd)⟩
  · intro bk b hmem
    have hb := List.all_eq_true.mp hall (bk, b) hmem
    rw [Bool.and_eq_true] at hb
    refine ⟨fun c hc => of_decide_eq_true (List.all_eq_true.mp hb.1 c hc), ?_⟩
    rw [Program.block?]
    revert hb
    cases hbeq : P.blocks[b]? with
    | none => intro hb; simp at hb
    | some B => exact fun hb => ⟨B, rfl,
        fun c hc => of_decide_eq_true (List.all_eq_true.mp hb.2 c hc)⟩
  · revert hobj
    cases hsig : assertSites P with
    | nil => intro hobj; simp at hobj
    | cons a0 rest =>
        cases rest with
        | nil =>
            obtain ⟨aB, iA, okReg⟩ := a0
            exact fun hobj => ⟨aB, iA, okReg, rfl,
              fun c hc => of_decide_eq_true (List.all_eq_true.mp hobj c hc)⟩
        | cons a1 rest' => intro hobj; simp at hobj

end Vc

/-! ## Per-bucket robustness — the annotation, consumed

The three factored halves of the old `expected`-wide dispatch, one per
annotation bucket kind. `checkVCAnn_sound` walks the `AnnVC`'s `perBlock`
buckets and applies these directly (each bucket is validated a subset of the
matching block generator), so the proof follows the annotation's structure
rather than re-searching `expected P`. -/

/-- Every CFG constraint the encoder emits for a block `S` is robust. -/
theorem cfg_robust {P : Program} {σ : State} {V : List Nat}
    (hfwd : forwardOK P = true) (hamo : amoSideOK P = true)
    (huse : usesOK P = true) (hdc : domClosedOK P = true)
    (hentryV : P.entry ∈ V) (hhead : V.head? = some P.entry)
    (hedge : Chained (EdgeTaken P σ) V) {S : Nat} (hSmem : S < P.blocks.length) :
    ∀ c ∈ Vc.cfgConstraintsFor P S,
      DefExt.Robust (fun t x => (t, x) ∈ DefExt.targets (witnessDefs P V))
          (setBlockVars P V σ) c
        ∨ ∃ d ∈ witnessDefs P V, d.toConstraint? = some c := by
  have hdomV := dom_visited hdc hfwd hedge hhead
  intro c hc
  unfold Vc.cfgConstraintsFor at hc
  by_cases hSe : S = P.entry
  · rw [if_pos hSe] at hc; cases hc
  · rw [if_neg hSe] at hc
    have hStail : S ∈ V → S ∈ V.tail := by
      intro hSV
      cases V with
      | nil => cases hhead
      | cons v0 rest =>
          obtain rfl := Option.some.inj hhead
          rcases List.mem_cons.mp hSV with rfl | h
          · exact absurd rfl hSe
          · exact h
    rcases List.mem_cons.mp hc with rfl | hcL'
    · refine Or.inl (robust_intro hentryV hdomV
        fun w' _hblk _hexit hguard _hag hdom => ?_)
      rw [Vc.eval_mkImp]
      by_cases hSV : S ∈ V
      · rw [Bool.or_eq_true]; right
        rw [Vc.eval_mkOr]
        obtain ⟨p, hpV, hE, -⟩ := chained_pred hedge hedge (hStail hSV)
        obtain ⟨cond, hcondmem, hcondeval⟩ := hE.edge_cond
        apply List.any_eq_true.mpr
        refine ⟨Vc.mkAnd2 (Vc.guardOf P p) cond,
          List.mem_map.mpr ⟨(p, cond), hcondmem, rfl⟩, ?_⟩
        rw [Vc.eval_mkAnd2]
        have hplt : p < P.blocks.length :=
          Nat.lt_trans (pred_lt hfwd (mem_predsOf.mpr ⟨cond, hcondmem⟩)) hSmem
        rw [hguard p hplt]
        obtain ⟨hblknil, hbvars⟩ := edge_cond_vars hcondmem
        have hcondw : cond.eval w' = cond.eval σ := by
          refine eval_congr cond ?_ ?_
          · intro q hq
            obtain ⟨r, B', t', e', rfl, hB', hterm'⟩ := hbvars q hq
            have hterm_use := usesOK_term huse hB'
            simp only [termUsesOK, hterm'] at hterm_use
            exact hdom p hpV .bool r (useOK_dom hterm_use)
          · intro q hq
            rw [hblknil] at hq
            cases hq
        rw [hcondw, hcondeval]
        simp [hpV]
      · rw [Bool.or_eq_true]; left
        rw [hguard S hSmem]
        simp [hSV]
    · rcases List.mem_cons.mp hcL' with rfl | hcL''
      · refine Or.inl (robust_intro hentryV hdomV
          fun w' _hblk _hexit hguard _hag _hdom => ?_)
        rw [Vc.eval_mkImp]
        by_cases hSV : S ∈ V
        · rw [Bool.or_eq_true]; right
          rw [Vc.eval_mkOr]
          obtain ⟨p, hpV, hE, -⟩ := chained_pred hedge hedge (hStail hSV)
          obtain ⟨cond, hcondmem, -⟩ := hE.edge_cond
          apply List.any_eq_true.mpr
          refine ⟨Vc.guardOf P p,
            List.mem_map.mpr ⟨(p, cond), hcondmem, rfl⟩, ?_⟩
          have hplt : p < P.blocks.length :=
            Nat.lt_trans (pred_lt hfwd (mem_predsOf.mpr ⟨cond, hcondmem⟩)) hSmem
          rw [hguard p hplt]
          simp [hpV]
        · rw [Bool.or_eq_true]; left
          rw [hguard S hSmem]
          simp [hSV]
      · rw [List.mem_map] at hcL''
        obtain ⟨cl, hclmem, rfl⟩ := hcL''
        refine Or.inl (robust_intro hentryV hdomV
          fun w' _hblk _hexit hguard _hag _hdom => ?_)
        rw [Vc.eval_mkImp]
        by_cases hSV : S ∈ V
        · rw [Bool.or_eq_true]; right
          obtain ⟨g1, g2, hg1, hg2, hne, rfl⟩ := Vc.mem_amoClauses hclmem
          rw [List.mem_map] at hg1 hg2
          obtain ⟨⟨q1, c1⟩, hq1e, rfl⟩ := hg1
          obtain ⟨⟨q2, c2⟩, hq2e, rfl⟩ := hg2
          have hq1p : q1 ∈ predsOf P S := mem_predsOf.mpr ⟨c1, hq1e⟩
          have hq2p : q2 ∈ predsOf P S := mem_predsOf.mpr ⟨c2, hq2e⟩
          have hq1lt : q1 < P.blocks.length :=
            Nat.lt_trans (pred_lt hfwd hq1p) hSmem
          have hq2lt : q2 < P.blocks.length :=
            Nat.lt_trans (pred_lt hfwd hq2p) hSmem
          simp only [Exp.eval, UnOp.denote, BinOp.denote,
            hguard q1 hq1lt, hguard q2 hq2lt]
          by_cases h1 : q1 ∈ V
          · by_cases h2 : q2 ∈ V
            · exfalso
              have hq12 : q1 ≠ q2 := fun h => hne (by rw [h])
              exact hq12 (visited_amo hfwd hamo hedge hSmem
                (two_mem_le_length hq1p hq2p hq12) h1 hq1p h2 hq2p)
            · simp [h2]
          · simp [h1]
        · rw [Bool.or_eq_true]; left
          rw [hguard S hSmem]
          simp [hSV]

/-- Every per-command constraint of a block's command is robust, or is one of
the unvisited-block definitions. -/
theorem cmd_robust_or_def {P : Program} {σ : State} {V : List Nat}
    (hssa : ssaOK P = true) (hfwd : forwardOK P = true) (hphi : phiOK P = true)
    (hamo : amoSideOK P = true) (hgf : guardFreeOK P = true)
    (hdc : domClosedOK P = true) (huse : usesOK P = true)
    (hentryV : P.entry ∈ V) (hhead : V.head? = some P.entry)
    (hedge : Chained (EdgeTaken P σ) V)
    (hfacts : ∀ v ∈ V, ∀ (B : Block) (i : Nat) (c' : Cmd),
      P.block? v = some B → B.cmds[i]? = some c' →
      ∃ prev : Option Nat, CmdFact σ prev c'
        ∧ ∀ p, prev = some p → p ∈ V ∧ EdgeTaken P σ p v)
    {b : Nat} {B : Block} {i : Nat} {cmd : Cmd}
    (hB : P.block? b = some B) (hci : B.cmds[i]? = some cmd) :
    ∀ c ∈ Vc.cmdConstraints P b cmd,
      DefExt.Robust (fun t x => (t, x) ∈ DefExt.targets (witnessDefs P V))
          (setBlockVars P V σ) c
        ∨ ∃ d ∈ witnessDefs P V, d.toConstraint? = some c := by
  have hdomV := dom_visited hdc hfwd hedge hhead
  have hblt : b < P.blocks.length := (List.getElem?_eq_some_iff.mp hB).1
  have hcmdmem : cmd ∈ B.cmds := List.mem_of_getElem? hci
  intro c hc
  rcases mem_cmdConstraints hc with hfc | ⟨t, y, arms, rfl, hshape⟩
  · obtain ⟨f, hfb, rfl⟩ := mem_factConstraints hfc
    refine Or.inl (robust_cmd_fact hentryV hdomV hblt hfb ?_
      (factB_vars_dom hssa huse hB hci hfb)
      (factB_blkVars (guardFree_at hgf (List.mem_of_getElem? hB)
        hcmdmem) hfb))
    intro hbV
    obtain ⟨prev, hfact, -⟩ := hfacts b hbV B i _ hB hci
    exact ⟨prev, hfact⟩
  · have harms : phiArmsOK P b arms = true := phiOK_at hphi hB hcmdmem
    rcases hshape with heq | ⟨hlen2, hcamo⟩
    · by_cases hbV : b ∈ V
      · refine Or.inl (robust_intro hentryV hdomV
          fun w' hblk _hexit _hguard hag _hdom => ?_)
        exact (visited_phi_defHolds hssa hfwd hphi hamo huse hedge
          hentryV hdomV hfacts hbV hB hci hblt hblk hag).toConstraint_eval
          heq
      · exact Or.inr ⟨⟨t, y, Vc.phiRhs P t arms⟩,
          witnessDefAt_mem_witnessDefs ⟨B, _, hB, hci, rfl⟩ hbV, heq⟩
    · obtain ⟨g1, g2, hg1, hg2, hne, rfl⟩ := Vc.mem_amoClauses hcamo
      rw [List.mem_map] at hg1 hg2
      obtain ⟨⟨q1, s1⟩, hq1arm, rfl⟩ := hg1
      obtain ⟨⟨q2, s2⟩, hq2arm, rfl⟩ := hg2
      refine Or.inl (robust_intro hentryV hdomV
        fun w' _hblk _hexit hguard _hag _hdom => ?_)
      have hq1lt : q1 < P.blocks.length := by
        have := phiArm_lt harms hq1arm; omega
      have hq2lt : q2 < P.blocks.length := by
        have := phiArm_lt harms hq2arm; omega
      simp only [Exp.eval, UnOp.denote, BinOp.denote,
        hguard q1 hq1lt, hguard q2 hq2lt]
      by_cases h1 : q1 ∈ V
      · by_cases h2 : q2 ∈ V
        · exfalso
          have hq12 : q1 ≠ q2 := fun h => hne (by rw [h])
          exact hq12 (visited_amo hfwd hamo hedge hblt
            (two_mem_le_length (phiArm_pred harms hq1arm)
              (phiArm_pred harms hq2arm) hq12)
            h1 (phiArm_pred harms hq1arm) h2 (phiArm_pred harms hq2arm))
        · simp [h2]
      · simp [h1]

/-- Every objective constraint is robust: the failing assert's condition is
false at σ (via `hlast`), dominated into every agreeing state. -/
theorem objective_robust {P : Program} {σ : State} {V : List Nat}
    (hone : singleAssertOK P = true) (hfwd : forwardOK P = true)
    (hdc : domClosedOK P = true) (huse : usesOK P = true)
    (hentryV : P.entry ∈ V) (hhead : V.head? = some P.entry)
    (hedge : Chained (EdgeTaken P σ) V)
    {aB iA okReg : Nat} {BA : Block} (hBA : P.block? aB = some BA)
    (hcA : BA.cmds[iA]? = some (.assert okReg))
    (hlast : ∃ (bf : Nat) (Bf : Block) (pcf cf : Nat), V.getLast? = some bf
      ∧ P.block? bf = some Bf ∧ Bf.cmds[pcf]? = some (.assert cf)
      ∧ σ.regs .bool cf = false) :
    ∀ c ∈ Vc.objective P aB okReg,
      DefExt.Robust (fun t x => (t, x) ∈ DefExt.targets (witnessDefs P V))
          (setBlockVars P V σ) c
        ∨ ∃ d ∈ witnessDefs P V, d.toConstraint? = some c := by
  have hdomV := dom_visited hdc hfwd hedge hhead
  intro c hc
  rcases List.mem_cons.mp hc with rfl | hc'
  · refine Or.inl (robust_intro hentryV hdomV
      fun w' _hblk _hexit hguard _hag hdom => ?_)
    rw [Vc.eval_mkImp]
    rw [Bool.or_eq_true]; right
    obtain ⟨bf, Bf, pcf, cf, hlastV, hBf, hcf, hfalse⟩ := hlast
    obtain ⟨hbf, hpcf, hcfok⟩ := singleAssert_unique hone hBf hcf hBA hcA
    have hbf' := hbf.symm
    have hcfok' := hcfok.symm
    subst hbf'
    subst hcfok'
    have haBV : aB ∈ V := getLast?_mem hlastV
    have haBlt : aB < P.blocks.length := (List.getElem?_eq_some_iff.mp hBA).1
    rw [Vc.eval_mkAnd2, hguard aB haBlt]
    have hok : w'.regs .bool okReg = false := by
      have hcuse := usesOK_cmd huse hBA hcA
      simp only [cmdUsesOK] at hcuse
      rw [hdom aB haBV .bool okReg (useOK_dom hcuse)]
      exact hfalse
    rw [Vc.eval_mkNot]
    simp [Exp.eval, hok, haBV]
  · rcases List.mem_cons.mp hc' with rfl | hc''
    · exact Or.inl (robust_intro hentryV hdomV
        fun w' _hblk hexit _hguard _hag _hdom => by
          simp only [Vc.exitVar, Exp.eval]; exact hexit)
    · cases hc''

/-! ## Soundness of `checkVCAnn`

The forward analogue of `checkVC_sound`/`checkVC_safe`: `forwardStructural`
supplies the structural facts and the per-bucket robustness lemmas above are
applied by walking the annotation's buckets; the annotated VC's constraints
are a subset of the block generators by the per-site validation. -/

theorem checkVCAnn_sound {P : Program} {a : Vc.AnnVC}
    (hchk : Vc.checkVCAnn P a = true) {s0 σ : State}
    (hrun : Steps P (Config.init P s0) (.failed σ)) :
    ∃ w, a.Sat w := by
  obtain ⟨hwf, hlen, hblocks, ⟨aB, iA, okReg, hsig, hobjsub⟩, hmap⟩ :=
    Vc.checkVCAnn_true hchk
  rw [wellFormed] at hwf
  simp only [Bool.and_eq_true] at hwf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hone, hssa⟩, hfwd⟩, hphi⟩, hamo⟩, hentry⟩, hgf⟩, hdc⟩, huse⟩ := hwf
  obtain ⟨V, hentV, hhead, hedge, hfacts, hlast⟩ :=
    forwardStructural hone hssa huse hfwd hphi hentry hrun
  obtain ⟨BA, hBA, hcA⟩ : ∃ B, P.block? aB = some B ∧ B.cmds[iA]? = some (.assert okReg) :=
    mem_assertSites.mp (by rw [hsig]; exact List.mem_singleton.mpr rfl)
  refine ⟨witness P V σ, ?_, ?_⟩
  · -- Walk the annotation's buckets: each is a subset of its block generator,
    -- so the matching per-bucket robustness lemma applies directly.
    refine DefExt.sat_extend (orderedDefs_witnessDefs hssa huse hphi) ?_
    intro c hc
    rw [Vc.AnnVC.flatten, List.mem_append] at hc
    rcases hc with hc | hc
    · rw [List.mem_flatten] at hc
      obtain ⟨L, hL, hcL⟩ := hc
      rw [List.mem_map] at hL
      obtain ⟨bk, hbk, rfl⟩ := hL
      obtain ⟨b, hbidx⟩ := List.mem_iff_getElem?.mp hbk
      have hblt : b < P.blocks.length := by
        have := (List.getElem?_eq_some_iff.mp hbidx).1; omega
      obtain ⟨hcfgsub, B, hB, hcmdssub⟩ :=
        hblocks bk b (List.mem_zipIdx_iff_getElem?.mpr hbidx)
      rw [List.mem_append] at hcL
      rcases hcL with hccfg | hccmds
      · exact cfg_robust hfwd hamo huse hdc hentV hhead hedge hblt c
          (hcfgsub c hccfg)
      · have hcmem := hcmdssub c hccmds
        rw [List.mem_flatten] at hcmem
        obtain ⟨L2, hL2, hcL2⟩ := hcmem
        rw [List.mem_map] at hL2
        obtain ⟨cmd, hcmdmem, rfl⟩ := hL2
        obtain ⟨i, hci⟩ := List.mem_iff_getElem?.mp hcmdmem
        exact cmd_robust_or_def hssa hfwd hphi hamo hgf hdc huse hentV hhead
          hedge hfacts hB hci c hcL2
    · exact objective_robust hone hfwd hdc huse hentV hhead hedge hBA hcA hlast
        c (hobjsub c hc)
  · have hall := DefExt.sat_extend_defs
      (ds := (Vc.expectedMapDefs P).map fun md => (⟨.map, md.1, md.2⟩ : DefExt.Def))
      (orderedDefs_witnessDefs hssa huse hphi)
      (fun d hd => by
        obtain ⟨md, hmd, rfl⟩ := List.mem_map.mp hd
        exact annExpectedMapDefs_robust_or_def hssa hfwd hphi hamo hgf hdc huse
          hentV hhead hedge hfacts md hmd)
    intro md hmd
    exact hall _ (List.mem_map.mpr ⟨md, hmap md hmd, rfl⟩)

theorem checkVCAnn_safe {P : Program} {a : Vc.AnnVC}
    (hchk : Vc.checkVCAnn P a = true) (hunsat : a.Unsat) : P.Safe :=
  fun ⟨_s0, _σ, hrun⟩ => hunsat (checkVCAnn_sound hchk hrun)

end Ttac
