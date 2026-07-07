import Ttac.VcDenot

/-!
# The weakening table: admission by "weak enough", not byte-equality

`checkVC` admits a constraint only if it is byte-identical to a member
of `expected P` — so every constant fold the Python encoder performs
must be mirrored exactly in trusted Lean, and any vcgen simplification
drift breaks the checker. This module replaces that admission test with
a *table judgment*: a candidate constraint is admissible if some anchor
the program's steps justify **weakens to** it.

Two tables, two growth axes:

* **Anchor table** — the formulas each instruction's step directly
  justifies. This is the existing per-instruction machinery
  (`Cmd.factB` → `cmdConstraints`, `cfgConstraintsFor`, `objective`),
  whose truth at every failing denotational run is `denot_sat`.
  *Adding a command = a `factB` row + its `denot` case.*
* **Closure table** (`weakensFrom`) — command-independent syntactic
  weakening steps: reflexivity, the trivial constraint, or-introduction,
  hypothesis-introduction. The sole proof obligation per row is its
  case in `weakensFrom_sound`: *if a formula is accepted as a
  weakening, it is a weakening.* *Adding a vcgen simplification = a row
  here.* Complex simplifications that a single syntactic row cannot
  recognize will carry witnesses (rewrite chains, replayed row by row)
  in the VC syntax — a future extension of the same table.

Soundness is admission-agnostic: `checkVCW` accepts ⇒ every candidate
is a weakening of a true anchor ⇒ `DenotSound` ⇒
`safe_denot_of_denotSound`. `checkVCW` strictly generalizes `checkVC`
(membership is the reflexivity row).
-/

namespace Ttac

namespace Vc

/-- The closure table: `weakensFrom a c` accepts `c` as a syntactic
weakening of the anchor `a`. One Bool row per shape; each row's
obligation is its case in `weakensFrom_sound`. -/
def weakensFrom (a c : BExp) : Bool :=
  decide (c = a)
    || decide (c = .litB true)
    || (match c with
        | .bin .or l r => decide (l = a) || decide (r = a)
        | .bin .imp _ r => decide (r = a)
        | _ => false)

/-- The table's contract: an accepted formula is a weakening — true
whenever its anchor is. One case per row. -/
theorem weakensFrom_sound {a c : BExp} {w : State}
    (h : weakensFrom a c = true) (ha : a.eval w = true) :
    c.eval w = true := by
  unfold weakensFrom at h
  rw [Bool.or_eq_true, Bool.or_eq_true] at h
  rcases h with (h | h) | h
  · obtain rfl := of_decide_eq_true h
    exact ha
  · obtain rfl := of_decide_eq_true h
    rfl
  · split at h
    · rw [Bool.or_eq_true] at h
      rcases h with h | h
      · obtain rfl := of_decide_eq_true h
        simp [Exp.eval, BinOp.denote, ha]
      · obtain rfl := of_decide_eq_true h
        simp [Exp.eval, BinOp.denote, ha]
    · obtain rfl := of_decide_eq_true h
      simp [Exp.eval, BinOp.denote, ha]
    · cases h

end Vc

/-- The weakening-table checker: every constraint must weaken from some
anchor. Map definitions are definitional equalities (no boolean
weakening applies); they keep the membership test. -/
def checkVCW (P : Program) (vc : Vc.VC) : Bool :=
  wellFormed P
    && vc.constraints.all
        (fun c => (Vc.expected P).any (fun a => Vc.weakensFrom a c))
    && vc.mapDefs.all (fun md => decide (md ∈ Vc.expectedMapDefs P))

/-- An accepted VC is weak enough: each candidate weakens from an
anchor, and every anchor is true at every failing denotational run
(`denot_sat`). -/
theorem denotSound_of_checkVCW {P : Program} {vc : Vc.VC}
    (hchk : checkVCW P vc = true) : DenotSound P vc := by
  rw [checkVCW, Bool.and_eq_true, Bool.and_eq_true] at hchk
  obtain ⟨⟨hwf, hmem⟩, hmdefs⟩ := hchk
  rw [wellFormed] at hwf
  simp only [Bool.and_eq_true] at hwf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hone, hssa⟩, hfwd⟩, hphi⟩, hamo⟩, hentry⟩, hgf⟩, -⟩, huse⟩ := hwf
  intro s0 hexit
  have hsat := denot_sat hone hssa hfwd hphi hamo hentry hgf huse hexit
  refine ⟨fun c hc => ?_, fun md hmd => hsat.2 md
    (of_decide_eq_true (List.all_eq_true.mp hmdefs md hmd))⟩
  obtain ⟨a, hamem, haw⟩ :=
    List.any_eq_true.mp (List.all_eq_true.mp hmem c hc)
  exact Vc.weakensFrom_sound haw (hsat.1 a hamem)

/-- The weakening-table `checkVC_safe`. -/
theorem checkVCW_safe_denot {P : Program} {vc : Vc.VC}
    (hchk : checkVCW P vc = true) (hunsat : Vc.Unsat vc) : Safe_denot P :=
  safe_denot_of_denotSound (denotSound_of_checkVCW hchk) hunsat

/-! ## Site-tagged admission: the global anchor pool eliminated

`checkVCW` still materializes `expected P` as one flat anchor pool.
With site-tagged candidates (`Vc.AnnVC`), admission consults only the
tagged site's own anchors — `cfgConstraintsFor P b` for a cfg-bucket
constraint, the block's `cmdConstraints` for a command-bucket one, the
two `objective` anchors — so nothing resembling the global expected VC
is ever computed by the checker. `Vc.expected` survives only in the
*proof* (the per-site anchors embed into it, and `denot_sat` supplies
their truth); the checker itself is per-site. -/

/-- Per-site anchors embed into the expected set (proof-side only). -/
theorem mem_expected_of_cfgFor {P : Program} {aB iA okReg : Nat}
    (heqs : Vc.assertSites P = [(aB, iA, okReg)])
    {S : Nat} (hS : S < P.blocks.length) {c : BExp}
    (hc : c ∈ Vc.cfgConstraintsFor P S) : c ∈ Vc.expected P := by
  unfold Vc.expected
  rw [heqs, List.mem_append, List.mem_append]
  left; right
  rw [Vc.cfgConstraints_eq, List.mem_flatten]
  exact ⟨_, List.mem_map.mpr ⟨S, List.mem_range.mpr hS, rfl⟩, hc⟩

theorem mem_expected_of_cmd {P : Program} {aB iA okReg : Nat}
    (heqs : Vc.assertSites P = [(aB, iA, okReg)])
    {b : Nat} {B : Block} (hB : P.block? b = some B) {c : BExp}
    (hc : c ∈ (B.cmds.map (Vc.cmdConstraints P b)).flatten) :
    c ∈ Vc.expected P := by
  unfold Vc.expected
  rw [heqs, List.mem_append, List.mem_append]
  left; left
  rw [List.mem_flatten]
  exact ⟨_, List.mem_map.mpr
    ⟨(B, b), List.mem_zipIdx_iff_getElem?.mpr hB, rfl⟩, hc⟩

theorem mem_expected_of_objective {P : Program} {aB iA okReg : Nat}
    (heqs : Vc.assertSites P = [(aB, iA, okReg)]) {c : BExp}
    (hc : c ∈ Vc.objective P aB okReg) : c ∈ Vc.expected P := by
  unfold Vc.expected
  rw [heqs, List.mem_append]
  exact Or.inr hc

/-- The site-tagged weakening checker: each bucket constraint must
weaken from one of *its own site's* anchors. No global anchor pool. -/
def checkVCWAnn (P : Program) (a : Vc.AnnVC) : Bool :=
  wellFormed P
    && decide (a.perBlock.length = P.blocks.length)
    && (a.perBlock.zipIdx.all fun (bk, b) =>
          bk.cfg.all (fun c =>
              (Vc.cfgConstraintsFor P b).any (fun x => Vc.weakensFrom x c))
            && (match P.blocks[b]? with
                | some B => bk.cmds.flatten.all (fun c =>
                    ((B.cmds.map (Vc.cmdConstraints P b)).flatten).any
                      (fun x => Vc.weakensFrom x c))
                | none => false))
    && (match Vc.assertSites P with
        | [(aB, _, okReg)] => a.objective.all (fun c =>
            (Vc.objective P aB okReg).any (fun x => Vc.weakensFrom x c))
        | _ => false)
    && a.mapDefs.all (fun md => decide (md ∈ Vc.expectedMapDefs P))

theorem denotSound_of_checkVCWAnn {P : Program} {a : Vc.AnnVC}
    (hchk : checkVCWAnn P a = true) :
    DenotSound P { constraints := a.flatten, mapDefs := a.mapDefs } := by
  unfold checkVCWAnn at hchk
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    Bool.and_eq_true] at hchk
  obtain ⟨⟨⟨⟨hwf, hlen⟩, hall⟩, hobj⟩, hmap⟩ := hchk
  rw [decide_eq_true_eq] at hlen
  have hwf' := hwf
  rw [wellFormed] at hwf'
  simp only [Bool.and_eq_true] at hwf'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hone, hssa⟩, hfwd⟩, hphi⟩, hamo⟩, hentry⟩, hgf⟩, -⟩, huse⟩ := hwf'
  intro s0 hexit
  have hsat := denot_sat hone hssa hfwd hphi hamo hentry hgf huse hexit
  obtain ⟨aB, iA, okReg, BA, heqs, hBA, hcA, -⟩ := singleAssert_shape hone
  refine ⟨fun c hc => ?_, fun md hmd => hsat.2 md
    (of_decide_eq_true (List.all_eq_true.mp hmap md hmd))⟩
  rw [Vc.AnnVC.flatten, List.mem_append] at hc
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
      simp only [hBb] at hcmdb
      obtain ⟨x, hxmem, hxw⟩ := List.any_eq_true.mp
        (List.all_eq_true.mp hcmdb c hcmds)
      exact Vc.weakensFrom_sound hxw
        (hsat.1 x (mem_expected_of_cmd heqs hBb hxmem))
  · rw [heqs] at hobj
    obtain ⟨x, hxmem, hxw⟩ := List.any_eq_true.mp
      (List.all_eq_true.mp hobj c hc)
    exact Vc.weakensFrom_sound hxw
      (hsat.1 x (mem_expected_of_objective heqs hxmem))

/-- The site-tagged weakening `checkVC_safe`, denotational side. -/
theorem checkVCWAnn_safe_denot {P : Program} {a : Vc.AnnVC}
    (hchk : checkVCWAnn P a = true) (hunsat : a.Unsat) : Safe_denot P :=
  safe_denot_of_denotSound (denotSound_of_checkVCWAnn hchk)
    (fun ⟨w, hs⟩ => hunsat ⟨w, hs⟩)

end Ttac
