import Ttac
import TtacExamples.Diamond

/-!
# Golden reference: gamma-merge (sea_gate hybrid) annotated VCs

Two programs through `checkVCGAnn`:

* the scalar diamond, with its join phi emitted as a guarded gamma over
  the branch register `c` instead of the block-guard `phiRhs`;
* the two-region program from the SeaBMC vcgen doc (`docs/vc`,
  Thin-GSSA example): an outer branch `c1` selects two regions, each
  with a local branch (`c2`/`c3`) and a local join, reconverging at
  `n`. The three gammas are exactly the doc's final thin form —
  `v_a = ite(c2, v_x, v_a0)`, `v_b = ite(c3, v_y, v_b0)`,
  `v = ite(c1, v_a, v_b)` — and the valuation table carries the
  claims a real annotator would derive (`c1` pinned throughout each
  region), exercising the multi-hop closure transport.

The doc's CFG has critical edges (`a → a_join` while `a` also branches
to `x`); `amoSideOK` (W5) forbids them, so the golden inserts the
pass-through split blocks the bwd0 pipeline requires anyway.

Tampered variants pin the rejection paths: an unjustified valuation
claim, a wrong cover set, and a wrong arm selection.
-/

namespace TtacExamples.GammaVc

open Ttac

/-- The command buckets a gamma-mode annotator emits: phi slots carrying
a certificate get the gamma constraint (plus the classical at-most-one
clauses); everything else keeps the classical generators. -/
def gammaBucketCmds (P : Program) (b : Nat) (B : Block)
    (gs : List (Nat × Vc.GammaCert)) : List (List BExp) :=
  B.cmds.zipIdx.map fun (c, i) =>
    match gs.find? (fun ig => decide (ig.1 = i)), c with
    | some ig, Cmd.phi t x arms =>
        (Vc.gammaConstraint? P b t x arms ig.2).toList
          ++ (if 2 ≤ arms.length then
                Vc.amoClauses (arms.map fun a => Vc.guardOf P a.1)
              else [])
    | _, c => Vc.cmdConstraints P b c

/-- The total-form twin: phi slots carrying a total-gamma certificate
emit the bare defining equation over the gate-cased ITE with `phiRhs`
tail. -/
def tgammaBucketCmds (P : Program) (gt : Vc.GateTable) (b : Nat)
    (B : Block) (gs : List (Nat × Vc.TGammaCert)) : List (List BExp) :=
  B.cmds.zipIdx.map fun (c, i) =>
    match gs.find? (fun ig => decide (ig.1 = i)), c with
    | some ig, Cmd.phi t x arms =>
        (Vc.tgammaConstraint? P gt t x arms ig.2).toList
          ++ (if 2 ≤ arms.length then
                Vc.amoClauses (arms.map fun a => Vc.guardOf P a.1)
              else [])
    | _, c => Vc.cmdConstraints P b c

/-! ## The diamond, gamma-merged -/

namespace Diamond

open TtacExamples.Diamond

/-- The join phi `y := phi [pos: y1, neg: y2]` as
`ite(c, y1, y2)`: the case covers `pos`, the tail is the last arm. -/
def gcert : Vc.GammaCert := ⟨[⟨.var .bool 0, 1, [1]⟩]⟩

def gammasAt (b : Nat) : List (Nat × Vc.GammaCert) :=
  if b = 3 then [(0, gcert)] else []

/-- Valuation table: `c` is pinned true at `pos` and false at `neg`,
each justified by the entry branch's own edge. -/
def val : ValTable := [[], [(0, true)], [(0, false)], []]

def gvc : Vc.GAnnVC where
  perBlock := prog.blocks.zipIdx.map fun (B, b) =>
    { cfg := Vc.cfgConstraintsFor prog b
      cmds := gammaBucketCmds prog b B (gammasAt b)
      maps := B.cmds.filterMap (Vc.cmdMapDef? prog)
      gammas := gammasAt b }
  objective := match Vc.assertSites prog with
    | [(aB, _, okReg)] => Vc.objective prog aB okReg
    | _ => []
  val := val

theorem gvc_ok : checkVCGAnn prog gvc = true := by native_decide

/-- The verified chain: the gamma-merged VC unsatisfiable ⇒ the diamond
is safe under the small-step semantics. -/
theorem gvc_implies_safe : Vc.GAnnVC.Unsat gvc → prog.Safe :=
  checkVCGAnn_safe gvc_ok

/-- An unjustified valuation claim (`c = true` at `neg`, contradicting
its own edge and claimed nowhere before) fails the closure. -/
example :
    checkVCGAnn prog
      { gvc with val := [[], [(0, true)], [(0, true)], []] } = false := by
  native_decide

/-- A wrong cover set (the `c`-case claiming to cover `neg`) reverses
the selection and is rejected. -/
example :
    checkVCGAnn prog
      { gvc with perBlock := gvc.perBlock.map fun bk =>
          { bk with gammas := bk.gammas.map fun ig =>
              (ig.1, ⟨[⟨.var .bool 0, 1, [2]⟩]⟩) } } = false := by
  native_decide

/-- A wrong arm (the `pos` case selecting `y2`): the emitted gamma
constraint no longer matches any certified anchor. -/
example :
    checkVCGAnn prog
      { gvc with perBlock := gvc.perBlock.map fun bk =>
          { bk with gammas := bk.gammas.map fun ig =>
              (ig.1, ⟨[⟨.var .bool 0, 2, [1]⟩]⟩) } } = false := by
  native_decide

/-! ### The total form

`y = ite(c, y1, phiRhs)` as an unguarded definition. The single case's
controller is the entry branch itself (`parent := none` — entry
dominates the assert block), oriented toward `pos`; the join
postdominates `pos` toward the assert block, so a firing case forces
the join. No gate table needed. -/

def tcert : Vc.TGammaCert := ⟨[⟨⟨none, 0, true⟩, 1, [1]⟩]⟩

def tgammasAt (b : Nat) : List (Nat × Vc.TGammaCert) :=
  if b = 3 then [(0, tcert)] else []

def tgvc : Vc.GAnnVC where
  perBlock := prog.blocks.zipIdx.map fun (B, b) =>
    { cfg := Vc.cfgConstraintsFor prog b
      cmds := tgammaBucketCmds prog [] b B (tgammasAt b)
      maps := B.cmds.filterMap (Vc.cmdMapDef? prog)
      tgammas := tgammasAt b }
  objective := match Vc.assertSites prog with
    | [(aB, _, okReg)] => Vc.objective prog aB okReg
    | _ => []
  val := val

theorem tgvc_ok : checkVCGAnn prog tgvc = true := by native_decide

theorem tgvc_implies_safe : Vc.GAnnVC.Unsat tgvc → prog.Safe :=
  checkVCGAnn_safe tgvc_ok

end Diamond

/-! ## The two-region program (SeaBMC doc, Thin-GSSA example)

int registers:  0 = v_a0, 1 = v_x, 2 = v_a, 3 = v_b0, 4 = v_y,
                5 = v_b, 6 = v
bool registers: 0 = c1, 1 = c2, 2 = c3, 3 = ok
blocks:         0 = entry, 1 = a, 2 = x, 3 = a_split, 4 = a_join,
                5 = b, 6 = y, 7 = b_split, 8 = b_join, 9 = n
-/

namespace TwoRegion

def prog : Program where
  blocks := [
    -- 0 entry: c1 := havoc; if c1 goto a else b
    { cmds := [.havoc .bool 0], term := .ifGoto 0 1 5 },
    -- 1 a: c2 := havoc; v_a0 := 10; if c2 goto x else a_split
    { cmds := [.havoc .bool 1, .assign .int 0 (.litI 10)],
      term := .ifGoto 1 2 3 },
    -- 2 x: v_x := 2; goto a_join
    { cmds := [.assign .int 1 (.litI 2)], term := .goto 4 },
    -- 3 a_split: goto a_join
    { cmds := [], term := .goto 4 },
    -- 4 a_join: v_a := phi [x: v_x, a_split: v_a0]; goto n
    { cmds := [.phi .int 2 [(2, 1), (3, 0)]], term := .goto 9 },
    -- 5 b: c3 := havoc; v_b0 := 20; if c3 goto y else b_split
    { cmds := [.havoc .bool 2, .assign .int 3 (.litI 20)],
      term := .ifGoto 2 6 7 },
    -- 6 y: v_y := 3; goto b_join
    { cmds := [.assign .int 4 (.litI 3)], term := .goto 8 },
    -- 7 b_split: goto b_join
    { cmds := [], term := .goto 8 },
    -- 8 b_join: v_b := phi [y: v_y, b_split: v_b0]; goto n
    { cmds := [.phi .int 5 [(6, 4), (7, 3)]], term := .goto 9 },
    -- 9 n: v := phi [a_join: v_a, b_join: v_b]; ok := 0 < v; assert ok
    { cmds := [.phi .int 6 [(4, 2), (8, 5)],
               .assign .bool 3 (.lt (.litI 0) (.var .int 6)),
               .assert 3],
      term := .halt }]
  entry := 0
  exit := none

/-- The doc's three thin gammas. -/
def gammasAt : Nat → List (Nat × Vc.GammaCert)
  | 4 => [(0, ⟨[⟨.var .bool 1, 1, [2]⟩]⟩)]  -- v_a = ite(c2, v_x, v_a0)
  | 8 => [(0, ⟨[⟨.var .bool 2, 4, [6]⟩]⟩)]  -- v_b = ite(c3, v_y, v_b0)
  | 9 => [(0, ⟨[⟨.var .bool 0, 2, [4]⟩]⟩)]  -- v   = ite(c1, v_a, v_b)
  | _ => []

/-- The valuation table: the local branch pinned on each side of its
own edge, and the outer `c1` carried down each region to the join the
final gamma switches on — the multi-hop closure at work. -/
def val : ValTable := [
  [],                     -- 0 entry
  [(0, true)],            -- 1 a
  [(1, true), (0, true)], -- 2 x
  [(1, false), (0, true)],-- 3 a_split
  [(0, true)],            -- 4 a_join
  [(0, false)],           -- 5 b
  [(2, true), (0, false)],-- 6 y
  [(2, false), (0, false)],-- 7 b_split
  [(0, false)],           -- 8 b_join
  []]                     -- 9 n

def gvc : Vc.GAnnVC where
  perBlock := prog.blocks.zipIdx.map fun (B, b) =>
    { cfg := Vc.cfgConstraintsFor prog b
      cmds := gammaBucketCmds prog b B (gammasAt b)
      maps := B.cmds.filterMap (Vc.cmdMapDef? prog)
      gammas := gammasAt b }
  objective := match Vc.assertSites prog with
    | [(aB, _, okReg)] => Vc.objective prog aB okReg
    | _ => []
  val := val

theorem gvc_ok : checkVCGAnn prog gvc = true := by native_decide

theorem gvc_implies_safe : Vc.GAnnVC.Unsat gvc → prog.Safe :=
  checkVCGAnn_safe gvc_ok

/-- Dropping the `c1` claims at the region joins breaks the final
gamma's certificate: the case guard is no longer decidable at its
predecessors. -/
example :
    checkVCGAnn prog
      { gvc with val := [[], [(0, true)], [(1, true), (0, true)],
          [(1, false), (0, true)], [], [(0, false)],
          [(2, true), (0, false)], [(2, false), (0, false)], [], []] }
      = false := by
  native_decide

/-! ### The total form

The doc's materialized thin gates as a real gate table: `G_a`/`G_b`
(the region gates) hang off the entry branch; the local joins' cases
reference them as parents, so their guards are the two-hop
`G_region ∧ c_local` conjunctions; the final join's case is the entry
branch itself. -/

def gates : Vc.GateTable := [
  ⟨1, [⟨none, 0, true⟩]⟩,    -- G_a  = c1
  ⟨5, [⟨none, 0, false⟩]⟩]   -- G_b  = ¬c1

def tgammasAt : Nat → List (Nat × Vc.TGammaCert)
  | 4 => [(0, ⟨[⟨⟨some 0, 1, true⟩, 1, [2]⟩]⟩)]  -- v_a: G_a ∧ c2 ⇒ v_x
  | 8 => [(0, ⟨[⟨⟨some 1, 5, true⟩, 4, [6]⟩]⟩)]  -- v_b: G_b ∧ c3 ⇒ v_y
  | 9 => [(0, ⟨[⟨⟨none, 0, true⟩, 2, [4]⟩]⟩)]    -- v:   c1 ⇒ v_a
  | _ => []

def tgvcWith (tg : Nat → List (Nat × Vc.TGammaCert)) : Vc.GAnnVC where
  perBlock := prog.blocks.zipIdx.map fun (B, b) =>
    { cfg := Vc.cfgConstraintsFor prog b
      cmds := tgammaBucketCmds prog gates b B (tg b)
      maps := B.cmds.filterMap (Vc.cmdMapDef? prog)
      tgammas := tg b }
  objective := match Vc.assertSites prog with
    | [(aB, _, okReg)] => Vc.objective prog aB okReg
    | _ => []
  val := val
  gates := gates

def tgvc : Vc.GAnnVC := tgvcWith tgammasAt

theorem tgvc_ok : checkVCGAnn prog tgvc = true := by native_decide

theorem tgvc_implies_safe : Vc.GAnnVC.Unsat tgvc → prog.Safe :=
  checkVCGAnn_safe tgvc_ok

/-- A wrong-side controller at `b_join` (`c1`'s *then* edge, which
selects the other region and forces nothing toward `b_join`): the
postdominator side condition rejects the case. -/
example :
    checkVCGAnn prog
      (tgvcWith fun b =>
        if b = 8 then [(0, ⟨[⟨⟨none, 0, true⟩, 4, [6]⟩]⟩)]
        else tgammasAt b) = false := by
  native_decide

end TwoRegion

end TtacExamples.GammaVc
