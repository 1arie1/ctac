import Ttac
import Ttac.Product

/-!
# Golden reference: the idealized rw-eq product on a rewritten diamond

`progA` is the safe scalar diamond; `progB` is a sound rewrite of it:
the branch condition, the pos-arm assignment, and the assert predicate
are re-expressed (`0 ≤ x` as `¬(x < 0)`, `x + 1` as `1 + x`,
`0 ≤ y` as `¬(y < 0)`), and the neg arm gains a valid assume
(`0 < y2`, which holds since that arm runs only when `x < 0`).

The checks pin the construction's intent before the transfer proof
exists: the product lands in the checkable fragment (SSA, forward,
..., everything except single-assert — it has one assert per CHK), the
CHKs pass on seeds through both arms *and on a seed whose two halves
disagree* (the havoc equate at work), and broken rewrites of the
branch and of the assert predicate are caught as EXIT-reaching seeds.
-/

namespace TtacExamples.ProductDemo

open Ttac

/-! ## The rewrite pair

int registers:  0 = x, 1 = y1, 2 = y2, 3 = y
bool registers: 0 = c, 1 = ok
blocks:         0 = entry, 1 = pos, 2 = neg, 3 = join
-/

def progA : Program where
  blocks := [
    { cmds := [
        .havoc .int 0,
        .assign .bool 0 (.le (.litI 0) (.var .int 0)),
        .assume (.le (.var .int 0) (.litI 100))],
      term := .ifGoto 0 1 2 },
    { cmds := [
        .assign .int 1 (.add (.var .int 0) (.litI 1))],
      term := .goto 3 },
    { cmds := [
        .assign .int 2 (.sub (.litI 0) (.var .int 0))],
      term := .goto 3 },
    { cmds := [
        .phi .int 3 [(1, 1), (2, 2)],
        .assign .bool 1 (.le (.litI 0) (.var .int 3)),
        .assert 1],
      term := .halt }]
  entry := 0
  exit := some 3

def progB : Program where
  blocks := [
    { cmds := [
        .havoc .int 0,
        .assign .bool 0 (.not (.lt (.var .int 0) (.litI 0))),
        .assume (.le (.var .int 0) (.litI 100))],
      term := .ifGoto 0 1 2 },
    { cmds := [
        .assign .int 1 (.add (.litI 1) (.var .int 0))],
      term := .goto 3 },
    { cmds := [
        .assign .int 2 (.sub (.litI 0) (.var .int 0)),
        .assume (.lt (.litI 0) (.var .int 2))],
      term := .goto 3 },
    { cmds := [
        .phi .int 3 [(1, 1), (2, 2)],
        .assign .bool 1 (.not (.lt (.var .int 3) (.litI 0))),
        .assert 1],
      term := .halt }]
  entry := 0
  exit := some 3

example : lockstep progA progB = true := by native_decide

example : wellFormed progA = true := by native_decide
example : wellFormed progB = true := by native_decide
example : phiCoversOK progB = true := by native_decide

/-! ## The product lands in the fragment (multi-assert aside) -/

example : ssaOK (product progA progB) = true := by native_decide
example : forwardOK (product progA progB) = true := by native_decide
example : phiOK (product progA progB) = true := by native_decide
example : amoSideOK (product progA progB) = true := by native_decide
example : entryOK (product progA progB) = true := by native_decide
example : guardFreeOK (product progA progB) = true := by native_decide
example : usesOK (product progA progB) = true := by native_decide

/-- The one deliberate departure: the product carries one assert per
CHK, so the single-assert conjunct fails by design. -/
example : singleAssertOK (product progA progB) = false := by native_decide

/-! ## CHKs pass on the sound rewrite -/

def seedX (v : Int) : State where
  regs := fun t => match t with
    | .int => fun x => match x with
        | 0 => v
        | _ => 0
    | .bool => fun _ => false
    | .map => fun _ => fun _ => 0
  blks := fun _ => false

-- Through the pos arm, the neg arm, and an assume-pruned seed.
example : (denot (product progA progB) (dup (seedX 0))).blks
    (product progA progB).blocks.length = false := by native_decide
example : (denot (product progA progB) (dup (seedX (-5)))).blks
    (product progA progB).blocks.length = false := by native_decide
example : (denot (product progA progB) (dup (seedX 200))).blks
    (product progA progB).blocks.length = false := by native_decide

/-- A seed whose two halves *disagree* on the havoc'd input: copy 0
reads `x₀ = 0` (int register 0) while the raw slot for copy 1's `x`
(int register 1) holds 999. The havoc equate `x₁ := x₀` overrides the
disagreement, so every CHK still passes — without the equate, the
B-copy's retained assume `x ≤ 100` would be falsifiable and the
product of this perfectly sound rewrite would be unsafe. -/
def skewSeed : State where
  regs := fun t => match t with
    | .int => fun x => match x with
        | 1 => (999 : Int)
        | _ => 0
    | .bool => fun _ => false
    | .map => fun _ => fun _ => 0
  blks := fun _ => false

example : (denot (product progA progB) skewSeed).blks
    (product progA progB).blocks.length = false := by native_decide

/-! ## The transfer theorem wires up on the pair

`Safe_denot` hypotheses are not decidable, so the goldens can't
discharge them; what they pin is that every side condition of the
transfer theorems is `native_decide`-checkable on a real pair. -/

example (hP : Safe_denot (product progA progB))
    (hB : Safe_denot progB) : Safe_denot progA :=
  product_transfer
    (wellFormed_iff.mp (by native_decide)).1
    (wellFormed_iff.mp (by native_decide)).1
    (wellFormed_iff.mp (by native_decide : wellFormed progB = true)).2
    (by native_decide) (by native_decide) hP hB

example (hP : Safe_denot (product progA progB))
    (hB : progB.Safe) : progA.Safe :=
  product_transfer_safe (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hP hB

/-! ## Broken rewrites are caught -/

/-- Branch condition inverted (`x < 0` instead of `¬(x < 0)`). -/
def badBranchEntry : Block where
  cmds := [
    .havoc .int 0,
    .assign .bool 0 (.lt (.var .int 0) (.litI 0)),
    .assume (.le (.var .int 0) (.litI 100))]
  term := .ifGoto 0 1 2

def progBadBranch : Program :=
  { progB with blocks := progB.blocks.set 0 badBranchEntry }

example : (denot (product progA progBadBranch) (dup (seedX 0))).blks
    (product progA progBadBranch).blocks.length = true := by native_decide

/-- Assert predicate strengthened (`2 ≤ y` instead of `0 ≤ y`): the
pairing CHK `Eq(okA, okB)` fails on `x = 0` (where `y = 1`). -/
def badAssertJoin : Block where
  cmds := [
    .phi .int 3 [(1, 1), (2, 2)],
    .assign .bool 1 (.le (.litI 2) (.var .int 3)),
    .assert 1]
  term := .halt

def progBadAssert : Program :=
  { progB with blocks := progB.blocks.set 3 badAssertJoin }

example : (denot (product progA progBadAssert) (dup (seedX 0))).blks
    (product progA progBadAssert).blocks.length = true := by native_decide

/-- Unjustified rewrite-side assume (`y2 < 0`, false on the neg arm):
the rule-4 CHK fails on `x = -5`. -/
def badAssumeNeg : Block where
  cmds := [
    .assign .int 2 (.sub (.litI 0) (.var .int 0)),
    .assume (.lt (.var .int 2) (.litI 0))]
  term := .goto 3

def progBadAssume : Program :=
  { progB with blocks := progB.blocks.set 2 badAssumeNeg }

example : (denot (product progA progBadAssume) (dup (seedX (-5)))).blks
    (product progA progBadAssume).blocks.length = true := by native_decide

end TtacExamples.ProductDemo
