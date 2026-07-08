import Ttac
import Ttac.ProductStutter

/-!
# Golden reference: the surgical rw-eq product (stuttering mode)

Two rewrite pairs pin the `productS` construction and wire the
transfer theorems.

`progA5`/`progB4` is the `cfg-simplify` shape: the rewrite drops a
fall-through stutter block, so one arm of the diamond reaches the
join through a chain — the join's routed phi must resolve that
predecessor through its *owner*.

`shiftA`/`shiftB` is the adversarial-indexing pair: an early stutter
block shifts every matched index by one, so reading `B`'s phi-arm
predecessors naively as `A`-indices would select the *wrong* arm on
the positive path (`B`-arm predecessor `2` names `B`'s pos block but
`A`'s neg block). The checks pin that the ownership-routed product
selects correctly on both paths — the design point that replaces the
implementation's DEST ghosts.
-/

namespace TtacExamples.ProductStutterDemo

open Ttac

/-! ## Pair 1: the `cfg-simplify` shape

int registers:  0 = x, 1 = y1, 2 = y2, 3 = y
bool registers: 0 = c, 1 = ok
A blocks: 0 entry, 1 pos, 2 mid (stutter), 3 neg, 4 join
B blocks: 0 entry, 1 pos, 2 neg, 3 join (mid dropped)
-/

def progA5 : Program where
  blocks := [
    { cmds := [
        .havoc .int 0,
        .assign .bool 0 (.le (.litI 0) (.var .int 0))],
      term := .ifGoto 0 1 3 },
    { cmds := [
        .assign .int 1 (.add (.var .int 0) (.litI 1))],
      term := .goto 2 },
    { cmds := [],
      term := .goto 4 },
    { cmds := [
        .assign .int 2 (.sub (.litI 0) (.var .int 0))],
      term := .goto 4 },
    { cmds := [
        .phi .int 3 [(2, 1), (3, 2)],
        .assign .bool 1 (.le (.litI 0) (.var .int 3)),
        .assert 1],
      term := .halt }]
  entry := 0
  exit := some 4

def progB4 : Program where
  blocks := [
    { cmds := [
        .havoc .int 0,
        .assign .bool 0 (.not (.lt (.var .int 0) (.litI 0)))],
      term := .ifGoto 0 1 2 },
    { cmds := [
        .assign .int 1 (.add (.litI 1) (.var .int 0))],
      term := .goto 3 },
    { cmds := [
        .assign .int 2 (.sub (.litI 0) (.var .int 0))],
      term := .goto 3 },
    { cmds := [
        .phi .int 3 [(1, 1), (2, 2)],
        .assign .bool 1 (.not (.lt (.var .int 3) (.litI 0))),
        .assert 1],
      term := .halt }]
  entry := 0
  exit := some 3

def mt5 : List (Option Nat) := [some 0, some 1, none, some 2, some 3]

example : wellFormed progA5 = true := by native_decide
example : wellFormed progB4 = true := by native_decide
example : phiCoversOK progB4 = true := by native_decide
example : surgeryOK progA5 progB4 mt5 = true := by native_decide

-- the surgical product still lands in the fragment (single-assert aside)
example : ssaOK (productS progA5 progB4 mt5) = true := by native_decide
example : forwardOK (productS progA5 progB4 mt5) = true := by native_decide
example : phiOK (productS progA5 progB4 mt5) = true := by native_decide
example : amoSideOK (productS progA5 progB4 mt5) = true := by native_decide
example : usesOK (productS progA5 progB4 mt5) = true := by native_decide

def seedX (v : Int) : State where
  regs := fun t => match t with
    | .int => fun x => match x with
        | 0 => v
        | _ => 0
    | .bool => fun _ => false
    | .map => fun _ => fun _ => 0
  blks := fun _ => false

-- CHKs pass through the stutter arm, the direct arm, and a skewed seed
example : (denot (productS progA5 progB4 mt5) (dup (seedX 5))).blks
    (productS progA5 progB4 mt5).blocks.length = false := by native_decide
example : (denot (productS progA5 progB4 mt5) (dup (seedX (-5)))).blks
    (productS progA5 progB4 mt5).blocks.length = false := by native_decide

def skewSeed : State where
  regs := fun t => match t with
    | .int => fun x => match x with
        | 1 => (999 : Int)
        | _ => 0
    | .bool => fun _ => false
    | .map => fun _ => fun _ => 0
  blks := fun _ => false

example : (denot (productS progA5 progB4 mt5) skewSeed).blks
    (productS progA5 progB4 mt5).blocks.length = false := by native_decide

-- a wrong witness is rejected (mid marked as matched)
example : surgeryOK progA5 progB4
    [some 0, some 1, some 2, some 2, some 3] = false := by native_decide

/-! ## Pair 2: shifted indices — routing is observable

int registers:  0 = x, 1 = y2 (neg), 2 = y1 (pos), 3 = z
bool registers: 0 = c, 1 = ok
A blocks: 0 entry, 1 sPos (stutter), 2 neg, 3 pos, 4 join
B blocks: 0 entry, 1 neg, 2 pos, 3 join

B's phi arm `(2, …)` names B's *pos* block; read naively as an
A-index it names A's *neg* block, which is inactive on the positive
path — naive index reuse would fall through to the wrong arm. The
ownership routing maps A-pred 3 (pos) → owner 3 → match 2 → B's pos
arm, and A-pred 2 (neg) → match 1 → B's neg arm.
-/

def shiftA : Program where
  blocks := [
    { cmds := [
        .havoc .int 0,
        .assign .bool 0 (.le (.litI 0) (.var .int 0))],
      term := .ifGoto 0 1 2 },
    { cmds := [],
      term := .goto 3 },
    { cmds := [
        .assign .int 1 (.sub (.litI 0) (.var .int 0))],
      term := .goto 4 },
    { cmds := [
        .assign .int 2 (.add (.var .int 0) (.litI 1))],
      term := .goto 4 },
    { cmds := [
        .phi .int 3 [(3, 2), (2, 1)],
        .assign .bool 1 (.lt (.var .int 0) (.var .int 3)),
        .assert 1],
      term := .halt }]
  entry := 0
  exit := some 4

def shiftB : Program where
  blocks := [
    { cmds := [
        .havoc .int 0,
        .assign .bool 0 (.le (.litI 0) (.var .int 0))],
      term := .ifGoto 0 2 1 },
    { cmds := [
        .assign .int 1 (.sub (.litI 0) (.var .int 0))],
      term := .goto 3 },
    { cmds := [
        .assign .int 2 (.add (.var .int 0) (.litI 1))],
      term := .goto 3 },
    { cmds := [
        .phi .int 3 [(2, 2), (1, 1)],
        .assign .bool 1 (.lt (.var .int 0) (.var .int 3)),
        .assert 1],
      term := .halt }]
  entry := 0
  exit := some 3

def mtShift : List (Option Nat) := [some 0, none, some 1, some 2, some 3]

example : wellFormed shiftA = true := by native_decide
example : wellFormed shiftB = true := by native_decide
example : phiCoversOK shiftB = true := by native_decide
example : surgeryOK shiftA shiftB mtShift = true := by native_decide

-- the routed product's CHKs pass on both paths — in particular on the
-- positive path, where naive index reuse would select the neg arm
example : (denot (productS shiftA shiftB mtShift) (dup (seedX 5))).blks
    (productS shiftA shiftB mtShift).blocks.length = false := by
  native_decide
example : (denot (productS shiftA shiftB mtShift) (dup (seedX (-5)))).blks
    (productS shiftA shiftB mtShift).blocks.length = false := by
  native_decide

/-- A genuinely broken rewrite — B's phi sources swapped — is caught
by the assert-pair CHK on the positive path. -/
def badJoin : Block where
  cmds := [
    .phi .int 3 [(2, 1), (1, 2)],
    .assign .bool 1 (.lt (.var .int 0) (.var .int 3)),
    .assert 1]
  term := .halt

def shiftBbad : Program :=
  { shiftB with blocks := shiftB.blocks.set 3 badJoin }

example : (denot (productS shiftA shiftBbad mtShift) (dup (seedX 5))).blks
    (productS shiftA shiftBbad mtShift).blocks.length = true := by
  native_decide

/-! ## The transfer theorems wire up on both pairs -/

example (hP : Safe_denot (productS progA5 progB4 mt5))
    (hB : Safe_denot progB4) : Safe_denot progA5 :=
  stutter_transfer
    (wellFormed_iff.mp (by native_decide)).1
    (wellFormed_iff.mp (by native_decide)).1
    (wellFormed_iff.mp (by native_decide : wellFormed progB4 = true)).2
    (by native_decide) hP hB

example (hP : Safe_denot (productS shiftA shiftB mtShift))
    (hB : shiftB.Safe) : shiftA.Safe :=
  stutter_transfer_safe (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hP hB

end TtacExamples.ProductStutterDemo
