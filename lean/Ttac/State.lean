import Mathlib.Logic.Function.Basic

/-!
# Tiny TAC deep embedding: register state

Total register files, one per namespace. Nothing is `Option`: under SSA
with no use-before-def every read is dominated by a write, so the junk
in unwritten registers is dead. This is also what makes an *arbitrary*
initial state a faithful model of havoc-at-entry.
-/

namespace Ttac

structure State where
  ints : Nat → Int
  bools : Nat → Bool
  /-- Block-reachability guards, read only by VC formulas (`BExp.blk`).
  The program semantics neither reads nor writes this component; the
  VC witness sets it once from the visited-block list. -/
  blks : Nat → Bool

namespace State

def updI (s : State) (x : Nat) (v : Int) : State :=
  { s with ints := Function.update s.ints x v }

def updB (s : State) (c : Nat) (v : Bool) : State :=
  { s with bools := Function.update s.bools c v }

@[simp] theorem updI_ints_self (s : State) (x : Nat) (v : Int) :
    (s.updI x v).ints x = v := by
  simp [updI]

@[simp] theorem updI_ints_of_ne (s : State) {x y : Nat} (h : y ≠ x) (v : Int) :
    (s.updI x v).ints y = s.ints y := by
  simp [updI, h]

@[simp] theorem updI_bools (s : State) (x : Nat) (v : Int) :
    (s.updI x v).bools = s.bools := rfl

@[simp] theorem updB_bools_self (s : State) (c : Nat) (v : Bool) :
    (s.updB c v).bools c = v := by
  simp [updB]

@[simp] theorem updB_bools_of_ne (s : State) {c d : Nat} (h : d ≠ c) (v : Bool) :
    (s.updB c v).bools d = s.bools d := by
  simp [updB, h]

@[simp] theorem updB_ints (s : State) (c : Nat) (v : Bool) :
    (s.updB c v).ints = s.ints := rfl

@[simp] theorem updI_blks (s : State) (x : Nat) (v : Int) :
    (s.updI x v).blks = s.blks := rfl

@[simp] theorem updB_blks (s : State) (c : Nat) (v : Bool) :
    (s.updB c v).blks = s.blks := rfl

end State

end Ttac
