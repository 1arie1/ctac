import Mathlib.Logic.Function.Basic
import Ttac.Ast

/-!
# Tiny TAC deep embedding: register state

One total register file per sort, plus the guard component. Nothing is
`Option`: under SSA with no use-before-def every read is dominated by a
write, so the junk in unwritten registers is dead. This is also what
makes an *arbitrary* initial state a faithful model of havoc-at-entry.

`upd` is the only writer, and it is touched *only* through the simp
lemmas below — the cross-sort lemma is stated at the whole-function
level (`.regs u = s.regs u`), which is cast-free (both sides live in
`Nat → u.denote` at the same `u`). Never unfold `upd` in a proof.
-/

namespace Ttac

structure State where
  regs : (t : Ty) → Nat → t.denote
  /-- Block-reachability guards, read only by VC formulas (`Exp.blk`).
  The program semantics neither reads nor writes this component; the
  VC witness sets it once from the visited-block list. -/
  blks : Nat → Bool

namespace State

def upd (s : State) (t : Ty) (x : Nat) (v : t.denote) : State :=
  { s with regs := Function.update s.regs t (Function.update (s.regs t) x v) }

@[simp] theorem upd_regs_self (s : State) (t : Ty) (x : Nat) (v : t.denote) :
    (s.upd t x v).regs t x = v := by
  simp [upd]

@[simp] theorem upd_regs_of_ne_sort (s : State) {t u : Ty} (h : u ≠ t)
    (x : Nat) (v : t.denote) : (s.upd t x v).regs u = s.regs u := by
  simp [upd, h]

@[simp] theorem upd_regs_of_ne_idx (s : State) (t : Ty) {x y : Nat}
    (h : y ≠ x) (v : t.denote) : (s.upd t x v).regs t y = s.regs t y := by
  simp [upd, h]

@[simp] theorem upd_blks (s : State) (t : Ty) (x : Nat) (v : t.denote) :
    (s.upd t x v).blks = s.blks := rfl

/-- Pair form of the disequality lemmas: the reader's `(sort, index)`
differs from the writer's. -/
theorem upd_regs_of_ne (s : State) {t u : Ty} {x y : Nat}
    (h : (u, y) ≠ (t, x)) (v : t.denote) :
    (s.upd t x v).regs u y = s.regs u y := by
  by_cases hu : u = t
  · subst hu
    have hy : y ≠ x := fun hyx => h (by rw [hyx])
    exact s.upd_regs_of_ne_idx u hy v
  · rw [s.upd_regs_of_ne_sort hu x v]

end State

end Ttac
