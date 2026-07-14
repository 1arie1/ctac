import Ttac

/-!
# Golden reference: counterexample certificate for an unsafe diamond

The scalar diamond with the `pos` arm broken (`y1 := x - 1` instead of
`x + 1`): the seed `x = 0` takes the `pos` branch and lands on
`y = -1`, failing `assert 0 <= y`.

The certificate is just the seed. `denot` is a computable fold, so
"this seed reaches EXIT" is a closed `Bool` equation discharged by
`native_decide` — evaluation *is* the replay. `not_safe_denot_of_seed`
turns it into the refutation `¬ Safe_denot prog`. The `ttac cex-check`
emitter's output is diffed against this file's shapes in the Python
test suite; keep them in sync.
-/

namespace TtacExamples.DiamondCex

open Ttac

/-! ## Deep embedding (unsafe variant)

int registers:  0 = x, 1 = y1, 2 = y2, 3 = y
bool registers: 0 = c, 1 = ok
blocks:         0 = entry, 1 = pos, 2 = neg, 3 = join
-/

def prog : Program where
  blocks := [
    -- 0: entry
    { cmds := [
        .havoc .int 0,
        .assign .bool 0 (.le (.litI 0) (.var .int 0))],
      term := .ifGoto 0 1 2 },
    -- 1: pos (broken: y1 := x - 1)
    { cmds := [
        .assign .int 1 (.sub (.var .int 0) (.litI 1))],
      term := .goto 3 },
    -- 2: neg
    { cmds := [
        .assign .int 2 (.sub (.litI 0) (.var .int 0))],
      term := .goto 3 },
    -- 3: join
    { cmds := [
        .phi .int 3 [(1, 1), (2, 2)],
        .assign .bool 1 (.le (.litI 0) (.var .int 3)),
        .assert 1],
      term := .halt }]
  entry := 0
  exit := some 3

/-! ## The seed

Only the havoc'd register (`x`, int 0) matters; everything the fold
computes is overwritten. `x = 0` drives `pos` (`0 <= 0`), so
`y = y1 = -1` and `ok = false`. -/

def seed : State where
  regs := fun t => match t with
    | .int => fun x => match x with
        | 0 => 0
        | _ => 0
    | .bool => fun _ => false
    | .map => fun _ => fun _ => 0
  blks := fun _ => false

/-- The replay: the seed's denotational run sets the EXIT guard. -/
theorem cex_ok : (denot prog seed).blks prog.blocks.length = true := by
  native_decide

/-- The certified verdict: the solver's `sat` was genuine. -/
theorem prog_not_safe_denot : ¬Safe_denot prog :=
  not_safe_denot_of_seed seed cex_ok

/-! ## The operational upgrade (converse adequacy)

With `wellFormed` and phi coverage checked, the denotational
counterexample replays as a real operational execution: the program is
`Program.Unsafe`, not merely denotationally so. -/

theorem wf_ok : wellFormed prog = true := by native_decide

theorem cov_ok : phiCoversOK prog = true := by native_decide

theorem prog_unsafe : prog.Unsafe :=
  unsafe_of_seed wf_ok cov_ok seed cex_ok

/-- A non-driving seed does not certify: `x = 5` keeps the diamond's
broken arm harmless (`y = 4`), so EXIT stays unreached and
`native_decide` on `= true` would fail — completeness loss, never a
wrong verdict. -/
example :
    (denot prog { seed with
      regs := fun t => match t with
        | .int => fun x => match x with
            | 0 => (5 : Int)
            | _ => 0
        | t' => seed.regs t' }).blks prog.blocks.length = false := by
  native_decide

end TtacExamples.DiamondCex
