import Ttac

/-!
# Golden reference: scalar diamond

Hand-written deep and shallow embeddings of the scalar diamond program

```
entry:
  x := havoc
  c := 0 <= x
  if c goto pos else neg
pos:
  y1 := x + 1
  goto join
neg:
  y2 := 0 - x
  goto join
join:
  y := phi [pos: y1, neg: y2]
  ok := 0 <= y
  assert ok
  halt
```

The `ttac lean` emitter's output for this program is diffed against
this file's shapes in the Python test suite; keep them in sync.
-/

namespace TtacExamples.Diamond

open Ttac

/-! ## Deep embedding

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
    -- 1: pos
    { cmds := [
        .assign .int 1 (.add (.var .int 0) (.litI 1))],
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

/-! ## Shallow embedding -/

def ok_join (y : Int) : Prop :=
  let ok : Bool := decide (0 ≤ y)
  ok = true ∧ True

def ok_pos (x : Int) : Prop :=
  let y1 : Int := x + 1
  ok_join y1

def ok_neg (x : Int) : Prop :=
  let y2 : Int := 0 - x
  ok_join y2

def ok_entry : Prop :=
  ∀ (x : Int),
    let c : Bool := decide (0 ≤ x)
    (c = true → ok_pos x) ∧ (c = false → ok_neg x)

theorem diamond_safe : ok_entry := by
  intro x
  simp only [ok_pos, ok_neg, ok_join, decide_eq_true_eq,
    decide_eq_false_iff_not, and_true]
  omega

end TtacExamples.Diamond
