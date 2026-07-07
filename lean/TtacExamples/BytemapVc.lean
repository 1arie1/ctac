import Ttac

/-!
# Golden reference: the bytemap-phi VC passes `checkVC`

Hand transcription of the real `ttac vcgen` output for
`docs/vc/examples/safe_bytemap_phi.ttac` (bwd0 encoding, bytemap-as-UF)
under the `ttac vc-check` numbering: blocks entry = 0, left = 1,
right = 2, join = 3, `BLK_EXIT` = 4; map registers M = 0, M1 = 1,
M2 = 2, M3 = 3.

The smt2 asserts become `constraints`; the `define-fun`s (stores in
both branches, the pointwise-ite map phi at the join) become `mapDefs`.
This pins the map side of the fold mirror against the Python encoder;
the Python test suite pins the transpiler against the same lines.
-/

namespace TtacExamples.BytemapPhi

open Ttac

/-!
int registers:  0 = i, 1 = v, 2 = x
bool registers: 0 = c, 1 = ok
map registers:  0 = M, 1 = M1, 2 = M2, 3 = M3
-/

def prog : Program where
  blocks := [
    -- 0: entry
    { cmds := [
        .havoc .map 0,
        .havoc .int 0,
        .havoc .int 1,
        .havoc .bool 0],
      term := .ifGoto 0 1 2 },
    -- 1: left
    { cmds := [
        .assign .map 1 (.store (.var .map 0) (.var .int 0) (.var .int 1))],
      term := .goto 3 },
    -- 2: right
    { cmds := [
        .assign .map 2 (.store (.var .map 0) (.var .int 0) (.var .int 1))],
      term := .goto 3 },
    -- 3: join
    { cmds := [
        .phi .map 3 [(1, 1), (2, 2)],
        .assign .int 2 (.select (.var .map 3) (.var .int 0)),
        .assign .bool 1 (.eqI (.var .int 2) (.var .int 1)),
        .assert 1],
      term := .halt }]
  entry := 0
  exit := none

def vc : Vc.VC where
  constraints := [
    -- (assert (or (not BLK_left) (not BLK_right)))  [map-phi AMO]
    .or (.not (.blk 1)) (.not (.blk 2)),
    -- (assert (=> BLK_join (= x (M3 i))))
    .imp (.blk 3)
      (.eqI (.var .int 2) (.select (.var .map 3) (.var .int 0))),
    -- (assert (=> BLK_join (= ok (= x v))))
    .imp (.blk 3)
      (.eqB (.var .bool 1) (.eqI (.var .int 2) (.var .int 1))),
    -- (assert (=> BLK_left c))
    .imp (.blk 1) (.var .bool 0),
    -- (assert (=> BLK_right (not c)))
    .imp (.blk 2) (.not (.var .bool 0)),
    -- (assert (=> BLK_join (or BLK_left BLK_right)))  [emitted twice]
    .imp (.blk 3) (.or (.blk 1) (.blk 2)),
    .imp (.blk 3) (.or (.blk 1) (.blk 2)),
    -- (assert (=> BLK_join (or (not BLK_left) (not BLK_right))))
    .imp (.blk 3) (.or (.not (.blk 1)) (.not (.blk 2))),
    -- (assert (=> BLK_EXIT (and BLK_join (not ok))))
    .imp (.blk 4) (.and (.blk 3) (.not (.var .bool 1))),
    -- (assert BLK_EXIT)
    .blk 4]
  mapDefs := [
    -- (define-fun M1 ((idx Int)) Int (ite (= idx i) v (M idx)))
    (1, .store (.var .map 0) (.var .int 0) (.var .int 1)),
    -- (define-fun M2 ((idx Int)) Int (ite (= idx i) v (M idx)))
    (2, .store (.var .map 0) (.var .int 0) (.var .int 1)),
    -- (define-fun M3 ((idx Int)) Int (ite BLK_left (M1 idx) (M2 idx)))
    (3, .ite (.blk 1) (.var .map 1) (.var .map 2))]

theorem vc_ok : checkVC prog vc = true := by native_decide

/-- The full verified chain: if the VC is unsatisfiable, the program is
safe under the small-step semantics (denotational route). -/
theorem vc_implies_safe : Vc.Unsat vc → prog.Safe :=
  checkVC_safe_via_denot vc_ok

/-- A tampered store (index and value swapped) must be rejected. -/
example :
    checkVC prog
      { constraints := [],
        mapDefs :=
          [(1, .store (.var .map 0) (.var .int 1) (.var .int 0))] }
      = false := by
  native_decide

end TtacExamples.BytemapPhi
