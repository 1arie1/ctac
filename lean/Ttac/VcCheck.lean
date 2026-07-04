import Ttac.Vc

/-!
# The VC checker

`checkVC P off vc` validates a transpiled VC against a program:
well-formedness of `P` (the side conditions under which the bwd0
encoding is complete) plus membership of every VC constraint in
`Vc.expected P off`. All checks are `Bool`-valued so a per-instance
`theorem ... := by native_decide` discharges them.

The dominator table is computed by ordinary *unverified* code; the
soundness proof consumes only the two closure properties re-checked by
`domClosedOK` (a wrong table either fails the check - rejection - or
still yields a sound proof).
-/

namespace Ttac

/-- Command position within a program: `(block index, cmd index)`. The
terminator of block `b` sits at `(b, cmds.length)`. -/
abbrev Pos := Nat × Nat

def posLt (p q : Pos) : Bool :=
  p.1 < q.1 || (p.1 = q.1 && p.2 < q.2)

/-! ## Definition sites -/

def cmdIntDef : Cmd → Option Nat
  | .assignI x _ => some x
  | .havocI x => some x
  | .phiI x _ => some x
  | _ => none

def cmdBoolDef : Cmd → Option Nat
  | .assignB c _ => some c
  | .havocB c => some c
  | .phiB c _ => some c
  | _ => none

/-- Positions of every definition of register `x` under the def-selector
`f` (`cmdIntDef` or `cmdBoolDef`). -/
def defPositions (P : Program) (f : Cmd → Option Nat) (x : Nat) : List Pos :=
  (P.blocks.zipIdx.map fun (B, b) =>
    B.cmds.zipIdx.filterMap fun (c, i) =>
      if f c = some x then some ((b, i) : Pos) else none).flatten

def intDefPositions (P : Program) (x : Nat) : List Pos :=
  defPositions P cmdIntDef x

def boolDefPositions (P : Program) (x : Nat) : List Pos :=
  defPositions P cmdBoolDef x

/-! ## CFG shape -/

def termTargets : Terminator → List Nat
  | .halt => []
  | .goto t => [t]
  | .ifGoto _ t e => [t, e]

def succsOf (P : Program) (p : Nat) : List Nat :=
  match P.blocks[p]? with
  | some B => (termTargets B.term).eraseDups
  | none => []

def predsOf (P : Program) (S : Nat) : List Nat :=
  ((Vc.edgesTo P S).map (·.1)).eraseDups

/-! ## Well-formedness conjuncts -/

/-- W1: exactly one assert, and it is the last command of its block
(an assume after the failing assert would be encoded but never
executed - unsound to accept). -/
def singleAssertOK (P : Program) : Bool :=
  (Vc.assertSites P).length = 1
    && (Vc.assertSites P).all fun (b, i, _) =>
        match P.blocks[b]? with
        | some B => i + 1 = B.cmds.length
        | none => false

def cmdSsaOK (P : Program) (b i : Nat) (c : Cmd) : Bool :=
  (match cmdIntDef c with
    | some x => (intDefPositions P x).all fun q => decide (q = ((b, i) : Pos))
    | none => true)
  && (match cmdBoolDef c with
    | some x => (boolDefPositions P x).all fun q => decide (q = ((b, i) : Pos))
    | none => true)

/-- W2: pure SSA - each register (per namespace) defined at most once
program-wide, checked as: every def site is the *only* member of its
register's def-position list. Rejects DSA-dynamic variables. -/
def ssaOK (P : Program) : Bool :=
  P.blocks.zipIdx.all fun (B, b) =>
    B.cmds.zipIdx.all fun (c, i) => cmdSsaOK P b i c

/-- W3: forward edges only - visited blocks are strictly increasing,
which gives acyclicity and visited-at-most-once. -/
def forwardOK (P : Program) : Bool :=
  P.blocks.zipIdx.all fun (B, b) =>
    (termTargets B.term).all fun t => b < t && t < P.blocks.length

/-- W4: phi arms are nonempty, name pairwise-distinct predecessors, and
each arm's predecessor really is a CFG predecessor with smaller index. -/
def phiArmsOK (P : Program) (b : Nat) (arms : PhiArms) : Bool :=
  !arms.isEmpty
    && decide (arms.map (·.1)).Nodup
    && arms.all fun (p, _) =>
        p < b && (Vc.edgesTo P b).any fun (q, _) => q = p

def phiOK (P : Program) : Bool :=
  P.blocks.zipIdx.all fun (B, b) =>
    B.cmds.all fun c =>
      match c with
      | .phiI _ arms | .phiB _ arms => phiArmsOK P b arms
      | _ => true

/-- W5: the critical-edge side condition that justifies the at-most-one
clauses - every predecessor of a multi-predecessor join has exactly one
successor. -/
def amoSideOK (P : Program) : Bool :=
  (List.range P.blocks.length).all fun S =>
    (predsOf P S).length < 2
      || (predsOf P S).all fun p => decide (succsOf P p = [S])

/-! W6: dominated uses. -/

/-- Untrusted forward dominator pass (preds have smaller index under
W3). Unreachable non-entry blocks get ⊤ (`range n`), the dataflow top. -/
def domTable (P : Program) : Array (List Nat) := Id.run do
  let n := P.blocks.length
  let mut dom : Array (List Nat) := Array.replicate n []
  for b in [0:n] do
    if b = P.entry then
      dom := dom.set! b [b]
    else
      let ps := predsOf P b
      match ps with
      | [] => dom := dom.set! b (List.range n)
      | p₀ :: rest =>
          let inter := rest.foldl
            (fun acc p => acc.filter (· ∈ dom.getD p []))
            (dom.getD p₀ [])
          dom := dom.set! b (b :: inter)
  return dom

/-- The only dominator facts the soundness proof uses, re-checked:
(D1) for every edge `p → u` with `u` non-entry, `dom u ⊆ u :: dom p`;
(D2) `dom entry ⊆ [entry]`. -/
def domClosedOK (P : Program) : Bool :=
  ((domTable P).getD P.entry []).all (· = P.entry)
    && (Vc.allEdges P).all fun (p, u, _) =>
        u = P.entry
          || ((domTable P).getD u []).all fun d =>
              d = u || ((domTable P).getD p []).contains d

/-- A use of register `r` (with def positions `defs`) at position
`(b, i)` is dominated: every def is earlier in the same block, or in a
strictly-earlier dominator block. -/
def useOK (dom : Array (List Nat)) (defs : List Pos) (b i : Nat) : Bool :=
  defs.all fun (d, j) =>
    (d = b && j < i) || (d < b && (dom.getD b []).contains d)

/-- Phi-arm rule: the source's defs must sit at or before the arm's
predecessor block and dominate it. -/
def armUseOK (dom : Array (List Nat)) (defs : List Pos) (p : Nat) : Bool :=
  defs.all fun (d, _) => d ≤ p && (dom.getD p []).contains d

def intUsesOK (P : Program) (dom : Array (List Nat)) (b i : Nat)
    (rs : List Nat) : Bool :=
  rs.all fun r => useOK dom (intDefPositions P r) b i

def boolUsesOK (P : Program) (dom : Array (List Nat)) (b i : Nat)
    (rs : List Nat) : Bool :=
  rs.all fun r => useOK dom (boolDefPositions P r) b i

def cmdUsesOK (P : Program) (dom : Array (List Nat)) (b i : Nat) : Cmd → Bool
  | .assignI _ e => intUsesOK P dom b i e.intVars && boolUsesOK P dom b i e.boolVars
  | .assignB _ e => intUsesOK P dom b i e.intVars && boolUsesOK P dom b i e.boolVars
  | .assume φ => intUsesOK P dom b i φ.intVars && boolUsesOK P dom b i φ.boolVars
  | .assert r => boolUsesOK P dom b i [r]
  | .havocI _ | .havocB _ => true
  | .phiI _ arms =>
      arms.all fun (p, src) => armUseOK dom (intDefPositions P src) p
  | .phiB _ arms =>
      arms.all fun (p, src) => armUseOK dom (boolDefPositions P src) p

def termUsesOK (P : Program) (dom : Array (List Nat)) (b : Nat) (B : Block) : Bool :=
  match B.term with
  | .ifGoto c _ _ => boolUsesOK P dom b B.cmds.length [c]
  | _ => true

def usesOK (P : Program) : Bool :=
  P.blocks.zipIdx.all fun (B, b) =>
    (B.cmds.zipIdx.all fun (c, i) => cmdUsesOK P (domTable P) b i c)
      && termUsesOK P (domTable P) b B

/-- W7: block booleans `off + b` must lie above every program bool
register, so the witness can set them independently. -/
def cmdBoolRegs : Cmd → List Nat
  | .assignI _ e => e.boolVars
  | .assignB c e => c :: e.boolVars
  | .havocI _ => []
  | .havocB c => [c]
  | .phiI _ _ => []
  | .phiB c arms => c :: arms.map (·.2)
  | .assume φ => φ.boolVars
  | .assert c => [c]

def boolRegsOf (P : Program) : List Nat :=
  (P.blocks.map fun B =>
    (B.cmds.map cmdBoolRegs).flatten
      ++ (match B.term with | .ifGoto c _ _ => [c] | _ => [])).flatten

def offOK (P : Program) (off : Nat) : Bool :=
  (boolRegsOf P).all (· < off)

/-- W8. -/
def entryOK (P : Program) : Bool :=
  decide (P.entry < P.blocks.length)

def wellFormed (P : Program) (off : Nat) : Bool :=
  singleAssertOK P && ssaOK P && forwardOK P && phiOK P && amoSideOK P
    && offOK P off && entryOK P && domClosedOK P && usesOK P

/-- The checker: well-formed program, and every VC constraint is one the
bwd0 encoder is entitled to emit. Subset is the sound direction -
duplicates and omissions in `vc` are harmless. -/
def checkVC (P : Program) (off : Nat) (vc : List BExp) : Bool :=
  wellFormed P off && vc.all fun c => decide (c ∈ Vc.expected P off)

end Ttac
