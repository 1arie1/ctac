import Ttac.Vc

/-!
# The VC checker

`checkVC P vc` validates a transpiled VC against a program:
well-formedness of `P` (the side conditions under which the bwd0
encoding is complete) plus membership of every VC constraint in
`Vc.expected P`. All checks are `Bool`-valued so a per-instance
`theorem ... := by native_decide` discharges them.

Definition sites and uses are checked uniformly over `(sort, register)`
pairs via the effect table `Cmd.def?` and the collector `Exp.vars` -
no per-sort checker duplication.

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

/-- Positions of every definition of register `tx = (sort, index)`. -/
def defPositions (P : Program) (tx : Ty × Nat) : List Pos :=
  (P.blocks.zipIdx.map fun (B, b) =>
    B.cmds.zipIdx.filterMap fun (c, i) =>
      if c.def? = some tx then some ((b, i) : Pos) else none).flatten

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
  match c.def? with
  | some tx => (defPositions P tx).all fun q => decide (q = ((b, i) : Pos))
  | none => true

/-- W2: pure SSA - each register (per sort) defined at most once
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
      | .phi _ _ arms => phiArmsOK P b arms
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

/-- Every register an expression reads is dominated at `(b, i)` - one
pass over the `(sort, register)` inventory, no per-sort split. -/
def expUsesOK (P : Program) (dom : Array (List Nat)) (b i : Nat)
    {t : Ty} (e : Exp t) : Bool :=
  e.vars.all fun tx => useOK dom (defPositions P tx) b i

def cmdUsesOK (P : Program) (dom : Array (List Nat)) (b i : Nat) : Cmd → Bool
  | .assign _ _ e => expUsesOK P dom b i e
  | .assume φ => expUsesOK P dom b i φ
  | .assert r => useOK dom (defPositions P (.bool, r)) b i
  | .havoc _ _ => true
  | .phi t _ arms =>
      arms.all fun (p, src) => armUseOK dom (defPositions P (t, src)) p

def termUsesOK (P : Program) (dom : Array (List Nat)) (b : Nat) (B : Block) : Bool :=
  match B.term with
  | .ifGoto c _ _ => useOK dom (defPositions P (.bool, c)) b B.cmds.length
  | _ => true

def usesOK (P : Program) : Bool :=
  P.blocks.zipIdx.all fun (B, b) =>
    (B.cmds.zipIdx.all fun (c, i) => cmdUsesOK P (domTable P) b i c)
      && termUsesOK P (domTable P) b B

/-- W7: the entry block is block 0 and the program is nonempty. Under
forward edges block 0 can have no predecessors, so this is what the
Python generator produces anyway; requiring it keeps the guard
convention uniform. -/
def entryOK (P : Program) : Bool :=
  decide (P.entry = 0) && decide (0 < P.blocks.length)

/-- W8: program expressions never mention guard atoms (`.blk`). ttac
programs cannot express them, but the checker quantifies over arbitrary
deep programs, and a guard-reading expression would let the program
observe the witness's guard assignment. -/
def cmdGuardFree : Cmd → Bool
  | .assign _ _ e => e.blkVars.isEmpty
  | .assume φ => φ.blkVars.isEmpty
  | _ => true

def guardFreeOK (P : Program) : Bool :=
  P.blocks.all fun B => B.cmds.all cmdGuardFree

def wellFormed (P : Program) : Bool :=
  singleAssertOK P && ssaOK P && forwardOK P && phiOK P && amoSideOK P
    && entryOK P && guardFreeOK P && domClosedOK P && usesOK P

/-- Prop-level bundle of `wellFormed`'s *program-shape* conjuncts, so
proof statements take one hypothesis instead of eight. Deliberately
excludes `domClosedOK` (the dominator-table certificate): the
denotational/VC development is dominance-free, and keeping `hdc` a
separate explicit hypothesis makes that boundary visible in the
signatures — only adequacy consumes it. -/
structure WellFormed (P : Program) : Prop where
  one : singleAssertOK P = true
  ssa : ssaOK P = true
  fwd : forwardOK P = true
  phi : phiOK P = true
  amo : amoSideOK P = true
  entry : entryOK P = true
  gf : guardFreeOK P = true
  uses : usesOK P = true

theorem wellFormed_iff {P : Program} :
    wellFormed P = true ↔ WellFormed P ∧ domClosedOK P = true := by
  constructor
  · intro hwf
    rw [wellFormed] at hwf
    simp only [Bool.and_eq_true] at hwf
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨hone, hssa⟩, hfwd⟩, hphi⟩, hamo⟩, hentry⟩, hgf⟩, hdc⟩,
      huse⟩ := hwf
    exact ⟨⟨hone, hssa, hfwd, hphi, hamo, hentry, hgf, huse⟩, hdc⟩
  · intro ⟨hwf, hdc⟩
    rw [wellFormed]
    simp only [Bool.and_eq_true]
    exact ⟨⟨⟨⟨⟨⟨⟨⟨hwf.one, hwf.ssa⟩, hwf.fwd⟩, hwf.phi⟩, hwf.amo⟩,
      hwf.entry⟩, hwf.gf⟩, hdc⟩, hwf.uses⟩

/-- The checker: well-formed program, every VC constraint is one the
bwd0 encoder is entitled to emit, and every map definition is one of
the program's. Subset is the sound direction - duplicates and
omissions in `vc` are harmless. -/
def checkVC (P : Program) (vc : Vc.VC) : Bool :=
  wellFormed P
    && vc.constraints.all (fun c => decide (c ∈ Vc.expected P))
    && vc.mapDefs.all (fun md => decide (md ∈ Vc.expectedMapDefs P))

end Ttac
