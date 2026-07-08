import Ttac.Product

/-!
# Exploration: the rw-eq product under CFG surgery (stuttering mode)

**Status: statement-and-construction probe.** The lockstep development
(`Ttac/Product.lean`) is complete and deliberately simple; this file
explores its extension to CFG surgery — the rewrite `B` drops blocks
of `A` (`ctac cfg-simplify`'s fall-through elimination), so `A`
*stutters* through dropped blocks between synchronization points. The
transfer theorem is stated (`StutterTransfer`, a `Prop`, not proved);
nothing here is imported by the library root.

## The witness

`B`'s blocks are a compacted subsequence of `A`'s, so the
correspondence cannot be positional: the *matching*
`mt : List (Option Nat)` (`mt[a] = some b` iff `A`-block `a` is
`B`-block `b`; `none` marks a stutter block) is untrusted input,
validated by the decidable `surgeryOK` — the Lean-side analog of
rw-eq's `sim_precheck`. Scope of this round, matching what
`cfg-simplify` emits: stutter blocks are single-predecessor `goto`
blocks (linear chains), matched terminators have the same kind, and
each `A`-target *chases* through its chain to a matched block whose
match is `B`'s corresponding target.

## Ownership-routed phis instead of DEST ghosts

The implementation's DEST/IN_DEST flags materialize "After waits for
Before" for the SMT encoding. Denotationally there is no waiting —
both final states just exist — and inside the `WellFormed` fragment
the flags turn out to be unnecessary altogether: the shape that would
genuinely need a committed-destination ghost (two `B`-predecessors of
one join both lying on a single A-path) requires a critical edge — a
branching block feeding a multi-predecessor join — which `amoSideOK`
on `B` forbids, and the chase/kind-matching conditions exclude the
remaining variants. What *does* have to change is arm keying: `B`'s
phi arms name `B`-predecessors in `B`'s compacted index space
(meaningless against the product's guards, which are `A`'s), and `A`
arrives at a join via a chain *tail*, not the divergence point
itself. The product therefore *re-keys* each B-copy phi on `A`'s
CFG: one arm per `A`-predecessor `p` of the join, with source looked
up from `B`'s arm of `matchOf (owner p)` — `owner p` being the
matched block whose stutter chain contains `p` (computable by walking
the single-predecessor chain backwards). Selection then rides `A`'s
at-most-one-active-predecessor exactly as in lockstep, and the DEST
commitment becomes the proof obligation
`matchOf (owner (A's taken pred)) = B's taken pred` instead of
program state.

## Expected proof shape and hypotheses (unproved)

The doubled final-state seeding and the deposit/extraction machinery
of the lockstep proof carry over; the new content is the τ-region
induction (guard transfer skips through chains via the chase) and —
the open risk — cross-CFG dominance: `domTable A = domTable B` is
lost, so `domClosedOK` appears for *both* sides in the conjecture,
and the `GoodB` junk-isolation argument needs a matching-transported
dominance correspondence that this probe does not yet design.
-/

namespace Ttac

open Vc

/-! ## The matching and its derived maps -/

/-- The match of an `A`-block, if any. -/
def matchOf (mt : List (Option Nat)) (a : Nat) : Option Nat :=
  (mt[a]?).getD none

/-- The owning matched block of a stutter block: walk the (validated:
unique) predecessor chain backwards until a matched block. Fuel-bounded
by the block index (predecessors are strictly smaller under
`forwardOK`); a miscomputed owner is rejected by `surgeryOK`, never
trusted. -/
def ownerGo (A : Program) (mt : List (Option Nat)) : Nat → Nat → Nat
  | 0, a => a
  | fuel + 1, a =>
      if (matchOf mt a).isSome then a
      else match predsOf A a with
        | [q] => ownerGo A mt fuel q
        | _ => a

def owner (A : Program) (mt : List (Option Nat)) (a : Nat) : Nat :=
  ownerGo A mt a a

/-- Chase an `A`-target through its stutter chain to the matched block
it resolves to. -/
def chaseGo (A : Program) (mt : List (Option Nat)) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, a =>
      if (matchOf mt a).isSome then some a
      else match A.block? a with
        | some Ba =>
            match Ba.term with
            | .goto t => chaseGo A mt fuel t
            | _ => none
        | none => none

def chase (A : Program) (mt : List (Option Nat)) (a : Nat) : Option Nat :=
  chaseGo A mt A.blocks.length a

/-! ## The surgical product -/

/-- B-copy emission at a matched block: identical to the lockstep
`prodCmdB` except for phis, which are re-keyed on `A`'s predecessors
with ownership-routed sources (see the module docstring). A failed
lookup falls back to register 0 — junk that `surgeryOK`'s routing
check rules out. -/
def prodCmdBS (A : Program) (mt : List (Option Nat)) (Ba : Block)
    (stride k i : Nat) : Cmd → List Cmd
  | .phi t x arms =>
      [.phi t (pv 1 x) ((predsOf A k).map fun p =>
        (p, pv 1 ((lookupArm arms
          ((matchOf mt (owner A mt p)).getD 0)).getD 0)))]
  | c => prodCmdB A Ba stride k i c

/-- Product block: matched blocks interleave both copies plus CHKs
(as in lockstep); stutter blocks carry the A-copy only. -/
def prodBlockS (A B : Program) (mt : List (Option Nat)) (stride k : Nat)
    (Ba : Block) : Block :=
  match matchOf mt k with
  | none =>
      { cmds := Ba.cmds.flatMap prodCmdA, term := Ba.term.rename (pv 0) }
  | some kb =>
      match B.block? kb with
      | none =>
          { cmds := Ba.cmds.flatMap prodCmdA, term := Ba.term.rename (pv 0) }
      | some Bb =>
          { cmds := Ba.cmds.flatMap prodCmdA
              ++ Bb.cmds.zipIdx.flatMap (fun ci =>
                  prodCmdBS A mt Ba stride k ci.2 ci.1)
              ++ prodTermChk stride k Ba Bb
            term := Ba.term.rename (pv 0) }

def productS (A B : Program) (mt : List (Option Nat)) : Program where
  blocks := A.blocks.zipIdx.map fun p =>
    prodBlockS A B mt (chkStride B.blocks) p.2 p.1
  entry := A.entry
  exit := A.exit

/-! ## The validator -/

/-- The `A`-target `ta` resolves through its chain to `B`'s target
`tb`. -/
def chaseTargetOK (A B : Program) (mt : List (Option Nat))
    (ta tb : Nat) : Bool :=
  match chase A mt ta with
  | some t' => matchOf mt t' == some tb && tb < B.blocks.length
  | none => false

/-- Matched terminators: same kind, targets correspond through the
chase. Conditions are free to differ (they get the branch CHK). -/
def termSurgeryOK (A B : Program) (mt : List (Option Nat)) :
    Terminator → Terminator → Bool
  | .halt, .halt => true
  | .goto ta, .goto tb => chaseTargetOK A B mt ta tb
  | .ifGoto _ ta ea, .ifGoto _ tb eb =>
      chaseTargetOK A B mt ta tb && chaseTargetOK A B mt ea eb
  | _, _ => false

/-- Round-1 stutter-block discipline: a single-predecessor `goto`
block with no assert (matching `cfg-simplify`'s fall-through shape). -/
def stutterBlockOK (A : Program) (a : Nat) (Ba : Block) : Bool :=
  (match Ba.term with | .goto _ => true | _ => false)
    && decide ((predsOf A a).length = 1)
    && Ba.cmds.all fun c =>
        match c with | .assert _ => false | _ => true

/-- Every `A`-predecessor of a matched phi block routes: its owner is
matched, and `B`'s phi has an arm for the owner's match. -/
def phiRouteOK (A : Program) (mt : List (Option Nat)) (k : Nat)
    (Bb : Block) : Bool :=
  Bb.cmds.all fun c =>
    match c with
    | .phi _ _ arms =>
        (predsOf A k).all fun p =>
          match matchOf mt (owner A mt p) with
          | some ob => (lookupArm arms ob).isSome
          | none => false
    | _ => true

/-- The full witness check — the Lean-side `sim_precheck`. -/
def surgeryOK (A B : Program) (mt : List (Option Nat)) : Bool :=
  decide (mt.length = A.blocks.length)
    && (matchOf mt A.entry == some B.entry)
    && (A.blocks.zipIdx.all fun (Ba, k) =>
        match matchOf mt k with
        | none => stutterBlockOK A k Ba
        | some kb =>
            match B.block? kb with
            | none => false
            | some Bb =>
                termSurgeryOK A B mt Ba.term Bb.term
                  && phiRouteOK A mt k Bb)
    -- the matching is strictly monotone (a subsequence), hence injective
    && ((List.range A.blocks.length).all fun a =>
        (List.range a).all fun a' =>
          match matchOf mt a', matchOf mt a with
          | some b', some b => decide (b' < b)
          | _, _ => true)
    -- the single asserts sit at matched blocks that correspond
    && (match assertSites A, assertSites B with
        | [(aB, _, _)], [(bB, _, _)] => matchOf mt aB == some bB
        | _, _ => false)

/-! ## The conjecture -/

/-- The stuttering transfer, stated. Note `domClosedOK` on *both*
sides: the lockstep proof derived `A`'s from `B`'s via table equality,
which CFG surgery forfeits — the cross-CFG dominance correspondence is
the open design question of the eventual proof. -/
def StutterTransfer : Prop :=
  ∀ (A B : Program) (mt : List (Option Nat)),
    WellFormed A → WellFormed B →
    domClosedOK A = true → domClosedOK B = true →
    phiCoversOK B = true → surgeryOK A B mt = true →
    Safe_denot (productS A B mt) → Safe_denot B → Safe_denot A

end Ttac
