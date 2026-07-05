import Ttac.Vars

/-!
# VC representation and the expected-constraint generator

`ttac vcgen` (Python, bwd0 encoding) emits an SMT VC over the program's
scalar registers plus per-block reachability booleans. The unverified
transpiler maps that VC to a `List BExp`: block `b` becomes the guard
atom `.blk b` and the synthetic `BLK_EXIT` becomes
`.blk P.blocks.length` - a namespace disjoint from program registers by
construction.

`expected P` recomputes, in Lean, the full list of constraints the
encoder is entitled to emit. The fold helpers (`mkImp`, `mkOr`, ...)
mirror the Python constant folding (`smt/util.py`, `smt/vc/terms.py`)
exactly - including quirks like keep-first dedup and the *unfolded*
at-most-one clauses - so real vcgen output matches structurally. A
constraint the encoder folds away entirely is represented as
`.lit true` and simply kept in the list (never matched, trivially
satisfied).

Soundness (`VcSound.lean`) only needs the subset direction: every
member of `expected` is satisfied by the witness built from a failing
execution, so any `vc ⊆ expected` is satisfiable when the program is
unsafe.
-/

namespace Ttac

namespace Vc

/-! ## Guards -/

/-- The block-reachability term. The entry block's guard is the literal
`true` (the Python encoder never declares `BLK_entry`); every other
block `b` is the dedicated guard atom `.blk b`. -/
def guardOf (P : Program) (b : Nat) : BExp :=
  if b = P.entry then .lit true else .blk b

/-- The synthetic `BLK_EXIT`: guard index one past the last block. -/
def exitVar (P : Program) : BExp :=
  .blk P.blocks.length

/-! ## Fold helpers - exact mirrors of the Python term constructors -/

/-- `implies`: `(=> true φ) → φ`; `(=> g true) → true` (a literal-`true`
fact is dropped by the encoder; we keep it as `.lit true`). -/
def mkImp : BExp → BExp → BExp
  | .lit true, φ => φ
  | _, .lit true => .lit true
  | g, φ => .imp g φ

/-- `not_`: folds literals only. -/
def mkNot : BExp → BExp
  | .lit true => .lit false
  | .lit false => .lit true
  | a => .not a

/-- Binary `and_`: drop `true`, `false` dominates, dedup. -/
def mkAnd2 (a b : BExp) : BExp :=
  if a = .lit true then b
  else if b = .lit true then a
  else if a = .lit false ∨ b = .lit false then .lit false
  else if a = b then a
  else .and a b

/-- Binary `or_`: drop `false`, `true` dominates, dedup. -/
def mkOr2 (a b : BExp) : BExp :=
  if a = .lit false then b
  else if b = .lit false then a
  else if a = .lit true ∨ b = .lit true then .lit true
  else if a = b then a
  else .or a b

/-- Keep-first dedup (Python `seen`-set semantics). Filtering after the
recursive call keeps the recursion structural; the result is the same. -/
def dedup1 : List BExp → List BExp
  | [] => []
  | x :: xs => x :: (dedup1 xs).filter (· ≠ x)

/-- n-ary `(or a b c ...)` as the right-nested binary chain - the same
nesting the transpiler uses for n-ary SMT `or`. -/
def orChain : BExp → List BExp → BExp
  | a, [] => a
  | a, b :: r => .or a (orChain b r)

/-- `util.or_terms`: keep-first dedup, `true` short-circuit, drop
`false`, singleton collapse. -/
def mkOr (l : List BExp) : BExp :=
  let u := dedup1 l
  if BExp.lit true ∈ u then .lit true
  else
    match u.filter (· ≠ .lit false) with
    | [] => .lit false
    | [d] => d
    | d :: ds => orChain d ds

/-- All ordered pairs `(xᵢ, xⱼ)` with `i < j` (Python's nested loop order). -/
def pairsLt : List BExp → List (BExp × BExp)
  | [] => []
  | x :: xs => xs.map (fun y => (x, y)) ++ pairsLt xs

/-- `util.at_most_one_terms`: pairwise `(or (not gᵢ) (not gⱼ))` over the
dedup'd, `false`-filtered guard list. NO folding inside - when the entry
guard (`.lit true`) is among the guards, `(or (not true) (not g))`
appears verbatim, matching the Python output. -/
def amoClauses (l : List BExp) : List BExp :=
  (pairsLt (dedup1 (l.filter (· ≠ .lit false)))).map
    fun (a, b) => .or (.not a) (.not b)

/-- `terms.ite` on int results: identical arms collapse, literal guards
select. -/
def mkIteI (c : BExp) (t e : IExp) : IExp :=
  if t = e then t
  else match c with
    | .lit true => t
    | .lit false => e
    | c => .ite c t e

/-- `terms.ite` on bool results: identical arms, literal guards, and the
bool-literal-arm folds. -/
def mkIteB (c t e : BExp) : BExp :=
  if t = e then t
  else match c, t, e with
    | .lit true, t, _ => t
    | .lit false, _, e => e
    | c, .lit true, .lit false => c
    | c, .lit false, .lit true => mkNot c
    | c, t, e => .ite c t e

/-! ## Lowering mirror

The Python lowerer routes program `not/and/or/ite` through the folding
constructors, so the term printed for a program expression is the
*folded* form. `lowerI`/`lowerB` reproduce it; arithmetic and
comparisons pass through untouched. -/

mutual
  def lowerI : IExp → IExp
    | .lit n => .lit n
    | .var x => .var x
    | .add a b => .add (lowerI a) (lowerI b)
    | .sub a b => .sub (lowerI a) (lowerI b)
    | .mul a b => .mul (lowerI a) (lowerI b)
    | .div a b => .div (lowerI a) (lowerI b)
    | .ite c t e => mkIteI (lowerB c) (lowerI t) (lowerI e)

  def lowerB : BExp → BExp
    | .lit b => .lit b
    | .var c => .var c
    | .le a b => .le (lowerI a) (lowerI b)
    | .lt a b => .lt (lowerI a) (lowerI b)
    | .eqI a b => .eqI (lowerI a) (lowerI b)
    | .eqB a b => .eqB (lowerB a) (lowerB b)
    | .not a => mkNot (lowerB a)
    | .and a b => mkAnd2 (lowerB a) (lowerB b)
    | .or a b => mkOr2 (lowerB a) (lowerB b)
    | .ite c t e => mkIteB (lowerB c) (lowerB t) (lowerB e)
    | .imp a b => mkImp (lowerB a) (lowerB b)
    | .blk b => .blk b
end

/-! ## CFG edges -/

/-- Out-edges of block `p` in emission order: goto contributes cond
`.lit true`; ifGoto contributes the then-edge on `.var c` before the
else-edge on `.not (.var c)`. -/
def outEdges (p : Nat) (B : Block) : List (Nat × Nat × BExp) :=
  match B.term with
  | .halt => []
  | .goto t => [(p, t, .lit true)]
  | .ifGoto c t e => [(p, t, .var c), (p, e, .not (.var c))]

def allEdges (P : Program) : List (Nat × Nat × BExp) :=
  (P.blocks.zipIdx.map fun (B, p) => outEdges p B).flatten

/-- In-edges of block `S`: `(pred, edge condition)` in emission order. -/
def edgesTo (P : Program) (S : Nat) : List (Nat × BExp) :=
  (allEdges P).filterMap fun (p, s, c) => if s = S then some (p, c) else none

/-! ## Phi right-hand sides

Shared between the phi constraint and the replay witness, so the
satisfaction proof for phi equations is by construction. The ITE chain
selects on the *predecessor block guards* in arm order; the last arm is
the else-tail. -/

def phiChainI (P : Program) : (Nat × Nat) → List (Nat × Nat) → IExp
  | (_, s), [] => .var s
  | (p, s), a :: r => mkIteI (guardOf P p) (.var s) (phiChainI P a r)

def phiRhsI (P : Program) (arms : PhiArms) : IExp :=
  match arms with
  | [] => .lit 0
  | a :: r => phiChainI P a r

def phiChainB (P : Program) : (Nat × Nat) → List (Nat × Nat) → BExp
  | (_, s), [] => .var s
  | (p, s), a :: r => mkIteB (guardOf P p) (.var s) (phiChainB P a r)

def phiRhsB (P : Program) (arms : PhiArms) : BExp :=
  match arms with
  | [] => .lit false
  | a :: r => phiChainB P a r

/-! ## The expected constraint set -/

def cmdConstraints (P : Program) (b : Nat) : Cmd → List BExp
  | .assignI x e => [mkImp (guardOf P b) (.eqI (.var x) (lowerI e))]
  | .assignB c e => [mkImp (guardOf P b) (.eqB (.var c) (lowerB e))]
  | .havocI _ | .havocB _ => []
  | .assume φ => [mkImp (guardOf P b) (lowerB φ)]
  | .assert _ => []
  | .phiI x arms =>
      BExp.eqI (.var x) (phiRhsI P arms)
        :: (if 2 ≤ arms.length then
              amoClauses (arms.map fun (p, _) => guardOf P p)
            else [])
  | .phiB c arms =>
      BExp.eqB (.var c) (phiRhsB P arms)
        :: (if 2 ≤ arms.length then
              amoClauses (arms.map fun (p, _) => guardOf P p)
            else [])

def cfgConstraints (P : Program) : List BExp :=
  ((List.range P.blocks.length).map fun S =>
    if S = P.entry then []
    else
      let ins := edgesTo P S
      let gS := guardOf P S
      let edgeTerms := ins.map fun (p, cond) => mkAnd2 (guardOf P p) cond
      let predTerms := ins.map fun (p, _) => guardOf P p
      mkImp gS (mkOr edgeTerms)
        :: mkImp gS (mkOr predTerms)
        :: (amoClauses predTerms).map (mkImp gS)).flatten

/-- `(block index, cmd index, cond register)` of every assert. -/
def assertSites (P : Program) : List (Nat × Nat × Nat) :=
  (P.blocks.zipIdx.map fun (B, b) =>
    B.cmds.zipIdx.filterMap fun (c, i) =>
      match c with
      | .assert r => some (b, i, r)
      | _ => none).flatten

def objective (P : Program) (aB okReg : Nat) : List BExp :=
  [ mkImp (exitVar P) (mkAnd2 (guardOf P aB) (mkNot (.var okReg))),
    exitVar P ]

/-- Every constraint the bwd0 encoder is entitled to emit for `P`. -/
def expected (P : Program) : List BExp :=
  match assertSites P with
  | [(aB, _, okReg)] =>
      (P.blocks.zipIdx.map fun (B, b) =>
        (B.cmds.map (cmdConstraints P b)).flatten).flatten
        ++ cfgConstraints P ++ objective P aB okReg
  | _ => []

/-! ## Satisfaction -/

def Sat (w : State) (vc : List BExp) : Prop := ∀ c ∈ vc, evalB w c = true

def Unsat (vc : List BExp) : Prop := ¬∃ w, Sat w vc

end Vc

end Ttac
