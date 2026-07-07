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
`.litB true` and simply kept in the list (never matched, trivially
satisfied).

The per-command constraint shape is table-driven: `Cmd.factB` supplies
the boolean fact and the constraint is `guard ⇒ lower(fact)`; only phi
(whose constraint is predecessor-indexed) is special-cased. Commands
without a bool-expressible fact contribute nothing.

Folds are written with named binders and term-level matches (never
equation-style) so `unfold f; split` works in the characterization
lemmas — equation-style non-recursive defs wrap a vacuous outer match
that blocks `split`.

Soundness (`VcDenot.lean`) only needs the subset direction: every
member of `expected` is satisfied by the denotational run of a failing
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
  if b = P.entry then .litB true else .blk b

/-- The synthetic `BLK_EXIT`: guard index one past the last block. -/
def exitVar (P : Program) : BExp :=
  .blk P.blocks.length

/-! ## Fold helpers - exact mirrors of the Python term constructors -/

/-- `implies`: `(=> true φ) → φ`; `(=> g true) → true` (a literal-`true`
fact is dropped by the encoder; we keep it as `.litB true`). -/
def mkImp (g φ : BExp) : BExp :=
  match g, φ with
  | .litB true, φ => φ
  | _, .litB true => .litB true
  | g, φ => .bin .imp g φ

/-- `not_`: folds literals only. -/
def mkNot (a : BExp) : BExp :=
  match a with
  | .litB true => .litB false
  | .litB false => .litB true
  | a => .un .not a

/-- Binary `and_`: drop `true`, `false` dominates, dedup. -/
def mkAnd2 (a b : BExp) : BExp :=
  if a = .litB true then b
  else if b = .litB true then a
  else if a = .litB false ∨ b = .litB false then .litB false
  else if a = b then a
  else .bin .and a b

/-- Binary `or_`: drop `false`, `true` dominates, dedup. -/
def mkOr2 (a b : BExp) : BExp :=
  if a = .litB false then b
  else if b = .litB false then a
  else if a = .litB true ∨ b = .litB true then .litB true
  else if a = b then a
  else .bin .or a b

/-- Keep-first dedup (Python `seen`-set semantics). Filtering after the
recursive call keeps the recursion structural; the result is the same. -/
def dedup1 : List BExp → List BExp
  | [] => []
  | x :: xs => x :: (dedup1 xs).filter (· ≠ x)

/-- n-ary `(or a b c ...)` as the right-nested binary chain - the same
nesting the transpiler uses for n-ary SMT `or`. -/
def orChain : BExp → List BExp → BExp
  | a, [] => a
  | a, b :: r => .bin .or a (orChain b r)

/-- `util.or_terms`: keep-first dedup, `true` short-circuit, drop
`false`, singleton collapse. -/
def mkOr (l : List BExp) : BExp :=
  let u := dedup1 l
  if Exp.litB true ∈ u then .litB true
  else
    match u.filter (· ≠ .litB false) with
    | [] => .litB false
    | [d] => d
    | d :: ds => orChain d ds

/-- All ordered pairs `(xᵢ, xⱼ)` with `i < j` (Python's nested loop order). -/
def pairsLt : List BExp → List (BExp × BExp)
  | [] => []
  | x :: xs => xs.map (fun y => (x, y)) ++ pairsLt xs

/-- `util.at_most_one_terms`: pairwise `(or (not gᵢ) (not gⱼ))` over the
dedup'd, `false`-filtered guard list. NO folding inside - when the entry
guard (`.litB true`) is among the guards, `(or (not true) (not g))`
appears verbatim, matching the Python output. -/
def amoClauses (l : List BExp) : List BExp :=
  (pairsLt (dedup1 (l.filter (· ≠ .litB false)))).map
    fun (a, b) => .bin .or (.un .not a) (.un .not b)

/-- `terms.ite`, polymorphic in the result sort: identical arms
collapse, literal guards select, and the bool-literal-arm folds apply
exactly at `t = .bool` (index unification prunes those arms at other
sorts — this single definition is the v1 `mkIteI` at `.int` and
`mkIteB` at `.bool`). -/
def mkIte {t : Ty} (c : BExp) (th el : Exp t) : Exp t :=
  if th = el then th
  else match c, th, el with
    | .litB true, th, _ => th
    | .litB false, _, el => el
    | c, .litB true, .litB false => c
    | c, .litB false, .litB true => mkNot c
    | c, th, el => .ite c th el

abbrev mkIteI (c : BExp) (t e : IExp) : IExp := mkIte c t e
abbrev mkIteB (c t e : BExp) : BExp := mkIte c t e

/-! ## Lowering mirror

The Python lowerer routes program `not/and/or/ite` (and the transpiler
routes `=>`) through the folding constructors, so the term printed for
a program expression is the *folded* form. `lower` reproduces it;
arithmetic, comparisons, and map operators pass through untouched. -/

/-- Folding application of a unary operator (the operators the Python
side folds route through their `mk*`; the rest apply bare). -/
def unFold : {a c : Ty} → UnOp a c → Exp a → Exp c
  | _, _, .not, e => mkNot e

/-- Folding application of a binary operator. -/
def binFold : {a b c : Ty} → BinOp a b c → Exp a → Exp b → Exp c
  | _, _, _, .and, l, r => mkAnd2 l r
  | _, _, _, .or, l, r => mkOr2 l r
  | _, _, _, .imp, l, r => mkImp l r
  | _, _, _, .add, l, r => .bin .add l r
  | _, _, _, .sub, l, r => .bin .sub l r
  | _, _, _, .mul, l, r => .bin .mul l r
  | _, _, _, .div, l, r => .bin .div l r
  | _, _, _, .le, l, r => .bin .le l r
  | _, _, _, .lt, l, r => .bin .lt l r
  | _, _, _, .eqI, l, r => .bin .eqI l r
  | _, _, _, .eqB, l, r => .bin .eqB l r
  | _, _, _, .select, l, r => .bin .select l r

def lower : {t : Ty} → Exp t → Exp t
  | _, .litI n => .litI n
  | _, .litB b => .litB b
  | _, .var t x => .var t x
  | _, .blk b => .blk b
  | _, .un op a => unFold op (lower a)
  | _, .bin op l r => binFold op (lower l) (lower r)
  | _, .tern op e₁ e₂ e₃ => .tern op (lower e₁) (lower e₂) (lower e₃)
  | _, .ite c th el => mkIte (lower c) (lower th) (lower el)

/-! ## CFG edges -/

/-- Out-edges of block `p` in emission order: goto contributes cond
`.litB true`; ifGoto contributes the then-edge on `.var .bool c` before
the else-edge on its negation. -/
def outEdges (p : Nat) (B : Block) : List (Nat × Nat × BExp) :=
  match B.term with
  | .halt => []
  | .goto t => [(p, t, .litB true)]
  | .ifGoto c t e =>
      [(p, t, .var .bool c), (p, e, .un .not (.var .bool c))]

def allEdges (P : Program) : List (Nat × Nat × BExp) :=
  (P.blocks.zipIdx.map fun (B, p) => outEdges p B).flatten

/-- In-edges of block `S`: `(pred, edge condition)` in emission order. -/
def edgesTo (P : Program) (S : Nat) : List (Nat × BExp) :=
  (allEdges P).filterMap fun (p, s, c) => if s = S then some (p, c) else none

/-! ## Phi right-hand sides

Shared between the phi constraint and the definitional-extension
witness, so the satisfaction proof for phi equations is by
construction. The ITE chain selects on the *predecessor block guards*
in arm order; the last arm is the else-tail. -/

def phiChain (P : Program) (t : Ty) : (Nat × Nat) → List (Nat × Nat) → Exp t
  | (_, s), [] => .var t s
  | (p, s), a :: r => mkIte (guardOf P p) (.var t s) (phiChain P t a r)

/-- The empty-arms placeholder is unreachable under `phiOK` (arms are
nonempty); any term works. -/
def phiRhs (P : Program) (t : Ty) (arms : PhiArms) : Exp t :=
  match arms with
  | [] => .var t 0
  | a :: r => phiChain P t a r

/-- The map-sorted defining equations, as the VC carries them. Scalar
phi equations are boolean constraints (`cmdConstraints`); map
definitions have no boolean form (no map equality operator) and are
checked as first-class definitions instead. -/
def cmdMapDef? (P : Program) : Cmd → Option (Nat × MExp)
  | .assign .map x e => some (x, lower e)
  | .phi .map x arms => some (x, phiRhs P .map arms)
  | _ => none

/-- Every map definition the encoder is entitled to emit for `P`. -/
def expectedMapDefs (P : Program) : List (Nat × MExp) :=
  (P.blocks.map fun B => B.cmds.filterMap (cmdMapDef? P)).flatten

/-! ## The expected constraint set -/

/-- The constraint a command's boolean fact contributes:
`guard ⇒ lower(fact)`, or nothing. Generic over the effect table - a
new local instruction gets its constraint (and its slice of the
soundness proof) from its `factB` row. -/
def factConstraints (P : Program) (b : Nat) (c : Cmd) : List BExp :=
  match c.factB with
  | some f => [mkImp (guardOf P b) (lower f)]
  | none => []

/-- Per-command constraints: phi contributes its (unguarded) defining
equation - at sorts that have one - plus the at-most-one clauses over
its arm guards; everything else is table-driven via `factConstraints`. -/
def cmdConstraints (P : Program) (b : Nat) : Cmd → List BExp
  | .phi t x arms =>
      (match eqConstraint? t x (phiRhs P t arms) with
        | some eq => [eq]
        | none => [])
      ++ (if 2 ≤ arms.length then
            amoClauses (arms.map fun (p, _) => guardOf P p)
          else [])
  | c => factConstraints P b c

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
  [ mkImp (exitVar P) (mkAnd2 (guardOf P aB) (mkNot (.var .bool okReg))),
    exitVar P ]

/-- Every constraint the bwd0 encoder is entitled to emit for `P`. -/
def expected (P : Program) : List BExp :=
  match assertSites P with
  | [(aB, _, okReg)] =>
      (P.blocks.zipIdx.map fun (B, b) =>
        (B.cmds.map (cmdConstraints P b)).flatten).flatten
        ++ cfgConstraints P ++ objective P aB okReg
  | _ => []

/-! ## The VC and its satisfaction

A transpiled VC has two parts: the boolean constraints (the smt2
asserts) and the map definitions (the smt2 `define-fun`s, read as
defining equations). Map definitions are satisfied at the `Prop` level
- pointwise equality of `Int → Int` denotations - never Bool-decided;
the *checker* only compares them structurally. -/

structure VC where
  constraints : List BExp
  mapDefs : List (Nat × MExp) := []
deriving Repr, DecidableEq

def Sat (w : State) (vc : VC) : Prop :=
  (∀ c ∈ vc.constraints, c.eval w = true)
    ∧ ∀ md ∈ vc.mapDefs, w.regs .map md.1 = md.2.eval w

/-- The full VC the bwd0 encoder is entitled to emit — the reference
object the by-construction lemmas satisfy. -/
def expectedVC (P : Program) : VC :=
  { constraints := expected P, mapDefs := expectedMapDefs P }

def Unsat (vc : VC) : Prop := ¬∃ w, Sat w vc

end Vc

end Ttac
