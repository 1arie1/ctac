/-!
# Tiny TAC deep embedding: abstract syntax

The syntax is *sort-indexed*: one register file and one expression type,
indexed by `Ty`. Registers are `Nat`-numbered with a separate namespace
per sort (`.var .int 0` and `.var .bool 0` are different registers), so
well-typedness holds by construction — there is no way to write an
ill-typed expression, and no typing judgment exists.

Operators live in *signature-indexed tables* (`UnOp`/`BinOp`/`TernOp`),
not in the expression type: evaluation, the variable collectors, and the
congruence lemma are written once over `un`/`bin`/`tern` and never
mention an individual operator. Adding an operator is a table row (a
constructor here, a denotation in `Eval.lean`, a Python spelling), never
a proof change.

Sort-specific literals (`litI`/`litB`, no map literals) keep
`DecidableEq` derivable — `Int → Int` has no decidable equality, and
`checkVC`'s membership test needs terms-as-data with decidable equality.
There is deliberately no equality operator at `.map` for the same reason
on the evaluation side.

Blocks are referenced by `Nat` index into `Program.blocks`. The `ttac`
surface language's purified-condition discipline (assert and branch
conditions are *named* bool registers, never expressions) is enforced
structurally: `Cmd.assert` and `Terminator.ifGoto` carry a register
number.

Commands are sort-indexed too (`assign t x e` subsumes the v1
`assignI`/`assignB`), and each is characterized by derived *effect
tables*: `Cmd.def?` (the write footprint) and `Cmd.factB` (the boolean
fact a step establishes, when one is expressible). The proof layers
consume the tables, not the constructors, wherever possible.
-/

namespace Ttac

/-- Register sorts. `.map` (bytemaps, `Int → Int`) is present from day
one; the Phase-A checker rejects `.map`-sorted programs and VCs until
the memory client lands. -/
inductive Ty : Type where
  | int
  | bool
  | map
deriving Repr, DecidableEq

/-- What a register of each sort holds. `@[reducible]` so instance
resolution and the `Decidable` coercion see through it. -/
@[reducible] def Ty.denote : Ty → Type
  | .int => Int
  | .bool => Bool
  | .map => Int → Int

/-! ## Operator tables -/

inductive UnOp : Ty → Ty → Type where
  | not : UnOp .bool .bool
deriving Repr, DecidableEq

inductive BinOp : Ty → Ty → Ty → Type where
  | add : BinOp .int .int .int
  | sub : BinOp .int .int .int
  | mul : BinOp .int .int .int
  /-- SMT-LIB Euclidean division. -/
  | div : BinOp .int .int .int
  | le : BinOp .int .int .bool
  | lt : BinOp .int .int .bool
  | eqI : BinOp .int .int .bool
  | eqB : BinOp .bool .bool .bool
  | and : BinOp .bool .bool .bool
  | or : BinOp .bool .bool .bool
  /-- SMT-LIB `(=> a b)`; occurs only in transpiled VC formulas. -/
  | imp : BinOp .bool .bool .bool
  /-- Bytemap read `M[i]`. -/
  | select : BinOp .map .int .int
deriving Repr, DecidableEq

inductive TernOp : Ty → Ty → Ty → Ty → Type where
  /-- Bytemap functional update `M[i := v]`. -/
  | store : TernOp .map .int .int .map
deriving Repr, DecidableEq

/-! ## Expressions -/

/-- Sort-indexed expressions. `blk b` is the block-reachability guard
`BLK_<b>` (index `P.blocks.length` is the synthetic `BLK_EXIT`); guards
occur only in transpiled VC formulas, never in programs — keeping them
a separate constructor makes their disjointness from program bool
registers hold by construction. -/
inductive Exp : Ty → Type where
  | litI (n : Int) : Exp .int
  | litB (b : Bool) : Exp .bool
  | var (t : Ty) (x : Nat) : Exp t
  | blk (b : Nat) : Exp .bool
  | un {a c : Ty} (op : UnOp a c) (e : Exp a) : Exp c
  | bin {a b c : Ty} (op : BinOp a b c) (l : Exp a) (r : Exp b) : Exp c
  | tern {a b c d : Ty} (op : TernOp a b c d)
      (e₁ : Exp a) (e₂ : Exp b) (e₃ : Exp c) : Exp d
  | ite {t : Ty} (c : Exp .bool) (th el : Exp t) : Exp t
deriving Repr, DecidableEq

abbrev IExp := Exp .int
abbrev BExp := Exp .bool
abbrev MExp := Exp .map

namespace Exp

/-! Smart constructors: construction sites (generated programs, VC
lists, goldens) keep the familiar operator spellings; folds and proofs
pattern-match the real `un`/`bin`/`tern` constructors. All are
definitionally equal to their expansions. -/

abbrev add (l r : IExp) : IExp := .bin .add l r
abbrev sub (l r : IExp) : IExp := .bin .sub l r
abbrev mul (l r : IExp) : IExp := .bin .mul l r
abbrev div (l r : IExp) : IExp := .bin .div l r
abbrev le (l r : IExp) : BExp := .bin .le l r
abbrev lt (l r : IExp) : BExp := .bin .lt l r
abbrev eqI (l r : IExp) : BExp := .bin .eqI l r
abbrev eqB (l r : BExp) : BExp := .bin .eqB l r
abbrev and (l r : BExp) : BExp := .bin .and l r
abbrev or (l r : BExp) : BExp := .bin .or l r
abbrev imp (l r : BExp) : BExp := .bin .imp l r
abbrev not (e : BExp) : BExp := .un .not e
abbrev select (m : MExp) (i : IExp) : IExp := .bin .select m i
abbrev store (m : MExp) (i v : IExp) : MExp := .tern .store m i v

end Exp

/-- The defining equation `x = e` as a boolean constraint, at sorts
that have an equality operator. `none` at `.map`: a map definition is
not bool-expressible and is handled as a first-class definition by the
VC layer instead. -/
def eqConstraint? : (t : Ty) → Nat → Exp t → Option BExp
  | .int, x, e => some (.bin .eqI (.var .int x) e)
  | .bool, x, e => some (.bin .eqB (.var .bool x) e)
  | .map, _, _ => none

/-! ## Commands -/

/-- Phi arms: `(predecessor block index, source register index)`. -/
abbrev PhiArms := List (Nat × Nat)

inductive Cmd : Type where
  | assign (t : Ty) (x : Nat) (e : Exp t)
  | havoc (t : Ty) (x : Nat)
  | phi (t : Ty) (x : Nat) (arms : PhiArms)
  | assume (φ : BExp)
  | assert (c : Nat)
deriving Repr, DecidableEq

namespace Cmd

/-- Effect table: write footprint. A command writes at most one
register; `(sort, index)` identifies it. -/
def def? : Cmd → Option (Ty × Nat)
  | .assign t x _ => some (t, x)
  | .havoc t x => some (t, x)
  | .phi t x _ => some (t, x)
  | .assume _ | .assert _ => none

/-- Effect table: the boolean fact a step of the command establishes at
its post-state. `none` when there is no such fact (havoc, assert), when
it is not bool-expressible (`assign .map` — there is no map equality
operator; its fact is a *definition*, handled separately in the memory
client), or when it is predecessor-indexed (phi). -/
def factB : Cmd → Option BExp
  | .assign t x e => eqConstraint? t x e
  | .assume φ => some φ
  | _ => none

end Cmd

inductive Terminator : Type where
  | halt
  | goto (b : Nat)
  | ifGoto (c : Nat) (t e : Nat)
deriving Repr, DecidableEq

structure Block where
  cmds : List Cmd
  term : Terminator
deriving Repr

/-- A program. `exit` is metadata for future SESE/SASA work: the `Step`
relation never consults it — `halt` anywhere ends execution. It is
optional because the `ttac` parser only designates an exit block when
one is labeled `exit`. -/
structure Program where
  blocks : List Block
  entry : Nat
  exit : Option Nat
deriving Repr

def Program.block? (P : Program) (b : Nat) : Option Block :=
  P.blocks[b]?

end Ttac
