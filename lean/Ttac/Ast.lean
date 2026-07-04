/-!
# Tiny TAC deep embedding: abstract syntax

Registers are `Nat`-numbered, with int and bool registers in *separate*
namespaces (`IExp.var 0` and `BExp.var 0` are different registers).
Together with the mutually inductive `IExp`/`BExp` split this makes
well-typedness hold by construction: there is no way to write an
ill-typed expression.

Blocks are referenced by `Nat` index into `Program.blocks`.

The v1 fragment is scalar-only: no bytemaps, no references. The `ttac`
surface language's purified-condition discipline (assert and branch
conditions are *named* bool registers, never expressions) is enforced
structurally: `Cmd.assert` and `Terminator.ifGoto` carry a register
number.
-/

namespace Ttac

mutual
  /-- Integer expressions. `div` is SMT-LIB Euclidean division. -/
  inductive IExp : Type where
    | lit (n : Int)
    | var (x : Nat)
    | add (a b : IExp)
    | sub (a b : IExp)
    | mul (a b : IExp)
    | div (a b : IExp)
    | ite (c : BExp) (t e : IExp)
  deriving Repr, DecidableEq

  /-- Boolean expressions. `imp` is SMT-LIB `(=> a b)`: it occurs only in
  transpiled VC formulas, never in programs (ttac has no implication). -/
  inductive BExp : Type where
    | lit (b : Bool)
    | var (c : Nat)
    | le (a b : IExp)
    | lt (a b : IExp)
    | eqI (a b : IExp)
    | eqB (a b : BExp)
    | not (a : BExp)
    | and (a b : BExp)
    | or (a b : BExp)
    | ite (c t e : BExp)
    | imp (a b : BExp)
  deriving Repr, DecidableEq
end

/-- Phi arms: `(predecessor block index, source register index)`. -/
abbrev PhiArms := List (Nat × Nat)

inductive Cmd : Type where
  | assignI (x : Nat) (e : IExp)
  | assignB (c : Nat) (e : BExp)
  | havocI (x : Nat)
  | havocB (c : Nat)
  | phiI (x : Nat) (arms : PhiArms)
  | phiB (c : Nat) (arms : PhiArms)
  | assume (b : BExp)
  | assert (c : Nat)
deriving Repr

inductive Terminator : Type where
  | halt
  | goto (b : Nat)
  | ifGoto (c : Nat) (t e : Nat)
deriving Repr

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
