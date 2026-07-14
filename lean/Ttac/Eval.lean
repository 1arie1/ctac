import Ttac.State

/-!
# Tiny TAC deep embedding: expression evaluation

Expressions are pure and total, so evaluation is a plain structural
recursion, not a relation. Each operator's meaning is a row in its
family's denotation table; `Exp.eval` itself never mentions an
individual operator.

Division is `Int.ediv`, written explicitly: SMT-LIB `div` is Euclidean
(remainder in `[0, |b|)`), and the reference interpreter
(`src/ctac/ttac/run.py`) is Euclidean with `x / 0 = 0`. `Int.ediv`
matches both, including the div-by-zero convention (SMT-LIB leaves
`x div 0` uninterpreted-but-total; fixing it to 0 refines that and
agrees with z3's default model). The trap to avoid is `Int.tdiv`
(truncation: `(-7).tdiv 2 = -3`, whereas `(-7).ediv 2 = -4`).

A `.map` value is a total function `Int → Int`: `select` is
application, `store` is pointwise update — matching the encoder's
bytemap-as-UF reading (a havoc'd map is an unconstrained function).
-/

namespace Ttac

def UnOp.denote : {a c : Ty} → UnOp a c → a.denote → c.denote
  | _, _, .not => fun x => !x

def BinOp.denote : {a b c : Ty} → BinOp a b c → a.denote → b.denote → c.denote
  | _, _, _, .add => fun x y => x + y
  | _, _, _, .sub => fun x y => x - y
  | _, _, _, .mul => fun x y => x * y
  | _, _, _, .div => Int.ediv
  | _, _, _, .le => fun x y => decide (x ≤ y)
  | _, _, _, .lt => fun x y => decide (x < y)
  | _, _, _, .eqI => fun x y => decide (x = y)
  | _, _, _, .eqB => fun x y => x == y
  | _, _, _, .and => fun x y => x && y
  | _, _, _, .or => fun x y => x || y
  | _, _, _, .imp => fun x y => !x || y
  | _, _, _, .select => fun m i => m i

def TernOp.denote : {a b c d : Ty} → TernOp a b c d →
    a.denote → b.denote → c.denote → d.denote
  | _, _, _, _, .store => fun m i v => fun p => if p = i then v else m p

def Exp.eval (s : State) : {t : Ty} → Exp t → t.denote
  | _, .litI n => n
  | _, .litB b => b
  | _, .var t x => s.regs t x
  | _, .blk b => s.blks b
  | _, .un op e => op.denote (e.eval s)
  | _, .bin op l r => op.denote (l.eval s) (r.eval s)
  | _, .tern op e₁ e₂ e₃ => op.denote (e₁.eval s) (e₂.eval s) (e₃.eval s)
  | _, .ite c th el => if c.eval s then th.eval s else el.eval s

-- Division semantics pins (mirror run.py's `_ediv` test vectors).
example : Int.ediv (-7) 2 = -4 := by decide
example : Int.ediv 7 (-2) = -3 := by decide
example : Int.ediv 7 2 = 3 := by decide
example : Int.ediv (-7) (-2) = 4 := by decide
example : Int.ediv 5 0 = 0 := by decide

end Ttac
