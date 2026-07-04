import Ttac.Ast
import Ttac.State

/-!
# Tiny TAC deep embedding: expression evaluation

Expressions are pure and total, so evaluation is a plain structural
recursion, not a relation.

Division is `Int.ediv`, written explicitly: SMT-LIB `div` is Euclidean
(remainder in `[0, |b|)`), and the reference interpreter
(`src/ctac/ttac/run.py`) is Euclidean with `x / 0 = 0`. `Int.ediv`
matches both, including the div-by-zero convention (SMT-LIB leaves
`x div 0` uninterpreted-but-total; fixing it to 0 refines that and
agrees with z3's default model). The trap to avoid is `Int.tdiv`
(truncation: `(-7).tdiv 2 = -3`, whereas `(-7).ediv 2 = -4`).
-/

namespace Ttac

mutual
  def evalI (s : State) : IExp → Int
    | .lit n => n
    | .var x => s.ints x
    | .add a b => evalI s a + evalI s b
    | .sub a b => evalI s a - evalI s b
    | .mul a b => evalI s a * evalI s b
    | .div a b => Int.ediv (evalI s a) (evalI s b)
    | .ite c t e => if evalB s c then evalI s t else evalI s e

  def evalB (s : State) : BExp → Bool
    | .lit b => b
    | .var c => s.bools c
    | .le a b => decide (evalI s a ≤ evalI s b)
    | .lt a b => decide (evalI s a < evalI s b)
    | .eqI a b => decide (evalI s a = evalI s b)
    | .eqB a b => evalB s a == evalB s b
    | .not a => !(evalB s a)
    | .and a b => evalB s a && evalB s b
    | .or a b => evalB s a || evalB s b
    | .ite c t e => if evalB s c then evalB s t else evalB s e
end

-- Division semantics pins (mirror run.py's `_ediv` test vectors).
example : Int.ediv (-7) 2 = -4 := by decide
example : Int.ediv 7 (-2) = -3 := by decide
example : Int.ediv 7 2 = 3 := by decide
example : Int.ediv (-7) (-2) = 4 := by decide
example : Int.ediv 5 0 = 0 := by decide

end Ttac
