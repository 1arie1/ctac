import Ttac.Eval

/-!
# Variable inventories and congruence

The three variable collectors (one per register namespace) and the
congruence lemma: evaluation depends only on an expression's variables.
This is the vocabulary shared by every layer above `Eval` - the use
checker (`VcCheck`), the generic definitional-extension lemma
(`DefExt`), and the encoding-specific soundness proof (`VcSound`) - so
it sits in its own module below all of them.
-/

namespace Ttac

/-! ## Variable collectors -/

mutual
  def IExp.intVars : IExp → List Nat
    | .lit _ => []
    | .var x => [x]
    | .add a b | .sub a b | .mul a b | .div a b => a.intVars ++ b.intVars
    | .ite c t e => c.intVars ++ t.intVars ++ e.intVars

  def IExp.boolVars : IExp → List Nat
    | .lit _ | .var _ => []
    | .add a b | .sub a b | .mul a b | .div a b => a.boolVars ++ b.boolVars
    | .ite c t e => c.boolVars ++ t.boolVars ++ e.boolVars

  def BExp.intVars : BExp → List Nat
    | .lit _ | .var _ | .blk _ => []
    | .le a b | .lt a b | .eqI a b => a.intVars ++ b.intVars
    | .eqB a b | .and a b | .or a b | .imp a b => a.intVars ++ b.intVars
    | .not a => a.intVars
    | .ite c t e => c.intVars ++ t.intVars ++ e.intVars

  def BExp.boolVars : BExp → List Nat
    | .lit _ | .blk _ => []
    | .var c => [c]
    | .le a b | .lt a b | .eqI a b => a.boolVars ++ b.boolVars
    | .eqB a b | .and a b | .or a b | .imp a b => a.boolVars ++ b.boolVars
    | .not a => a.boolVars
    | .ite c t e => c.boolVars ++ t.boolVars ++ e.boolVars

  def IExp.blkVars : IExp → List Nat
    | .lit _ | .var _ => []
    | .add a b | .sub a b | .mul a b | .div a b => a.blkVars ++ b.blkVars
    | .ite c t e => c.blkVars ++ t.blkVars ++ e.blkVars

  def BExp.blkVars : BExp → List Nat
    | .lit _ | .var _ => []
    | .blk b => [b]
    | .le a b | .lt a b | .eqI a b => a.blkVars ++ b.blkVars
    | .eqB a b | .and a b | .or a b | .imp a b => a.blkVars ++ b.blkVars
    | .not a => a.blkVars
    | .ite c t e => c.blkVars ++ t.blkVars ++ e.blkVars
end

/-! ## Congruence -/

mutual
  theorem evalI_congr {s t : State} : (e : IExp) →
      (∀ x ∈ e.intVars, s.ints x = t.ints x) →
      (∀ c ∈ e.boolVars, s.bools c = t.bools c) →
      (∀ q ∈ e.blkVars, s.blks q = t.blks q) →
      evalI s e = evalI t e
    | .lit _, _, _, _ => rfl
    | .var x, hi, _, _ => hi x (by simp [IExp.intVars])
    | .add a b, hi, hb, hk => by
        simp only [evalI]
        rw [evalI_congr a (fun x hx => hi x (by simp [IExp.intVars, hx]))
              (fun c hc => hb c (by simp [IExp.boolVars, hc]))
              (fun q hq => hk q (by simp [IExp.blkVars, hq])),
            evalI_congr b (fun x hx => hi x (by simp [IExp.intVars, hx]))
              (fun c hc => hb c (by simp [IExp.boolVars, hc]))
              (fun q hq => hk q (by simp [IExp.blkVars, hq]))]
    | .sub a b, hi, hb, hk => by
        simp only [evalI]
        rw [evalI_congr a (fun x hx => hi x (by simp [IExp.intVars, hx]))
              (fun c hc => hb c (by simp [IExp.boolVars, hc]))
              (fun q hq => hk q (by simp [IExp.blkVars, hq])),
            evalI_congr b (fun x hx => hi x (by simp [IExp.intVars, hx]))
              (fun c hc => hb c (by simp [IExp.boolVars, hc]))
              (fun q hq => hk q (by simp [IExp.blkVars, hq]))]
    | .mul a b, hi, hb, hk => by
        simp only [evalI]
        rw [evalI_congr a (fun x hx => hi x (by simp [IExp.intVars, hx]))
              (fun c hc => hb c (by simp [IExp.boolVars, hc]))
              (fun q hq => hk q (by simp [IExp.blkVars, hq])),
            evalI_congr b (fun x hx => hi x (by simp [IExp.intVars, hx]))
              (fun c hc => hb c (by simp [IExp.boolVars, hc]))
              (fun q hq => hk q (by simp [IExp.blkVars, hq]))]
    | .div a b, hi, hb, hk => by
        simp only [evalI]
        rw [evalI_congr a (fun x hx => hi x (by simp [IExp.intVars, hx]))
              (fun c hc => hb c (by simp [IExp.boolVars, hc]))
              (fun q hq => hk q (by simp [IExp.blkVars, hq])),
            evalI_congr b (fun x hx => hi x (by simp [IExp.intVars, hx]))
              (fun c hc => hb c (by simp [IExp.boolVars, hc]))
              (fun q hq => hk q (by simp [IExp.blkVars, hq]))]
    | .ite c t' e', hi, hb, hk => by
        simp only [evalI]
        rw [evalB_congr c (fun x hx => hi x (by simp [IExp.intVars, hx]))
              (fun c hc => hb c (by simp [IExp.boolVars, hc]))
              (fun q hq => hk q (by simp [IExp.blkVars, hq])),
            evalI_congr t' (fun x hx => hi x (by simp [IExp.intVars, hx]))
              (fun c hc => hb c (by simp [IExp.boolVars, hc]))
              (fun q hq => hk q (by simp [IExp.blkVars, hq])),
            evalI_congr e' (fun x hx => hi x (by simp [IExp.intVars, hx]))
              (fun c hc => hb c (by simp [IExp.boolVars, hc]))
              (fun q hq => hk q (by simp [IExp.blkVars, hq]))]

  theorem evalB_congr {s t : State} : (e : BExp) →
      (∀ x ∈ e.intVars, s.ints x = t.ints x) →
      (∀ c ∈ e.boolVars, s.bools c = t.bools c) →
      (∀ q ∈ e.blkVars, s.blks q = t.blks q) →
      evalB s e = evalB t e
    | .lit _, _, _, _ => rfl
    | .var c, _, hb, _ => hb c (by simp [BExp.boolVars])
    | .blk b, _, _, hk => hk b (by simp [BExp.blkVars])
    | .le a b, hi, hb, hk => by
        simp only [evalB]
        rw [evalI_congr a (fun x hx => hi x (by simp [BExp.intVars, hx]))
              (fun c hc => hb c (by simp [BExp.boolVars, hc]))
              (fun q hq => hk q (by simp [BExp.blkVars, hq])),
            evalI_congr b (fun x hx => hi x (by simp [BExp.intVars, hx]))
              (fun c hc => hb c (by simp [BExp.boolVars, hc]))
              (fun q hq => hk q (by simp [BExp.blkVars, hq]))]
    | .lt a b, hi, hb, hk => by
        simp only [evalB]
        rw [evalI_congr a (fun x hx => hi x (by simp [BExp.intVars, hx]))
              (fun c hc => hb c (by simp [BExp.boolVars, hc]))
              (fun q hq => hk q (by simp [BExp.blkVars, hq])),
            evalI_congr b (fun x hx => hi x (by simp [BExp.intVars, hx]))
              (fun c hc => hb c (by simp [BExp.boolVars, hc]))
              (fun q hq => hk q (by simp [BExp.blkVars, hq]))]
    | .eqI a b, hi, hb, hk => by
        simp only [evalB]
        rw [evalI_congr a (fun x hx => hi x (by simp [BExp.intVars, hx]))
              (fun c hc => hb c (by simp [BExp.boolVars, hc]))
              (fun q hq => hk q (by simp [BExp.blkVars, hq])),
            evalI_congr b (fun x hx => hi x (by simp [BExp.intVars, hx]))
              (fun c hc => hb c (by simp [BExp.boolVars, hc]))
              (fun q hq => hk q (by simp [BExp.blkVars, hq]))]
    | .eqB a b, hi, hb, hk => by
        simp only [evalB]
        rw [evalB_congr a (fun x hx => hi x (by simp [BExp.intVars, hx]))
              (fun c hc => hb c (by simp [BExp.boolVars, hc]))
              (fun q hq => hk q (by simp [BExp.blkVars, hq])),
            evalB_congr b (fun x hx => hi x (by simp [BExp.intVars, hx]))
              (fun c hc => hb c (by simp [BExp.boolVars, hc]))
              (fun q hq => hk q (by simp [BExp.blkVars, hq]))]
    | .and a b, hi, hb, hk => by
        simp only [evalB]
        rw [evalB_congr a (fun x hx => hi x (by simp [BExp.intVars, hx]))
              (fun c hc => hb c (by simp [BExp.boolVars, hc]))
              (fun q hq => hk q (by simp [BExp.blkVars, hq])),
            evalB_congr b (fun x hx => hi x (by simp [BExp.intVars, hx]))
              (fun c hc => hb c (by simp [BExp.boolVars, hc]))
              (fun q hq => hk q (by simp [BExp.blkVars, hq]))]
    | .or a b, hi, hb, hk => by
        simp only [evalB]
        rw [evalB_congr a (fun x hx => hi x (by simp [BExp.intVars, hx]))
              (fun c hc => hb c (by simp [BExp.boolVars, hc]))
              (fun q hq => hk q (by simp [BExp.blkVars, hq])),
            evalB_congr b (fun x hx => hi x (by simp [BExp.intVars, hx]))
              (fun c hc => hb c (by simp [BExp.boolVars, hc]))
              (fun q hq => hk q (by simp [BExp.blkVars, hq]))]
    | .imp a b, hi, hb, hk => by
        simp only [evalB]
        rw [evalB_congr a (fun x hx => hi x (by simp [BExp.intVars, hx]))
              (fun c hc => hb c (by simp [BExp.boolVars, hc]))
              (fun q hq => hk q (by simp [BExp.blkVars, hq])),
            evalB_congr b (fun x hx => hi x (by simp [BExp.intVars, hx]))
              (fun c hc => hb c (by simp [BExp.boolVars, hc]))
              (fun q hq => hk q (by simp [BExp.blkVars, hq]))]
    | .not a, hi, hb, hk => by
        simp only [evalB]
        rw [evalB_congr a (fun x hx => hi x (by simp [BExp.intVars, hx]))
              (fun c hc => hb c (by simp [BExp.boolVars, hc]))
              (fun q hq => hk q (by simp [BExp.blkVars, hq]))]
    | .ite c t' e', hi, hb, hk => by
        simp only [evalB]
        rw [evalB_congr c (fun x hx => hi x (by simp [BExp.intVars, hx]))
              (fun c hc => hb c (by simp [BExp.boolVars, hc]))
              (fun q hq => hk q (by simp [BExp.blkVars, hq])),
            evalB_congr t' (fun x hx => hi x (by simp [BExp.intVars, hx]))
              (fun c hc => hb c (by simp [BExp.boolVars, hc]))
              (fun q hq => hk q (by simp [BExp.blkVars, hq])),
            evalB_congr e' (fun x hx => hi x (by simp [BExp.intVars, hx]))
              (fun c hc => hb c (by simp [BExp.boolVars, hc]))
              (fun q hq => hk q (by simp [BExp.blkVars, hq]))]
end

end Ttac
