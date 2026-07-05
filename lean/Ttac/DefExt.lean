import Ttac.Vars

/-!
# Definitional extension

The generic lemma behind the VC witness construction, independent of
any particular encoding:

> If a state `w` satisfies a constraint set ψ *robustly* - each
> constraint stays true under arbitrary changes to a set `W` of
> registers - and `EQ` is a list of definitions with pairwise-distinct
> left-hand sides in `W` whose right-hand sides read only variables
> outside `W` or defined *earlier* in the list, then folding the
> definitions over `w` yields a state satisfying ψ ∧ EQ.

Robustness is deliberately *semantic* ("true in every state agreeing
with `w` outside `W`"), not syntactic non-occurrence of `W`-variables.
The syntactic form is false for the VC use case: an unvisited phi
target occurs in ψ inside the guard-false facts of its own block and
inside dead disjuncts of visited CFG constraints. The syntactic
condition survives as the sufficient-condition bridge
`robust_of_avoids`.

The extension is an explicit fold (`applyDefs`), not a bare
existential: the two halves - `applyDefs_defHolds` ("each definition
holds in the final state") and `agrees_applyDefs` ("everything outside
the targets is untouched") - are also useful separately. The headline
theorem `sat_extend` combines them.
-/

namespace Ttac

namespace DefExt

/-! ## Definitions and their application -/

/-- A single definition: target register and right-hand side, in one of
the two namespaces. -/
inductive Def where
  | defI (x : Nat) (rhs : IExp)
  | defB (x : Nat) (rhs : BExp)

namespace Def

def intTarget? : Def → Option Nat
  | .defI x _ => some x
  | .defB _ _ => none

def boolTarget? : Def → Option Nat
  | .defI _ _ => none
  | .defB x _ => some x

def rhsIntVars : Def → List Nat
  | .defI _ r => r.intVars
  | .defB _ r => r.intVars

def rhsBoolVars : Def → List Nat
  | .defI _ r => r.boolVars
  | .defB _ r => r.boolVars

/-- The definition as an equality constraint - the exact shape a VC
encoder emits for it. -/
def toConstraint : Def → BExp
  | .defI x r => .eqI (.var x) r
  | .defB x r => .eqB (.var x) r

end Def

def applyDef (s : State) : Def → State
  | .defI x r => s.updI x (evalI s r)
  | .defB x r => s.updB x (evalB s r)

def applyDefs : List Def → State → State
  | [], s => s
  | d :: ds, s => applyDefs ds (applyDef s d)

def intTargets (l : List Def) : List Nat := l.filterMap Def.intTarget?

def boolTargets (l : List Def) : List Nat := l.filterMap Def.boolTarget?

theorem mem_intTargets {x : Nat} {l : List Def} :
    x ∈ intTargets l ↔ ∃ d, d ∈ l ∧ d.intTarget? = some x := by
  simp [intTargets, List.mem_filterMap]

theorem mem_boolTargets {x : Nat} {l : List Def} :
    x ∈ boolTargets l ↔ ∃ d, d ∈ l ∧ d.boolTarget? = some x := by
  simp [boolTargets, List.mem_filterMap]

/-! ## Ordering

`OrderedDefs` is the acyclicity condition, phrased over the list order:
no definition reads its own target (`SelfOK`), and no later definition
writes an earlier definition's target or any variable its right-hand
side reads (`Untouched`, applied pairwise). Equivalently: every
right-hand-side variable is either outside the target set or the
target of a strictly earlier definition. -/

/-- `d`'s right-hand side does not read `d`'s own target. -/
def SelfOK (d : Def) : Prop :=
  (∀ x, d.intTarget? = some x → x ∉ d.rhsIntVars)
    ∧ (∀ x, d.boolTarget? = some x → x ∉ d.rhsBoolVars)

/-- `d'` (a later definition) writes neither `d`'s target nor any
variable `d`'s right-hand side reads. -/
def Untouched (d d' : Def) : Prop :=
  (∀ x, d'.intTarget? = some x → d.intTarget? ≠ some x ∧ x ∉ d.rhsIntVars)
    ∧ (∀ x, d'.boolTarget? = some x → d.boolTarget? ≠ some x ∧ x ∉ d.rhsBoolVars)

def OrderedDefs (l : List Def) : Prop :=
  (∀ d ∈ l, SelfOK d) ∧ l.Pairwise Untouched

theorem OrderedDefs.tail {d : Def} {ds : List Def}
    (h : OrderedDefs (d :: ds)) : OrderedDefs ds :=
  ⟨fun d' hd' => h.1 d' (List.mem_cons_of_mem _ hd'), h.2.of_cons⟩

/-! ## What the fold leaves untouched -/

theorem applyDef_ints_ne {s : State} {d : Def} {x : Nat}
    (h : d.intTarget? ≠ some x) : (applyDef s d).ints x = s.ints x := by
  cases d with
  | defI y r =>
      simp only [Def.intTarget?, ne_eq, Option.some.injEq] at h
      exact State.updI_ints_of_ne s (fun hxy => h hxy.symm) _
  | defB y r => rfl

theorem applyDef_bools_ne {s : State} {d : Def} {x : Nat}
    (h : d.boolTarget? ≠ some x) : (applyDef s d).bools x = s.bools x := by
  cases d with
  | defI y r => rfl
  | defB y r =>
      simp only [Def.boolTarget?, ne_eq, Option.some.injEq] at h
      exact State.updB_bools_of_ne s (fun hxy => h hxy.symm) _

theorem applyDef_blks (s : State) (d : Def) :
    (applyDef s d).blks = s.blks := by
  cases d <;> rfl

theorem applyDefs_ints_notTarget : ∀ {l : List Def} {s : State} {x : Nat},
    x ∉ intTargets l → (applyDefs l s).ints x = s.ints x
  | [], _, _, _ => rfl
  | d :: ds, s, x, h => by
      have hd : d.intTarget? ≠ some x := fun heq =>
        h (mem_intTargets.mpr ⟨d, List.mem_cons_self .., heq⟩)
      have hds : x ∉ intTargets ds := fun hm => by
        obtain ⟨d', hd', ht⟩ := mem_intTargets.mp hm
        exact h (mem_intTargets.mpr ⟨d', List.mem_cons_of_mem _ hd', ht⟩)
      rw [applyDefs, applyDefs_ints_notTarget hds, applyDef_ints_ne hd]

theorem applyDefs_bools_notTarget : ∀ {l : List Def} {s : State} {x : Nat},
    x ∉ boolTargets l → (applyDefs l s).bools x = s.bools x
  | [], _, _, _ => rfl
  | d :: ds, s, x, h => by
      have hd : d.boolTarget? ≠ some x := fun heq =>
        h (mem_boolTargets.mpr ⟨d, List.mem_cons_self .., heq⟩)
      have hds : x ∉ boolTargets ds := fun hm => by
        obtain ⟨d', hd', ht⟩ := mem_boolTargets.mp hm
        exact h (mem_boolTargets.mpr ⟨d', List.mem_cons_of_mem _ hd', ht⟩)
      rw [applyDefs, applyDefs_bools_notTarget hds, applyDef_bools_ne hd]

theorem applyDefs_blks : ∀ (l : List Def) (s : State),
    (applyDefs l s).blks = s.blks
  | [], _ => rfl
  | d :: ds, s => by rw [applyDefs, applyDefs_blks, applyDef_blks]

/-! ## Every definition holds in the final state -/

def DefHolds (s : State) : Def → Prop
  | .defI x r => s.ints x = evalI s r
  | .defB x r => s.bools x = evalB s r

/-- The heart of definitional extension: under `OrderedDefs`, the
written value survives to the end of the fold (nothing later writes the
target) and the right-hand side's variables survive as well (nothing
later - or the definition itself - writes them), so the equation holds
in the *final* state. -/
theorem applyDefs_defHolds : ∀ {l : List Def}, OrderedDefs l →
    ∀ (s : State), ∀ d ∈ l, DefHolds (applyDefs l s) d
  | [], _, _, _, hd => (List.not_mem_nil hd).elim
  | d0 :: ds, hord, s, d, hd => by
      obtain ⟨hself, hpair⟩ := hord
      rw [List.pairwise_cons] at hpair
      obtain ⟨huntouched, hpair'⟩ := hpair
      have hord' : OrderedDefs ds :=
        ⟨fun d' hd' => hself d' (List.mem_cons_of_mem _ hd'), hpair'⟩
      rcases List.mem_cons.mp hd with rfl | hdtail
      · cases d with
        | defI x r =>
            have hxnot : x ∉ intTargets ds := fun hx => by
              obtain ⟨d', hd', htgt⟩ := mem_intTargets.mp hx
              exact ((huntouched d' hd').1 x htgt).1 rfl
            show (applyDefs ds (applyDef s (.defI x r))).ints x
              = evalI (applyDefs ds (applyDef s (.defI x r))) r
            rw [applyDefs_ints_notTarget hxnot]
            have hwrite : (applyDef s (.defI x r)).ints x = evalI s r := by
              simp [applyDef]
            rw [hwrite]
            refine (evalI_congr r ?_ ?_ ?_).symm
            · intro v hv
              have hvnot : v ∉ intTargets ds := fun hvt => by
                obtain ⟨d', hd', htgt⟩ := mem_intTargets.mp hvt
                exact ((huntouched d' hd').1 v htgt).2 hv
              rw [applyDefs_ints_notTarget hvnot]
              have hvx : v ≠ x := fun h =>
                (hself _ (List.mem_cons_self ..)).1 x rfl (h ▸ hv)
              exact State.updI_ints_of_ne s hvx _
            · intro v hv
              have hvnot : v ∉ boolTargets ds := fun hvt => by
                obtain ⟨d', hd', htgt⟩ := mem_boolTargets.mp hvt
                exact ((huntouched d' hd').2 v htgt).2 hv
              rw [applyDefs_bools_notTarget hvnot]
              rfl
            · intro q _
              rw [applyDefs_blks, applyDef_blks]
        | defB x r =>
            have hxnot : x ∉ boolTargets ds := fun hx => by
              obtain ⟨d', hd', htgt⟩ := mem_boolTargets.mp hx
              exact ((huntouched d' hd').2 x htgt).1 rfl
            show (applyDefs ds (applyDef s (.defB x r))).bools x
              = evalB (applyDefs ds (applyDef s (.defB x r))) r
            rw [applyDefs_bools_notTarget hxnot]
            have hwrite : (applyDef s (.defB x r)).bools x = evalB s r := by
              simp [applyDef]
            rw [hwrite]
            refine (evalB_congr r ?_ ?_ ?_).symm
            · intro v hv
              have hvnot : v ∉ intTargets ds := fun hvt => by
                obtain ⟨d', hd', htgt⟩ := mem_intTargets.mp hvt
                exact ((huntouched d' hd').1 v htgt).2 hv
              rw [applyDefs_ints_notTarget hvnot]
              rfl
            · intro v hv
              have hvnot : v ∉ boolTargets ds := fun hvt => by
                obtain ⟨d', hd', htgt⟩ := mem_boolTargets.mp hvt
                exact ((huntouched d' hd').2 v htgt).2 hv
              rw [applyDefs_bools_notTarget hvnot]
              have hvx : v ≠ x := fun h =>
                (hself _ (List.mem_cons_self ..)).2 x rfl (h ▸ hv)
              exact State.updB_bools_of_ne s hvx _
            · intro q _
              rw [applyDefs_blks, applyDef_blks]
      · exact applyDefs_defHolds hord' (applyDef s d0) d hdtail

theorem DefHolds.toConstraint_eval {s : State} {d : Def}
    (h : DefHolds s d) : evalB s d.toConstraint = true := by
  cases d with
  | defI x r =>
      simp only [DefHolds] at h
      simp [Def.toConstraint, evalB, evalI, h]
  | defB x r =>
      simp only [DefHolds] at h
      simp [Def.toConstraint, evalB, h]

/-! ## Robustness -/

/-- `w'` agrees with `w` outside the register sets `WI`/`WB` and has
the same guard component. -/
def Agrees (WI WB : Nat → Prop) (w w' : State) : Prop :=
  (∀ x, ¬WI x → w'.ints x = w.ints x)
    ∧ (∀ x, ¬WB x → w'.bools x = w.bools x)
    ∧ w'.blks = w.blks

/-- A constraint is *robust* at `w` with respect to `WI`/`WB`: it holds
in every state agreeing with `w` outside them. This is deliberately
weaker than "no `W`-variable occurs in the constraint" - a `W`-variable
may occur as long as it cannot affect the truth value (behind a false
guard, inside a disjunct that is not the witnessing one, ...). -/
def Robust (WI WB : Nat → Prop) (w : State) (c : BExp) : Prop :=
  ∀ w', Agrees WI WB w w' → evalB w' c = true

/-- The syntactic sufficient condition: a true constraint none of whose
variables lies in `W` is robust. Constraints that need the semantic
form are exactly those this bridge cannot handle. -/
theorem robust_of_avoids {WI WB : Nat → Prop} {w : State} {c : BExp}
    (h : evalB w c = true)
    (hI : ∀ r ∈ c.intVars, ¬WI r) (hB : ∀ r ∈ c.boolVars, ¬WB r) :
    Robust WI WB w c := by
  intro w' ⟨aI, aB, ablk⟩
  rw [evalB_congr c (fun r hr => aI r (hI r hr)) (fun r hr => aB r (hB r hr))
    (fun q _ => congrFun ablk q)]
  exact h

theorem agrees_applyDefs (l : List Def) (w : State) :
    Agrees (· ∈ intTargets l) (· ∈ boolTargets l) w (applyDefs l w) :=
  ⟨fun _ hx => applyDefs_ints_notTarget hx,
   fun _ hx => applyDefs_bools_notTarget hx,
   applyDefs_blks l w⟩

/-! ## The headline theorem -/

/-- **Definitional extension.** If every constraint of ψ is either
robust at `w` (with respect to the definitions' targets) or *is* one of
the definitions, then the extension `applyDefs defs w` satisfies all of
ψ: robust constraints survive because the fold only writes targets,
and definition constraints hold by `applyDefs_defHolds`. -/
theorem sat_extend {ψ : List BExp} {defs : List Def} {w : State}
    (hord : OrderedDefs defs)
    (hc : ∀ c ∈ ψ,
      Robust (· ∈ intTargets defs) (· ∈ boolTargets defs) w c
        ∨ ∃ d ∈ defs, c = d.toConstraint) :
    ∀ c ∈ ψ, evalB (applyDefs defs w) c = true := by
  intro c hcmem
  rcases hc c hcmem with hrob | ⟨d, hd, rfl⟩
  · exact hrob _ (agrees_applyDefs defs w)
  · exact (applyDefs_defHolds hord w d hd).toConstraint_eval

end DefExt

end Ttac
