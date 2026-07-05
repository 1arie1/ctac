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

Definitions and the write set `W` are sort-indexed: a definition's
target is a plain `(Ty × Nat)` pair, `W : Ty → Nat → Prop`. `DefHolds`
is a `Prop`-level equality of denotations, so map-sorted definitions
(function equalities) are covered natively; only `toConstraint?` - the
boolean-constraint rendering - is partial (no equality operator at
`.map`).

The extension is an explicit fold (`applyDefs`), not a bare
existential: the two halves - `applyDefs_defHolds` ("each definition
holds in the final state") and `agrees_applyDefs` ("everything outside
the targets is untouched") - are also useful separately. The headline
theorem `sat_extend` combines them.
-/

namespace Ttac

namespace DefExt

/-! ## Definitions and their application -/

/-- A single definition: target register (sort and index) and
right-hand side. -/
structure Def where
  t : Ty
  x : Nat
  rhs : Exp t

/-- The written register, as a plain pair - product equality is
decidable and cast-free. -/
def Def.target (d : Def) : Ty × Nat := (d.t, d.x)

/-- The definition as an equality constraint - the exact shape a VC
encoder emits for it. Partial: `none` at `.map`. -/
def Def.toConstraint? (d : Def) : Option BExp :=
  eqConstraint? d.t d.x d.rhs

def applyDef (s : State) (d : Def) : State :=
  s.upd d.t d.x (d.rhs.eval s)

def applyDefs : List Def → State → State
  | [], s => s
  | d :: ds, s => applyDefs ds (applyDef s d)

def targets (l : List Def) : List (Ty × Nat) := l.map Def.target

theorem mem_targets {tx : Ty × Nat} {l : List Def} :
    tx ∈ targets l ↔ ∃ d ∈ l, d.target = tx := by
  simp [targets, List.mem_map]

/-! ## Ordering

`OrderedDefs` is the acyclicity condition, phrased over the list order:
no definition reads its own target (`SelfOK`), and no later definition
writes an earlier definition's target or any variable its right-hand
side reads (`Untouched`, applied pairwise). Equivalently: every
right-hand-side variable is either outside the target set or the
target of a strictly earlier definition. -/

/-- `d`'s right-hand side does not read `d`'s own target. -/
def SelfOK (d : Def) : Prop :=
  d.target ∉ d.rhs.vars

/-- `d'` (a later definition) writes neither `d`'s target nor any
variable `d`'s right-hand side reads. -/
def Untouched (d d' : Def) : Prop :=
  d'.target ≠ d.target ∧ d'.target ∉ d.rhs.vars

def OrderedDefs (l : List Def) : Prop :=
  (∀ d ∈ l, SelfOK d) ∧ l.Pairwise Untouched

theorem OrderedDefs.tail {d : Def} {ds : List Def}
    (h : OrderedDefs (d :: ds)) : OrderedDefs ds :=
  ⟨fun d' hd' => h.1 d' (List.mem_cons_of_mem _ hd'), h.2.of_cons⟩

/-! ## What the fold leaves untouched -/

theorem applyDef_regs_ne {s : State} {d : Def} {u : Ty} {y : Nat}
    (h : (u, y) ≠ d.target) : (applyDef s d).regs u y = s.regs u y :=
  s.upd_regs_of_ne h _

theorem applyDef_blks (s : State) (d : Def) :
    (applyDef s d).blks = s.blks := rfl

theorem applyDefs_regs_notTarget : ∀ {l : List Def} {s : State}
    {u : Ty} {y : Nat}, (u, y) ∉ targets l →
    (applyDefs l s).regs u y = s.regs u y
  | [], _, _, _, _ => rfl
  | d :: ds, s, u, y, h => by
      have hd : (u, y) ≠ d.target := fun heq =>
        h (mem_targets.mpr ⟨d, List.mem_cons_self .., heq.symm⟩)
      have hds : (u, y) ∉ targets ds := fun hm => by
        obtain ⟨d', hd', ht⟩ := mem_targets.mp hm
        exact h (mem_targets.mpr ⟨d', List.mem_cons_of_mem _ hd', ht⟩)
      rw [applyDefs, applyDefs_regs_notTarget hds, applyDef_regs_ne hd]

theorem applyDefs_blks : ∀ (l : List Def) (s : State),
    (applyDefs l s).blks = s.blks
  | [], _ => rfl
  | d :: ds, s => by rw [applyDefs, applyDefs_blks, applyDef_blks]

/-! ## Every definition holds in the final state -/

def DefHolds (s : State) (d : Def) : Prop :=
  s.regs d.t d.x = d.rhs.eval s

/-- The heart of definitional extension: under `OrderedDefs`, the
written value survives to the end of the fold (nothing later writes the
target) and the right-hand side's variables survive as well (nothing
later - or the definition itself - writes them), so the equation holds
in the *final* state. One sort-generic proof; no per-namespace cases. -/
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
      · have hxnot : d.target ∉ targets ds := fun hx => by
          obtain ⟨d', hd', htgt⟩ := mem_targets.mp hx
          exact (huntouched d' hd').1 htgt
        show (applyDefs ds (applyDef s d)).regs d.t d.x
          = d.rhs.eval (applyDefs ds (applyDef s d))
        rw [show d.target = (d.t, d.x) from rfl] at hxnot
        rw [applyDefs_regs_notTarget hxnot]
        have hwrite : (applyDef s d).regs d.t d.x = d.rhs.eval s :=
          State.upd_regs_self ..
        rw [hwrite]
        refine (eval_congr d.rhs ?_ ?_).symm
        · intro p hp
          have hpnot : p ∉ targets ds := fun hpt => by
            obtain ⟨d', hd', htgt⟩ := mem_targets.mp hpt
            exact (huntouched d' hd').2 (htgt ▸ hp)
          rw [applyDefs_regs_notTarget (by exact hpnot)]
          exact applyDef_regs_ne (fun heq => hself d (List.mem_cons_self ..)
            (heq ▸ hp))
        · intro q _
          rw [applyDefs_blks, applyDef_blks]
      · exact applyDefs_defHolds hord' (applyDef s d0) d hdtail

theorem DefHolds.toConstraint_eval {s : State} {d : Def}
    (h : DefHolds s d) {c : BExp} (hc : d.toConstraint? = some c) :
    c.eval s = true := by
  obtain ⟨t, x, rhs⟩ := d
  simp only [DefHolds] at h
  cases t with
  | int =>
      obtain rfl := Option.some.inj hc
      simp [Exp.eval, BinOp.denote, h]
  | bool =>
      obtain rfl := Option.some.inj hc
      simp [Exp.eval, BinOp.denote, h]
  | map => cases hc

/-! ## Robustness -/

/-- `w'` agrees with `w` outside the register set `W` and has the same
guard component. -/
def Agrees (W : Ty → Nat → Prop) (w w' : State) : Prop :=
  (∀ t x, ¬W t x → w'.regs t x = w.regs t x) ∧ w'.blks = w.blks

/-- A constraint is *robust* at `w` with respect to `W`: it holds in
every state agreeing with `w` outside it. This is deliberately weaker
than "no `W`-variable occurs in the constraint" - a `W`-variable may
occur as long as it cannot affect the truth value (behind a false
guard, inside a disjunct that is not the witnessing one, ...). -/
def Robust (W : Ty → Nat → Prop) (w : State) (c : BExp) : Prop :=
  ∀ w', Agrees W w w' → c.eval w' = true

/-- The syntactic sufficient condition: a true constraint none of whose
variables lies in `W` is robust. Constraints that need the semantic
form are exactly those this bridge cannot handle. -/
theorem robust_of_avoids {W : Ty → Nat → Prop} {w : State} {c : BExp}
    (h : c.eval w = true) (hv : ∀ p ∈ c.vars, ¬W p.1 p.2) :
    Robust W w c := by
  intro w' ⟨hreg, hblk⟩
  rw [eval_congr c (fun p hp => hreg p.1 p.2 (hv p hp))
    (fun q _ => congrFun hblk q)]
  exact h

theorem agrees_applyDefs (l : List Def) (w : State) :
    Agrees (fun t x => (t, x) ∈ targets l) w (applyDefs l w) :=
  ⟨fun _ _ hx => applyDefs_regs_notTarget hx, applyDefs_blks l w⟩

/-! ## The headline theorem -/

/-- **Definitional extension.** If every constraint of ψ is either
robust at `w` (with respect to the definitions' targets) or *is* one of
the definitions, then the extension `applyDefs defs w` satisfies all of
ψ: robust constraints survive because the fold only writes targets,
and definition constraints hold by `applyDefs_defHolds`. -/
theorem sat_extend {ψ : List BExp} {defs : List Def} {w : State}
    (hord : OrderedDefs defs)
    (hc : ∀ c ∈ ψ,
      Robust (fun t x => (t, x) ∈ targets defs) w c
        ∨ ∃ d ∈ defs, d.toConstraint? = some c) :
    ∀ c ∈ ψ, c.eval (applyDefs defs w) = true := by
  intro c hcmem
  rcases hc c hcmem with hrob | ⟨d, hd, hdc⟩
  · exact hrob _ (agrees_applyDefs defs w)
  · exact (applyDefs_defHolds hord w d hd).toConstraint_eval hdc

end DefExt

end Ttac
