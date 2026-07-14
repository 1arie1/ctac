import Ttac.VcDenot

/-!
# Postdominators to the assert block: the forcing certificate

The total-gamma encoding needs the *unreached* direction: at an
inactive join no gamma case may fire, which reduces per case to
"controller reached and oriented toward `s` ⇒ the join is reached".
That forcing is postdominance — but computed **to the assert block**,
not to program termination: a failing run's active chain provably
passes through the assert block, whereas nothing guarantees it
survives the assumes *after* it (`docs/vc`'s classical pdom-to-exit is
unsound here). Sites whose controllers sit past the assert block
simply cannot produce the certificate and keep the classical `phiRhs`
constraint.

The shape mirrors the dominator certificate exactly: `pdomTable` is
ordinary unverified code (a backward pass over reversed edges, sound
for any output), and the proof consumes only two closure facts
re-checked by `pdomClosedOK` — (P2) `pdom aB ⊆ [aB]`, (P1) for every
edge `u → v` with `u ≠ aB`, `pdom u ⊆ u :: pdom v`. Transport
(`pdom_visited`) walks the closure down the failing run's taken-edge
chain from a member `s ≤ aB` to the assert block.
-/

namespace Ttac

/-- Untrusted backward postdominator pass toward sink `aB` (succs have
larger index under W3, so reverse iteration sees them first). Blocks
that cannot reach `aB` — including everything past it — get ⊤; the
closure holds for any output, and junk entries are never consumed
(transport starts at an *active* `s ≤ aB`, which does reach `aB`). -/
def pdomTable (P : Program) (aB : Nat) : Array (List Nat) := Id.run do
  let n := P.blocks.length
  let mut pd : Array (List Nat) := Array.replicate n []
  for k in [0:n] do
    let b := n - 1 - k
    if b = aB then
      pd := pd.set! b [b]
    else
      match succsOf P b with
      | [] => pd := pd.set! b (List.range n)
      | s₀ :: rest =>
          let inter := rest.foldl
            (fun acc s => acc.filter (· ∈ pd.getD s []))
            (pd.getD s₀ [])
          pd := pd.set! b (b :: inter)
  return pd

def pdomOf (P : Program) (aB u : Nat) : List Nat :=
  (pdomTable P aB).getD u []

/-- The only postdominator facts the proof uses, re-checked. -/
def pdomClosedOK (P : Program) (aB : Nat) : Bool :=
  (pdomOf P aB aB).all (· = aB)
    && (Vc.allEdges P).all fun (u, v, _) =>
        u = aB
          || (pdomOf P aB u).all fun d =>
              d = u || (pdomOf P aB v).contains d

theorem pdomClosed_sink {P : Program} {aB : Nat}
    (hpc : pdomClosedOK P aB = true) :
    ∀ d ∈ pdomOf P aB aB, d = aB := by
  rw [pdomClosedOK, Bool.and_eq_true] at hpc
  intro d hd
  exact of_decide_eq_true (List.all_eq_true.mp hpc.1 d hd)

theorem pdomClosed_edge {P : Program} {aB : Nat}
    (hpc : pdomClosedOK P aB = true) {u v : Nat} {cond : BExp}
    (hedge : (u, v, cond) ∈ Vc.allEdges P) (hne : u ≠ aB) :
    ∀ d ∈ pdomOf P aB u, d = u ∨ d ∈ pdomOf P aB v := by
  rw [pdomClosedOK, Bool.and_eq_true] at hpc
  have h := List.all_eq_true.mp hpc.2 (u, v, cond) hedge
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · exact absurd (of_decide_eq_true h) hne
  · intro d hd
    have h' := List.all_eq_true.mp h d hd
    rw [Bool.or_eq_true] at h'
    rcases h' with h' | h'
    · exact Or.inl (of_decide_eq_true h')
    · exact Or.inr (List.contains_iff_mem.mp h')

/-! ## Chain lemmas -/

/-- The chain's unique continuation: a taken edge out of a non-final
chain member lands on the chain (`edgeTaken_unique` pins the successor
to the chain's own next element). -/
theorem chained_succ_mem {P : Program} {σ : State} :
    ∀ {V : List Nat}, Chained (EdgeTaken P σ) V → Chained (· < ·) V →
      ∀ {c z : Nat}, c ∈ V → z ∈ V → c < z →
        ∀ {s : Nat}, EdgeTaken P σ c s → s ∈ V := by
  intro V
  induction V with
  | nil => intro _ _ _ _ hc; cases hc
  | cons x rest ih =>
      intro hedge hlt c z hc hz hcz s hE
      rcases List.mem_cons.mp hc with rfl | hc'
      · have hzr : z ∈ rest := by
          rcases List.mem_cons.mp hz with rfl | hz'
          · omega
          · exact hz'
        cases rest with
        | nil => cases hzr
        | cons y rest' =>
            obtain ⟨hExy, -⟩ := chained_destruct hedge
            obtain rfl : s = y := edgeTaken_unique hE hExy
            exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
      · have hzr : z ∈ rest := by
          rcases List.mem_cons.mp hz with rfl | hz'
          · have := chained_lt_tail hlt rfl c hc'
            omega
          · exact hz'
        cases rest with
        | nil => cases hc'
        | cons y rest' =>
            obtain ⟨-, hEch⟩ := chained_destruct hedge
            obtain ⟨-, hLch⟩ := chained_destruct hlt
            exact List.mem_cons_of_mem _ (ih hEch hLch hc' hzr hcz hE)

/-- Transport: a postdominator (toward `aB`) of an active `s ≤ aB` is
active — walk the closure along the chain segment from `s` to `aB`. -/
theorem pdom_visited {P : Program} {σ : State} {aB : Nat}
    (hpc : pdomClosedOK P aB = true) :
    ∀ {V : List Nat}, Chained (EdgeTaken P σ) V → Chained (· < ·) V →
      ∀ {s : Nat}, s ∈ V → aB ∈ V → s ≤ aB →
        ∀ j ∈ pdomOf P aB s, j ∈ V := by
  intro V
  induction V with
  | nil => intro _ _ _ hs; cases hs
  | cons x rest ih =>
      intro hedge hlt s hs haB hsle j hj
      rcases List.mem_cons.mp hs with rfl | hs'
      · by_cases hsa : s = aB
        · subst hsa
          obtain rfl := pdomClosed_sink hpc j hj
          exact hs
        · have haBr : aB ∈ rest := by
            rcases List.mem_cons.mp haB with rfl | h
            · exact absurd rfl hsa
            · exact h
          cases rest with
          | nil => cases haBr
          | cons y rest' =>
              obtain ⟨hExy, hEch⟩ := chained_destruct hedge
              obtain ⟨-, hLch⟩ := chained_destruct hlt
              obtain ⟨cond, hedge'⟩ := hExy.mem_allEdges
              rcases pdomClosed_edge hpc hedge' hsa j hj with rfl | hjy
              · exact hs
              · have hyle : y ≤ aB :=
                  chained_lt_bound hLch rfl aB haBr
                exact List.mem_cons_of_mem _
                  (ih hEch hLch (List.mem_cons_self ..) haBr hyle j hjy)
      · have haBr : aB ∈ rest := by
          rcases List.mem_cons.mp haB with rfl | h
          · have := chained_lt_tail hlt rfl s hs'
            omega
          · exact h
        cases rest with
        | nil => cases hs'
        | cons y rest' =>
            obtain ⟨-, hEch⟩ := chained_destruct hedge
            obtain ⟨-, hLch⟩ := chained_destruct hlt
            exact List.mem_cons_of_mem _
              (ih hEch hLch hs' haBr hsle j hj)

/-- The denotational instance: over a failing run's active list. -/
theorem pdom_active {P : Program} {s0 : State} (hwf : WellFormed P)
    {aB : Nat} (hpc : pdomClosedOK P aB = true)
    {s : Nat} (hs : s ∈ activeList P s0) (haB : aB ∈ activeList P s0)
    (hsle : s ≤ aB) : ∀ j ∈ pdomOf P aB s, j ∈ activeList P s0 :=
  pdom_visited hpc (denot_hedge hwf)
    ((denot_hedge hwf).imp fun _ _ h => h.lt hwf.fwd) hs haB hsle

end Ttac
