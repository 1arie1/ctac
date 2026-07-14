import Ttac.VcCoadequacy

/-!
# The idealized rw-eq product (lockstep fragment)

`product A B` merges an original program `A` and its rewrite `B` into
one program whose asserts are exactly the equivalence checks (CHKs)
that `ctac rw-eq` materializes. The metatheorem (`product_transfer`)
is the safety transfer the rw-eq certificate licenses:

    Safe_denot (product A B) → Safe_denot B → Safe_denot A

with the operational form `product_transfer_safe` on top via the
denotational-operational equivalence.

This is the *idealized* product, not the walker's output: the walker
(`src/ctac/rw_eq/transform.py`) shares a single register namespace and
emits per-assignment CHKs; here the two copies live in disjoint
namespaces (`pv j i = 3*i + j`, copy 0 = A, copy 1 = B, 2 = CHK
registers), so assignments need no CHKs at all — only the observables
are checked. Walker conformance is a separate, later question (the
bridge is a merge + copy-propagation chain starting from the paired
havocs' equate, see below).

Design decisions forced by `denot`'s position-blind `assumesOK` (every
assume in a block guards the whole block, regardless of position):

* **A's assumes are the only assumes.** Product reachability is
  exactly A's. B's assumes are *asserted*, never assumed (rule-4
  form: a retained B-assume must be valid at A-reachable states) — an
  emitted `assume condB` would guard the block and make the very CHK
  that checks it vacuous on the states that matter.
* **A's assert is dropped from the A-copy.** Only the pairing CHK
  `Eq(predA, predB)` remains; emitting `assume predA` (the walker's
  rule-5b tail) would make the assert block infeasible precisely on
  A's failing seeds.
* **Paired havocs are equated, not duplicated.** The A-copy keeps
  `havoc x₀`; the B-copy's havoc of the same register becomes the
  assignment `x₁ := x₀`. Without the equate, seeds disagreeing across
  the halves falsify every retained B-assume about a havoc'd value —
  `Safe_denot (product A B)` would fail for sound rewrites. The
  equate is the simulation's input correspondence (and the seed of
  the copy-propagation chain back to the walker's shared namespace).

No map restriction is needed: renaming is sort-uniform, CHKs compare
only bool registers and B-assume conditions, and the havoc equate is
an assignment (never a map equality).

The hypothesis asymmetry mirrors adequacy vs. coadequacy: the A-half
projection is pointwise (product guards *are* A's guards), so A needs
only `WellFormed`; the B-half must relate product values to B's own
run across regions A's trace never reaches, so B additionally needs
`domClosedOK` (junk isolation; the table is shared with A under
lockstep) and `phiCoversOK` (arm selection).

Proof shape: seed the product with both programs' *final* fold states
side by side (`prodSeed`) — coadequacy's self-write trick, doubled.
The A-copy fold is then the identity (`prodCmdA_fold`); the B-copy's
writes are self-writes at A-active blocks and junk confined to
non-`GoodB` registers elsewhere (`prodCmdB_step`); the fold induction
(`transfer_inv`) extracts each A-active block's CHK content from
product safety and threads guard transfer along A's active prefix.
-/

namespace Ttac

open Vc

/-! ## Renaming -/

/-- Copy-indexed register renaming: copy `j`'s register `i` is
`3*i + j`. Copies 0 (original) and 1 (rewrite) never collide, and
`j = 2` is reserved for walker-minted CHK registers. -/
def pv (j i : Nat) : Nat := 3 * i + j

def Exp.rename (ρ : Nat → Nat) : {t : Ty} → Exp t → Exp t
  | _, .litI n => .litI n
  | _, .litB b => .litB b
  | _, .var t x => .var t (ρ x)
  | _, .blk b => .blk b
  | _, .un op e => .un op (e.rename ρ)
  | _, .bin op l r => .bin op (l.rename ρ) (r.rename ρ)
  | _, .tern op e₁ e₂ e₃ =>
      .tern op (e₁.rename ρ) (e₂.rename ρ) (e₃.rename ρ)
  | _, .ite c th el => .ite (c.rename ρ) (th.rename ρ) (el.rename ρ)

/-- Pull a renaming into the state: reading renamed registers is
reading through the reindexed register file. Guards are untouched
(renaming never rewrites `.blk`). -/
def State.reindex (s : State) (ρ : Nat → Nat) : State where
  regs := fun t x => s.regs t (ρ x)
  blks := s.blks

/-- The renaming lemma — the entire "keeping variable names straight"
machinery. Everything downstream reasons about `σ.reindex (pv j)`
instead of chasing indices. -/
theorem Exp.eval_rename (ρ : Nat → Nat) (s : State) :
    {t : Ty} → (e : Exp t) → (e.rename ρ).eval s = e.eval (s.reindex ρ)
  | _, .litI _ => rfl
  | _, .litB _ => rfl
  | _, .var _ _ => rfl
  | _, .blk _ => rfl
  | _, .un op e => by
      show op.denote ((e.rename ρ).eval s) = _
      rw [eval_rename ρ s e]; rfl
  | _, .bin op l r => by
      show op.denote ((l.rename ρ).eval s) ((r.rename ρ).eval s) = _
      rw [eval_rename ρ s l, eval_rename ρ s r]; rfl
  | _, .tern op e₁ e₂ e₃ => by
      show op.denote ((e₁.rename ρ).eval s) ((e₂.rename ρ).eval s)
        ((e₃.rename ρ).eval s) = _
      rw [eval_rename ρ s e₁, eval_rename ρ s e₂, eval_rename ρ s e₃]; rfl
  | _, .ite c th el => by
      show (if (c.rename ρ).eval s then (th.rename ρ).eval s
        else (el.rename ρ).eval s) = _
      rw [eval_rename ρ s c, eval_rename ρ s th, eval_rename ρ s el]; rfl

def Cmd.rename (ρ : Nat → Nat) : Cmd → Cmd
  | .assign t x e => .assign t (ρ x) (e.rename ρ)
  | .havoc t x => .havoc t (ρ x)
  | .phi t x arms => .phi t (ρ x) (arms.map fun a => (a.1, ρ a.2))
  | .assume φ => .assume (φ.rename ρ)
  | .assert c => .assert (ρ c)

def Terminator.rename (ρ : Nat → Nat) : Terminator → Terminator
  | .halt => .halt
  | .goto t => .goto t
  | .ifGoto c t e => .ifGoto (ρ c) t e

/-! ## The product construction -/

/-- CHK registers for block `k` occupy the window
`[stride*k, stride*(k+1))` of the `j = 2` namespace: one slot per
B-side command index plus one terminator slot, so `stride` is B's
maximal block width plus one. -/
def chkStride (Bs : List Block) : Nat :=
  (Bs.map (·.cmds.length)).foldl max 0 + 1

def chkReg (stride k i : Nat) : Nat := pv 2 (stride * k + i)

/-- Does `P` havoc register `(t, x)` anywhere? Decides whether a
B-side havoc pairs with an A-side one (→ equate) or is B-only
(→ kept unconstrained, which only over-approximates B). -/
def hasHavoc (P : Program) (t : Ty) (x : Nat) : Bool :=
  P.blocks.any fun B => B.cmds.any fun c =>
    match c with
    | .havoc t' x' => decide (t' = t) && decide (x' = x)
    | _ => false

/-- The unique assert register of a block, if any. -/
def Block.assertReg? (B : Block) : Option Nat :=
  B.cmds.findSome? fun c =>
    match c with | .assert r => some r | _ => none

/-- A-copy emission: everything renamed into copy 0, except the assert,
which is dropped — its content lives entirely in the pairing CHK. -/
def prodCmdA : Cmd → List Cmd
  | .assert _ => []
  | c => [c.rename (pv 0)]

/-- B-copy emission for the command at index `i` of block `k`:
assumes and asserts become CHKs, a paired havoc becomes the input
equate, everything else is renamed into copy 1. `Ba` is A's block
(source of the assert pairing and, via `A`, the havoc pairing). -/
def prodCmdB (A : Program) (Ba : Block) (stride k i : Nat) : Cmd → List Cmd
  | .assume φ =>
      let r := chkReg stride k i
      [.assign .bool r (φ.rename (pv 1)), .assert r]
  | .assert c' =>
      let r := chkReg stride k i
      let chk : BExp := match Ba.assertReg? with
        | some cA => .eqB (.var .bool (pv 0 cA)) (.var .bool (pv 1 c'))
        | none => .var .bool (pv 1 c')
      [.assign .bool r chk, .assert r]
  | .havoc t x =>
      if hasHavoc A t x then [.assign t (pv 1 x) (.var t (pv 0 x))]
      else [.havoc t (pv 1 x)]
  | c => [c.rename (pv 1)]

/-- Branch-agreement CHK: at a conditional, the two copies' condition
registers must agree (the product branches on A's). -/
def prodTermChk (stride k : Nat) (Ba Bb : Block) : List Cmd :=
  match Ba.term, Bb.term with
  | .ifGoto cA _ _, .ifGoto cB _ _ =>
      let r := chkReg stride k Bb.cmds.length
      [.assign .bool r (.eqB (.var .bool (pv 0 cA)) (.var .bool (pv 1 cB))),
       .assert r]
  | _, _ => []

def prodBlock (A : Program) (stride k : Nat) (Ba Bb : Block) : Block where
  cmds := Ba.cmds.flatMap prodCmdA
    ++ Bb.cmds.zipIdx.flatMap (fun ci => prodCmdB A Ba stride k ci.2 ci.1)
    ++ prodTermChk stride k Ba Bb
  term := Ba.term.rename (pv 0)

def product (A B : Program) : Program where
  blocks := (A.blocks.zip B.blocks).zipIdx.map fun p =>
    prodBlock A (chkStride B.blocks) p.2 p.1.1 p.1.2
  entry := A.entry
  exit := A.exit

/-! ## Lockstep compatibility -/

/-- Same control shape, conditions free to differ (they get a CHK). -/
def termShapeOK : Terminator → Terminator → Bool
  | .halt, .halt => true
  | .goto t, .goto t' => decide (t = t')
  | .ifGoto _ t e, .ifGoto _ t' e' => decide (t = t') && decide (e = e')
  | _, _ => false

/-- The lockstep fragment: same block count and entry, per-block
matching terminator shape, and the (single, by `WellFormed`) asserts
in the same blocks. -/
def lockstep (A B : Program) : Bool :=
  decide (A.blocks.length = B.blocks.length)
    && decide (A.entry = B.entry)
    && ((A.blocks.zip B.blocks).all fun p => termShapeOK p.1.term p.2.term)
    && decide ((assertSites A).map (·.1) = (assertSites B).map (·.1))

/-! ## The transfer theorem -/

/-- The canonical product seed: both copies (and, harmlessly, the CHK
slots — they are always assigned) read the same underlying seed. This
is the witness the transfer proof drives the product with. -/
def dup (s0 : State) : State where
  regs := fun t x => s0.regs t (x / 3)
  blks := s0.blks

/-- Projecting a copy back out of a duplicated seed recovers the
original seed. -/
theorem dup_reindex (s0 : State) {j : Nat} (h : j < 3) :
    (dup s0).reindex (pv j) = s0 := by
  obtain ⟨r, b⟩ := s0
  show State.mk _ _ = _
  congr 1
  funext t x
  show r t (pv j x / 3) = r t x
  congr 1
  simp only [pv]
  omega

/-! ## Namespace arithmetic

Every disjointness fact the proof needs about the three register
namespaces is `omega` over `pv`. -/

theorem pv_eq_iff {j j' : Nat} (hj : j < 3) (hj' : j' < 3) {x y : Nat} :
    pv j x = pv j' y ↔ j = j' ∧ x = y := by
  constructor
  · intro h; unfold pv at h; omega
  · rintro ⟨rfl, rfl⟩; rfl

theorem pv_ne {j j' : Nat} (hj : j < 3) (hj' : j' < 3) (hne : j ≠ j')
    (x y : Nat) : pv j x ≠ pv j' y := fun h =>
  hne ((pv_eq_iff hj hj').mp h).1

theorem pv_pair_ne {t u : Ty} {j j' : Nat} (hj : j < 3) (hj' : j' < 3)
    (hne : j ≠ j') (x y : Nat) :
    ((t, pv j x) : Ty × Nat) ≠ (u, pv j' y) := fun h =>
  pv_ne hj hj' hne x y (congrArg Prod.snd h)

/-- Copy registers never alias CHK slots — stated with the `chkReg`
spelling so `rw` matches construction sites syntactically. -/
theorem pv_chk_pair_ne {t u : Ty} {j : Nat} (hj : j < 3) (hne : j ≠ 2)
    (x stride k i : Nat) :
    ((t, pv j x) : Ty × Nat) ≠ (u, chkReg stride k i) :=
  pv_pair_ne hj (by omega) hne x _

@[simp] theorem reindex_regs (s : State) (ρ : Nat → Nat) (t : Ty) (x : Nat) :
    (s.reindex ρ).regs t x = s.regs t (ρ x) := rfl

@[simp] theorem reindex_blks (s : State) (ρ : Nat → Nat) :
    (s.reindex ρ).blks = s.blks := rfl

theorem le_foldl_max : ∀ (l : List Nat) (a : Nat),
    a ≤ l.foldl max a ∧ ∀ x ∈ l, x ≤ l.foldl max a
  | [], a => ⟨Nat.le_refl a, fun x hx => absurd hx (List.not_mem_nil)⟩
  | b :: l, a => by
      obtain ⟨ha, hall⟩ := le_foldl_max l (max a b)
      refine ⟨Nat.le_trans (Nat.le_max_left a b) ha, fun x hx => ?_⟩
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact Nat.le_trans (Nat.le_max_right a x) ha
      · exact hall x hx'

/-- Per-block width bound: every CHK slot index used by block `k`
(`i ≤ Bb.cmds.length`) stays inside the block's window. -/
theorem lt_chkStride {Bs : List Block} {k : Nat} {Bb : Block}
    (hBb : Bs[k]? = some Bb) : Bb.cmds.length < chkStride Bs := by
  have hmem : Bb.cmds.length ∈ Bs.map (·.cmds.length) :=
    List.mem_map.mpr ⟨Bb, List.mem_of_getElem? hBb, rfl⟩
  have := (le_foldl_max (Bs.map (·.cmds.length)) 0).2 _ hmem
  unfold chkStride
  omega

theorem chkReg_inj {stride : Nat} {k i k' i' : Nat}
    (hi : i < stride) (hi' : i' < stride)
    (h : chkReg stride k i = chkReg stride k' i') : k = k' ∧ i = i' := by
  unfold chkReg pv at h
  have hm : stride * k + i = stride * k' + i' := by omega
  have hk : k = k' := by
    rcases Nat.lt_trichotomy k k' with hlt | heq | hgt
    · exfalso
      have : stride * (k + 1) ≤ stride * k' := Nat.mul_le_mul_left _ hlt
      have : stride * k + stride ≤ stride * k' := by
        rw [Nat.mul_succ] at this; omega
      omega
    · exact heq
    · exfalso
      have : stride * (k' + 1) ≤ stride * k := Nat.mul_le_mul_left _ hgt
      have : stride * k' + stride ≤ stride * k := by
        rw [Nat.mul_succ] at this; omega
      omega
  subst hk
  exact ⟨rfl, by omega⟩

/-! ## Lockstep unpacking -/

/-- The conjuncts of `lockstep`, in usable form. -/
theorem lockstep_facts {A B : Program} (hls : lockstep A B = true) :
    A.blocks.length = B.blocks.length ∧ A.entry = B.entry
      ∧ (∀ {k : Nat} {Ba Bb : Block}, A.block? k = some Ba →
          B.block? k = some Bb → termShapeOK Ba.term Bb.term = true)
      ∧ (assertSites A).map (·.1) = (assertSites B).map (·.1) := by
  unfold lockstep at hls
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hls
  obtain ⟨⟨⟨hlen, hentry⟩, hterm⟩, hsites⟩ := hls
  refine ⟨hlen, hentry, ?_, hsites⟩
  intro k Ba Bb hBa hBb
  have hmem : (Ba, Bb) ∈ A.blocks.zip B.blocks := by
    rw [List.mem_iff_getElem?]
    exact ⟨k, List.getElem?_zip_eq_some.mpr ⟨hBa, hBb⟩⟩
  exact List.all_eq_true.mp hterm (Ba, Bb) hmem

/-- The product's block table, pointwise. -/
theorem product_block? {A B : Program}
    (_hlen : A.blocks.length = B.blocks.length) {k : Nat} {Ba Bb : Block}
    (hBa : A.block? k = some Ba) (hBb : B.block? k = some Bb) :
    (product A B).block? k
      = some (prodBlock A (chkStride B.blocks) k Ba Bb) := by
  unfold product Program.block? at *
  rw [List.getElem?_map, List.getElem?_zipIdx,
    (List.getElem?_zip_eq_some (z := (Ba, Bb))).mpr ⟨hBa, hBb⟩]
  simp

theorem product_length {A B : Program}
    (hlen : A.blocks.length = B.blocks.length) :
    (product A B).blocks.length = A.blocks.length := by
  unfold product
  simp [List.length_zip, hlen]

theorem product_entry (A B : Program) : (product A B).entry = A.entry := rfl

theorem product_block?_of_lt {A B : Program}
    (hlen : A.blocks.length = B.blocks.length) {k : Nat}
    (hk : k < A.blocks.length) :
    ∃ Ba Bb, A.block? k = some Ba ∧ B.block? k = some Bb
      ∧ (product A B).block? k
          = some (prodBlock A (chkStride B.blocks) k Ba Bb) := by
  have hBa : A.block? k = some A.blocks[k] := List.getElem?_eq_getElem hk
  have hBb : B.block? k = some B.blocks[k] :=
    List.getElem?_eq_getElem (by omega)
  exact ⟨_, _, hBa, hBb, product_block? hlen hBa hBb⟩

/-! ## The product block's anatomy -/

/-- Write-target characterization: every register the product's block
`k` can define is a copy register (`pv 0` / `pv 1`) or a CHK slot in
block `k`'s own window. -/
theorem prodBlock_def_target {A : Program} {stride k : Nat} {Ba Bb : Block}
    {c : Cmd} (hc : c ∈ (prodBlock A stride k Ba Bb).cmds)
    {t : Ty} {w : Nat} (hdef : c.def? = some (t, w)) :
    (∃ x, w = pv 0 x) ∨ (∃ x, w = pv 1 x)
      ∨ (∃ i, i ≤ Bb.cmds.length ∧ w = chkReg stride k i) := by
  unfold prodBlock at hc
  rcases List.mem_append.mp hc with hc' | hcT
  · rcases List.mem_append.mp hc' with hcA | hcB
    · -- A-copy: renamed non-assert commands write `pv 0` registers
      obtain ⟨cA, -, hcA⟩ := List.mem_flatMap.mp hcA
      left
      cases cA with
      | assert r => simp [prodCmdA] at hcA
      | assign t' x e =>
          simp only [prodCmdA, List.mem_singleton] at hcA
          subst hcA
          cases hdef
          exact ⟨x, rfl⟩
      | havoc t' x =>
          simp only [prodCmdA, List.mem_singleton] at hcA
          subst hcA
          cases hdef
          exact ⟨x, rfl⟩
      | phi t' x arms =>
          simp only [prodCmdA, List.mem_singleton] at hcA
          subst hcA
          cases hdef
          exact ⟨x, rfl⟩
      | assume φ =>
          simp only [prodCmdA, List.mem_singleton] at hcA
          subst hcA
          cases hdef
    · -- B-copy: renamed / equated commands write `pv 1`; CHKs write slots
      obtain ⟨⟨cB, i⟩, hmem, hcB⟩ := List.mem_flatMap.mp hcB
      have hilen : i < Bb.cmds.length := by
        have := List.mem_zipIdx_iff_getElem?.mp hmem
        exact (List.getElem?_eq_some_iff.mp this).1
      cases cB with
      | assume φ =>
          simp only [prodCmdB] at hcB
          rcases List.mem_cons.mp hcB with rfl | hcB'
          · cases hdef
            exact Or.inr (Or.inr ⟨i, by omega, rfl⟩)
          · rcases List.mem_singleton.mp hcB' with rfl
            cases hdef
      | assert c' =>
          simp only [prodCmdB] at hcB
          rcases List.mem_cons.mp hcB with rfl | hcB'
          · cases hdef
            exact Or.inr (Or.inr ⟨i, by omega, rfl⟩)
          · rcases List.mem_singleton.mp hcB' with rfl
            cases hdef
      | havoc t' x =>
          simp only [prodCmdB] at hcB
          split at hcB
          · rcases List.mem_singleton.mp hcB with rfl
            cases hdef
            exact Or.inr (Or.inl ⟨x, rfl⟩)
          · rcases List.mem_singleton.mp hcB with rfl
            cases hdef
            exact Or.inr (Or.inl ⟨x, rfl⟩)
      | assign t' x e =>
          simp only [prodCmdB, List.mem_singleton] at hcB
          subst hcB
          cases hdef
          exact Or.inr (Or.inl ⟨x, rfl⟩)
      | phi t' x arms =>
          simp only [prodCmdB, List.mem_singleton] at hcB
          subst hcB
          cases hdef
          exact Or.inr (Or.inl ⟨x, rfl⟩)
  · -- terminator CHK
    unfold prodTermChk at hcT
    split at hcT
    · rcases List.mem_cons.mp hcT with rfl | hcT'
      · cases hdef
        exact Or.inr (Or.inr ⟨Bb.cmds.length, Nat.le_refl _, rfl⟩)
      · rcases List.mem_singleton.mp hcT' with rfl
        cases hdef
    · cases hcT

/-- The product block's assumes are exactly A's, renamed into copy 0:
`assumesOK` over the product block reduces to A-side conditions. -/
theorem prodBlock_assume {A : Program} {stride k : Nat} {Ba Bb : Block}
    {c : Cmd} (hc : c ∈ (prodBlock A stride k Ba Bb).cmds)
    {φ : BExp} (heq : c = .assume φ) :
    ∃ ψ : BExp, φ = ψ.rename (pv 0) ∧ .assume ψ ∈ Ba.cmds := by
  subst heq
  unfold prodBlock at hc
  rcases List.mem_append.mp hc with hc' | hcT
  · rcases List.mem_append.mp hc' with hcA | hcB
    · obtain ⟨cA, hmemA, hcA⟩ := List.mem_flatMap.mp hcA
      cases cA with
      | assume ψ =>
          simp only [prodCmdA, List.mem_singleton, Cmd.rename] at hcA
          exact ⟨ψ, Cmd.assume.inj hcA, hmemA⟩
      | assert r => simp [prodCmdA] at hcA
      | assign t' x e =>
          simp only [prodCmdA, List.mem_singleton, Cmd.rename] at hcA
          cases hcA
      | havoc t' x =>
          simp only [prodCmdA, List.mem_singleton, Cmd.rename] at hcA
          cases hcA
      | phi t' x arms =>
          simp only [prodCmdA, List.mem_singleton, Cmd.rename] at hcA
          cases hcA
    · obtain ⟨⟨cB, i⟩, -, hcB⟩ := List.mem_flatMap.mp hcB
      exfalso
      cases cB with
      | assume φ' =>
          simp only [prodCmdB] at hcB
          rcases List.mem_cons.mp hcB with h | h
          · cases h
          · rcases List.mem_singleton.mp h with h; cases h
      | assert c' =>
          simp only [prodCmdB] at hcB
          rcases List.mem_cons.mp hcB with h | h
          · cases h
          · rcases List.mem_singleton.mp h with h; cases h
      | havoc t' x =>
          simp only [prodCmdB] at hcB
          split at hcB <;> rcases List.mem_singleton.mp hcB with h <;> cases h
      | assign t' x e => simp [prodCmdB, Cmd.rename] at hcB
      | phi t' x arms => simp [prodCmdB, Cmd.rename] at hcB
  · exfalso
    unfold prodTermChk at hcT
    split at hcT
    · rcases List.mem_cons.mp hcT with h | h
      · cases h
      · rcases List.mem_singleton.mp h with h; cases h
    · cases hcT

/-! ## Edge correspondence

The product branches on A's renamed condition registers over A's edge
structure; `reach` over the product therefore mirrors `reach` over A. -/

theorem outEdges_prodBlock {A : Program} {stride k p : Nat} {Ba Bb : Block} :
    Vc.outEdges p (prodBlock A stride k Ba Bb)
      = (Vc.outEdges p Ba).map fun e =>
          (e.1, e.2.1, e.2.2.rename (pv 0)) := by
  show Vc.outEdges p { cmds := _, term := Ba.term.rename (pv 0) } = _
  cases hT : Ba.term <;>
    simp [Vc.outEdges, Terminator.rename, hT, Exp.rename]

theorem mem_edgesTo_product {A B : Program}
    (hlen : A.blocks.length = B.blocks.length) {b p : Nat} {cond' : BExp} :
    (p, cond') ∈ Vc.edgesTo (product A B) b ↔
      ∃ cond, (p, cond) ∈ Vc.edgesTo A b ∧ cond' = cond.rename (pv 0) := by
  constructor
  · intro h
    obtain ⟨Bp', hBp', hout⟩ := mem_allEdges_elim (mem_edgesTo.mp h)
    have hplt : p < (product A B).blocks.length :=
      (List.getElem?_eq_some_iff.mp hBp').1
    rw [product_length hlen] at hplt
    obtain ⟨Ba, Bb, hBa, hBb, hPB⟩ := product_block?_of_lt hlen hplt
    obtain rfl : Bp' = prodBlock A (chkStride B.blocks) p Ba Bb :=
      Option.some.inj (hBp'.symm.trans hPB)
    rw [outEdges_prodBlock, List.mem_map] at hout
    obtain ⟨⟨q, s, cond⟩, hmem, heq⟩ := hout
    obtain ⟨rfl, -⟩ := outEdges_shape hmem
    simp only [Prod.mk.injEq] at heq
    obtain ⟨-, hs, rfl⟩ := heq
    subst hs
    exact ⟨cond, mem_edgesTo.mpr (mem_allEdges_intro hBa hmem), rfl⟩
  · rintro ⟨cond, h, rfl⟩
    obtain ⟨Ba, hBa, hout⟩ := mem_allEdges_elim (mem_edgesTo.mp h)
    have hplt : p < A.blocks.length := (List.getElem?_eq_some_iff.mp hBa).1
    have hBb : B.block? p = some B.blocks[p] :=
      List.getElem?_eq_getElem (by omega)
    refine mem_edgesTo.mpr (mem_allEdges_intro (product_block? hlen hBa hBb) ?_)
    rw [outEdges_prodBlock, List.mem_map]
    exact ⟨(p, b, cond), hout, rfl⟩

/-- Edge conditions have no guard atoms and, renamed, evaluate through
the copy-0 projection. -/
theorem edge_cond_rename_eval {A : Program} {b p : Nat} {cond : BExp}
    (hmem : (p, cond) ∈ Vc.edgesTo A b) {R W : State}
    (hv : ∀ t x, R.regs t (pv 0 x) = W.regs t x) :
    (cond.rename (pv 0)).eval R = cond.eval W := by
  obtain ⟨hbnil, -⟩ := edge_cond_vars hmem
  rw [Exp.eval_rename]
  exact eval_congr cond (fun q _ => hv q.1 q.2)
    (fun q hq => by rw [hbnil] at hq; cases hq)

/-- `reach` over the product is `reach` over A, at any state whose
copy-0 half mirrors `W` and whose guards below `b` mirror `W`'s. -/
theorem reach_product {A B : Program} (hfwd : forwardOK A = true)
    (hlen : A.blocks.length = B.blocks.length) {b : Nat} {R W : State}
    (hv : ∀ t x, R.regs t (pv 0 x) = W.regs t x)
    (hb : ∀ p, p < b → R.blks p = W.blks p) :
    reach (product A B) R b = reach A W b := by
  unfold reach
  rw [product_entry]
  congr 1
  rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨⟨p, cond'⟩, hmem, hpc⟩
    obtain ⟨cond, hmemA, rfl⟩ := (mem_edgesTo_product hlen).mp hmem
    rw [Bool.and_eq_true] at hpc
    have hplt : p < b := pred_lt hfwd (mem_predsOf.mpr ⟨cond, hmemA⟩)
    refine ⟨(p, cond), hmemA, ?_⟩
    rw [Bool.and_eq_true]
    exact ⟨by rw [← hb p hplt]; exact hpc.1,
      by rw [← edge_cond_rename_eval hmemA hv]; exact hpc.2⟩
  · rintro ⟨⟨p, cond⟩, hmemA, hpc⟩
    rw [Bool.and_eq_true] at hpc
    have hplt : p < b := pred_lt hfwd (mem_predsOf.mpr ⟨cond, hmemA⟩)
    refine ⟨(p, cond.rename (pv 0)), (mem_edgesTo_product hlen).mpr
      ⟨cond, hmemA, rfl⟩, ?_⟩
    rw [Bool.and_eq_true]
    exact ⟨by rw [hb p hplt]; exact hpc.1,
      by rw [edge_cond_rename_eval hmemA hv]; exact hpc.2⟩

/-! ## Assume correspondence -/

/-- A-assumes survive verbatim (renamed) into the product block. -/
theorem prodBlock_assume_mem {A : Program} {stride k : Nat} {Ba Bb : Block}
    {ψ : BExp} (hmem : Cmd.assume ψ ∈ Ba.cmds) :
    Cmd.assume (ψ.rename (pv 0)) ∈ (prodBlock A stride k Ba Bb).cmds := by
  unfold prodBlock
  refine List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl ?_)))
  exact List.mem_flatMap.mpr ⟨.assume ψ, hmem, by
    simp [prodCmdA, Cmd.rename]⟩

/-- `assumesOK` over a product block is `assumesOK` over A's block, at
any state whose copy-0 half mirrors `W` (A's assumes are guard-free). -/
theorem assumesOK_prodBlock {A : Program} (hgf : guardFreeOK A = true)
    {stride k b : Nat} {Ba Bb : Block} (hBa : A.block? b = some Ba)
    {R W : State} (hv : ∀ t x, R.regs t (pv 0 x) = W.regs t x) :
    assumesOK R (prodBlock A stride k Ba Bb) = assumesOK W Ba := by
  have heval : ∀ ψ : BExp, Cmd.assume ψ ∈ Ba.cmds →
      (ψ.rename (pv 0)).eval R = ψ.eval W := by
    intro ψ hmem
    have hgfc := guardFree_at hgf (List.mem_of_getElem? hBa) hmem
    simp only [cmdGuardFree, List.isEmpty_iff] at hgfc
    rw [Exp.eval_rename]
    exact eval_congr ψ (fun q _ => hv q.1 q.2)
      (fun q hq => by rw [hgfc] at hq; cases hq)
  rw [Bool.eq_iff_iff]
  unfold assumesOK
  rw [List.all_eq_true, List.all_eq_true]
  constructor
  · intro h c hc
    cases c with
    | assume ψ =>
        show ψ.eval W = true
        rw [← heval ψ hc]
        exact h _ (prodBlock_assume_mem hc)
    | assign t x e => trivial
    | havoc t x => trivial
    | phi t x arms => trivial
    | assert r => trivial
  · intro h c hc
    cases c with
    | assume φ =>
        obtain ⟨ψ, rfl, hmemA⟩ := prodBlock_assume hc rfl
        show (ψ.rename (pv 0)).eval R = true
        rw [heval ψ hmemA]
        exact h _ hmemA
    | assign t x e => trivial
    | havoc t x => trivial
    | phi t x arms => trivial
    | assert r => trivial

/-! ## CHK sites -/

/-- The rule-4 CHK of a B-assume sits in the product block. -/
theorem chk_assume_mem {A : Program} {stride k i : Nat} {Ba Bb : Block}
    {φ : BExp} (hi : Bb.cmds[i]? = some (.assume φ)) :
    Cmd.assign .bool (chkReg stride k i) (φ.rename (pv 1))
        ∈ (prodBlock A stride k Ba Bb).cmds
      ∧ Cmd.assert (chkReg stride k i)
        ∈ (prodBlock A stride k Ba Bb).cmds := by
  have hmemz : ((Cmd.assume φ, i) : Cmd × Nat) ∈ Bb.cmds.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr hi
  constructor <;>
    refine List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr
      (List.mem_flatMap.mpr ⟨(Cmd.assume φ, i), hmemz, ?_⟩))))
  · simp [prodCmdB]
  · simp [prodCmdB]

/-- The rule-5b CHK of the assert pair sits in the product block. -/
theorem chk_assert_mem {A : Program} {stride k i : Nat} {Ba Bb : Block}
    {c' : Nat} (hi : Bb.cmds[i]? = some (.assert c')) {cA : Nat}
    (hreg : Ba.assertReg? = some cA) :
    Cmd.assign .bool (chkReg stride k i)
        (.eqB (.var .bool (pv 0 cA)) (.var .bool (pv 1 c')))
        ∈ (prodBlock A stride k Ba Bb).cmds
      ∧ Cmd.assert (chkReg stride k i)
        ∈ (prodBlock A stride k Ba Bb).cmds := by
  have hmemz : ((Cmd.assert c', i) : Cmd × Nat) ∈ Bb.cmds.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr hi
  constructor <;>
    refine List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr
      (List.mem_flatMap.mpr ⟨(Cmd.assert c', i), hmemz, ?_⟩))))
  · simp [prodCmdB, hreg]
  · simp [prodCmdB, hreg]

/-- The rule-7 branch CHK sits in the product block. -/
theorem chk_branch_mem {A : Program} {stride k : Nat} {Ba Bb : Block}
    {cA tA eA cB tB eB : Nat} (hta : Ba.term = .ifGoto cA tA eA)
    (htb : Bb.term = .ifGoto cB tB eB) :
    Cmd.assign .bool (chkReg stride k Bb.cmds.length)
        (.eqB (.var .bool (pv 0 cA)) (.var .bool (pv 1 cB)))
        ∈ (prodBlock A stride k Ba Bb).cmds
      ∧ Cmd.assert (chkReg stride k Bb.cmds.length)
        ∈ (prodBlock A stride k Ba Bb).cmds := by
  constructor <;>
    refine List.mem_append.mpr (Or.inr ?_) <;>
    · unfold prodTermChk
      rw [hta, htb]
      simp

/-- Extraction: with the product safe, any CHK site of an active block
carries a true register at the final state. -/
theorem safe_denot_site_true {P : Program} (hP : Safe_denot P) (σ : State)
    {b i r : Nat} (hsite : (b, i, r) ∈ Vc.assertSites P)
    (hblt : b < P.blocks.length) (hblk : (denot P σ).blks b = true) :
    (denot P σ).regs .bool r = true := by
  have h := hP σ
  rw [denot_blks_exit] at h
  unfold reachExit at h
  rw [List.any_eq_false] at h
  have hthis : ¬((prefixState P σ P.blocks.length).blks b
      && !(prefixState P σ P.blocks.length).regs .bool r) = true := h _ hsite
  have hb' : (prefixState P σ P.blocks.length).blks b = true := by
    rw [← denot_blks_lt hblt]; exact hblk
  rw [denot_regs]
  rcases Bool.eq_false_or_eq_true
    ((prefixState P σ P.blocks.length).regs .bool r) with ht | hf
  · exact ht
  · exact absurd (by rw [hb', hf]; rfl) hthis

/-! ## A/B-side final-state facts

Everything the transfer proof consumes about `A` and `B` individually,
stated at their final denotational states. -/

theorem any_congr_mem {α : Type _} {p q : α → Bool} :
    ∀ {l : List α}, (∀ a ∈ l, p a = q a) → l.any p = l.any q
  | [], _ => rfl
  | a :: l, h => by
      rw [List.any_cons, List.any_cons, h a (List.mem_cons_self ..),
        any_congr_mem (fun a' ha' => h a' (List.mem_cons_of_mem _ ha'))]

theorem all_congr_mem {α : Type _} {p q : α → Bool} :
    ∀ {l : List α}, (∀ a ∈ l, p a = q a) → l.all p = l.all q
  | [], _ => rfl
  | a :: l, h => by
      rw [List.all_cons, List.all_cons, h a (List.mem_cons_self ..),
        all_congr_mem (fun a' ha' => h a' (List.mem_cons_of_mem _ ha'))]

/-- Final-state guard characterization: a block's guard is its `reach`
and `assumesOK` evaluated at the *final* state (all reads are frozen by
the end of the block's own fold). -/
theorem denot_blks_final_char {P : Program} {s0 : State}
    (hwf : WellFormed P) {v : Nat} {Bv : Block}
    (hBv : P.block? v = some Bv) :
    (denot P s0).blks v
      = (reach P (denot P s0) v && assumesOK (denot P s0) Bv) := by
  rw [denot_blks_char hBv]
  congr 1
  · -- reach transports: guards of preds are `< v`, conditions read
    -- registers defined at the predecessor's terminator or earlier
    unfold reach
    congr 1
    refine any_congr_mem (fun ⟨p, cond⟩ hmem => ?_)
    have hplt : p < v := pred_lt hwf.fwd (mem_predsOf.mpr ⟨cond, hmem⟩)
    obtain ⟨hbnil, hbvars⟩ := edge_cond_vars hmem
    have hcond : cond.eval
          (Bv.cmds.foldl (denotCmd P) (prefixState P s0 v))
        = cond.eval (denot P s0) := by
      rw [eval_denot_eq_block hBv cond
        (fun q hq d j hd => by
          obtain ⟨r, B', t', e', rfl, hB', hterm'⟩ := hbvars q hq
          have hterm_use := usesOK_term hwf.uses hB'
          simp only [termUsesOK, hterm'] at hterm_use
          have := useOK_before hterm_use d j hd
          simp only [posLt, Bool.or_eq_true, Bool.and_eq_true,
            decide_eq_true_eq] at this
          omega)
        (fun q hq => by rw [hbnil] at hq; cases hq)]
    rw [hcond, denot_blks_of_lt hBv hplt]
  · -- assumesOK transports: assume reads are dominated at their sites
    unfold assumesOK
    refine all_congr_mem (fun c hc => ?_)
    cases c with
    | assume φ =>
        obtain ⟨i, hci⟩ := List.mem_iff_getElem?.mp hc
        have hu := usesOK_cmd hwf.uses hBv hci
        simp only [cmdUsesOK] at hu
        have hgfc := guardFree_at hwf.gf (List.mem_of_getElem? hBv) hc
        simp only [cmdGuardFree, List.isEmpty_iff] at hgfc
        show φ.eval _ = φ.eval _
        rw [eval_denot_eq_block hBv φ
          (fun p hp d j hd => by
            have := expUsesOK_before hu p hp d j hd
            simp only [posLt, Bool.or_eq_true, Bool.and_eq_true,
              decide_eq_true_eq] at this
            omega)
          (fun q hq => by rw [hgfc] at hq; cases hq)]
    | assign t x e => rfl
    | havoc t x => rfl
    | phi t x arms => rfl
    | assert r => rfl

/-- A register whose only definition is a havoc keeps its seed value:
`denotCmd` treats havoc as identity, and SSA rules out other writers. -/
theorem denotCmd_regs_no_write {P : Program} {W : State} {c : Cmd}
    {t : Ty} {x : Nat} (hassign : ∀ e, c ≠ .assign t x e)
    (hphi : ∀ arms, c ≠ .phi t x arms) :
    (denotCmd P W c).regs t x = W.regs t x := by
  cases c with
  | assign t' x' e =>
      by_cases h : ((t', x') : Ty × Nat) = (t, x)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp h
        exact absurd rfl (hassign e)
      · exact State.upd_regs_of_ne W (fun heq => h heq.symm) _
  | phi t' x' arms =>
      by_cases h : ((t', x') : Ty × Nat) = (t, x)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp h
        exact absurd rfl (hphi arms)
      · exact State.upd_regs_of_ne W (fun heq => h heq.symm) _
  | havoc t' x' => rfl
  | assume φ => rfl
  | assert r => rfl

theorem denot_regs_of_havoc_def {P : Program} {s0 : State}
    (hssa : ssaOK P = true) {t : Ty} {x : Nat} {d j : Nat} {Bd : Block}
    (hBd : P.block? d = some Bd) (hcj : Bd.cmds[j]? = some (.havoc t x)) :
    (denot P s0).regs t x = s0.regs t x := by
  have hno : ∀ (b : Nat) (Bb : Block), P.block? b = some Bb →
      ∀ c ∈ Bb.cmds, (∀ e, c ≠ .assign t x e) ∧ (∀ arms, c ≠ .phi t x arms) := by
    intro b Bb hBb c hc
    obtain ⟨i, hci⟩ := List.mem_iff_getElem?.mp hc
    constructor
    · intro e heq
      subst heq
      obtain ⟨rfl, rfl⟩ := ssa_unique hssa ⟨Bd, _, hBd, hcj, rfl⟩
        ⟨Bb, _, hBb, hci, rfl⟩
      obtain rfl : Bd = Bb := Option.some.inj (hBd.symm.trans hBb)
      have := Option.some.inj (hcj.symm.trans hci)
      cases this
    · intro arms heq
      subst heq
      obtain ⟨rfl, rfl⟩ := ssa_unique hssa ⟨Bd, _, hBd, hcj, rfl⟩
        ⟨Bb, _, hBb, hci, rfl⟩
      obtain rfl : Bd = Bb := Option.some.inj (hBd.symm.trans hBb)
      have := Option.some.inj (hcj.symm.trans hci)
      cases this
  have hfold : ∀ (cs : List Cmd) (W : State),
      (∀ c ∈ cs, (∀ e, c ≠ .assign t x e) ∧ (∀ arms, c ≠ .phi t x arms)) →
      (cs.foldl (denotCmd P) W).regs t x = W.regs t x := by
    intro cs
    induction cs with
    | nil => intro W _; rfl
    | cons c cs ih =>
        intro W h
        rw [List.foldl_cons,
          ih _ (fun c' hc' => h c' (List.mem_cons_of_mem _ hc')),
          denotCmd_regs_no_write (h c (List.mem_cons_self ..)).1
            (h c (List.mem_cons_self ..)).2]
  have hpfx : ∀ k, (prefixState P s0 k).regs t x = s0.regs t x := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
        rw [prefixState_succ]
        unfold denotBlock
        cases hBk : P.block? k with
        | none => exact ih
        | some Bk =>
            show ((Bk.cmds.foldl (denotCmd P) _).regs t x) = _
            rw [hfold _ _ (hno k Bk hBk), ih]
  rw [denot_regs]
  exact hpfx P.blocks.length

/-! ## Cross-program CFG transfer -/

/-- Same-shape terminators have identical target lists. -/
theorem termTargets_shape_eq {Ta Tb : Terminator}
    (h : termShapeOK Ta Tb = true) : termTargets Ta = termTargets Tb := by
  cases Ta <;> cases Tb <;> simp_all [termShapeOK, termTargets]

/-- The `(source, target)` projection of the edge lists coincides under
lockstep: same blocks, same terminator shapes. -/
theorem allEdges_proj_eq {A B : Program}
    (hlen : A.blocks.length = B.blocks.length)
    (hterm : ∀ {k : Nat} {Ba Bb : Block}, A.block? k = some Ba →
      B.block? k = some Bb → termShapeOK Ba.term Bb.term = true) :
    (Vc.allEdges A).map (fun e => (e.1, e.2.1))
      = (Vc.allEdges B).map (fun e => (e.1, e.2.1)) := by
  have houtEdges : ∀ (p : Nat) (Ba Bb : Block),
      termShapeOK Ba.term Bb.term = true →
      (Vc.outEdges p Ba).map (fun e => (e.1, e.2.1))
        = (Vc.outEdges p Bb).map (fun e => (e.1, e.2.1)) := by
    intro p Ba Bb h
    cases hta : Ba.term <;> cases htb : Bb.term <;>
      rw [hta, htb] at h <;>
      simp_all [termShapeOK, Vc.outEdges]
  unfold Vc.allEdges
  rw [List.map_flatten, List.map_flatten, List.map_map, List.map_map]
  congr 1
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_map, List.getElem?_map, List.getElem?_zipIdx,
    List.getElem?_zipIdx]
  cases hA : A.blocks[i]? with
  | none =>
      have : B.blocks[i]? = none := by
        rw [List.getElem?_eq_none_iff] at hA ⊢
        omega
      rw [this]
  | some Ba =>
      have hilt : i < A.blocks.length := (List.getElem?_eq_some_iff.mp hA).1
      have hB : B.blocks[i]? = some B.blocks[i] :=
        List.getElem?_eq_getElem (by omega)
      rw [hB]
      simp only [Option.map_some, Function.comp]
      congr 1
      exact houtEdges _ _ _ (hterm hA hB)

theorem predsOf_eq {A B : Program}
    (hlen : A.blocks.length = B.blocks.length)
    (hterm : ∀ {k : Nat} {Ba Bb : Block}, A.block? k = some Ba →
      B.block? k = some Bb → termShapeOK Ba.term Bb.term = true) :
    predsOf A = predsOf B := by
  funext S
  unfold predsOf
  congr 1
  have h1 : (Vc.edgesTo A S).map (·.1)
      = (Vc.allEdges A).filterMap fun e =>
          if e.2.1 = S then some e.1 else none := by
    unfold Vc.edgesTo
    rw [List.map_filterMap]
    congr 1
    funext ⟨p, s, c⟩
    by_cases hs : s = S <;> simp [hs]
  have h2 : (Vc.edgesTo B S).map (·.1)
      = (Vc.allEdges B).filterMap fun e =>
          if e.2.1 = S then some e.1 else none := by
    unfold Vc.edgesTo
    rw [List.map_filterMap]
    congr 1
    funext ⟨p, s, c⟩
    by_cases hs : s = S <;> simp [hs]
  have h3 : ∀ (P' : Program),
      ((Vc.allEdges P').filterMap fun e => if e.2.1 = S then some e.1 else none)
        = ((Vc.allEdges P').map (fun e => (e.1, e.2.1))).filterMap
            fun e => if e.2 = S then some e.1 else none := by
    intro P'
    rw [List.filterMap_map]
    rfl
  rw [h1, h2, h3, h3, allEdges_proj_eq hlen hterm]

theorem domTable_eq {A B : Program}
    (hlen : A.blocks.length = B.blocks.length) (hentry : A.entry = B.entry)
    (hpreds : predsOf A = predsOf B) : domTable A = domTable B := by
  unfold domTable
  rw [hlen, hentry, hpreds]

theorem domClosedOK_transfer {A B : Program}
    (htab : domTable A = domTable B) (hentry : A.entry = B.entry)
    (hproj : (Vc.allEdges A).map (fun e => (e.1, e.2.1))
      = (Vc.allEdges B).map (fun e => (e.1, e.2.1)))
    (hdcB : domClosedOK B = true) : domClosedOK A = true := by
  unfold domClosedOK at *
  rw [htab, hentry]
  rw [Bool.and_eq_true] at hdcB ⊢
  refine ⟨hdcB.1, ?_⟩
  have hfac : ∀ (P' : Program), (Vc.allEdges P').all
      (fun (e : Nat × Nat × BExp) => e.2.1 = B.entry
        || ((domTable B).getD e.2.1 []).all fun d =>
            d = e.2.1 || ((domTable B).getD e.1 []).contains d)
      = ((Vc.allEdges P').map (fun e => (e.1, e.2.1))).all
          (fun (e : Nat × Nat) => e.2 = B.entry
            || ((domTable B).getD e.2 []).all fun d =>
                d = e.2 || ((domTable B).getD e.1 []).contains d) := by
    intro P'
    rw [List.all_map]
    rfl
  rw [hfac, hproj, ← hfac]
  exact hdcB.2

/-- Dominators of active blocks are active (A-side, via `dom_visited`
over the activeList's taken-edge chain). -/
theorem active_dom_closed {A : Program} (hwfA : WellFormed A)
    (hdcA : domClosedOK A = true) {s0 : State} {u : Nat}
    (hu : u ∈ activeList A s0) {d : Nat} (hd : d ∈ domOf A u) :
    d ∈ activeList A s0 := by
  have hhead := (denot_hentry hwfA.fwd hwfA.uses hu).2
  exact dom_visited hdcA hwfA.fwd (denot_hedge hwfA) hhead u hu d hd

/-! ## Cross-program phi evaluation -/

/-- Renamed phi chains evaluate through the reindexed state; the chain
shape only consults the entry index, shared under lockstep. -/
theorem phiChain_rename_eval {P Q : Program} (hent : Q.entry = P.entry)
    (ρ : Nat → Nat) {t : Ty} (W : State) :
    ∀ (a : Nat × Nat) (rest : List (Nat × Nat)),
      (Vc.phiChain Q t (a.1, ρ a.2) (rest.map fun ar => (ar.1, ρ ar.2))).eval W
        = (Vc.phiChain P t a rest).eval (W.reindex ρ)
  | (p, s), [] => rfl
  | (p, s), a' :: rest' => by
      simp only [Vc.phiChain, List.map_cons, Vc.eval_mkIte]
      have hg : (Vc.guardOf Q p).eval W
          = (Vc.guardOf P p).eval (W.reindex ρ) := by
        unfold Vc.guardOf
        rw [hent]
        split <;> rfl
      rw [hg, phiChain_rename_eval hent ρ W a' rest']
      rfl

theorem lookupArm_map (ρ : Nat → Nat) (p : Nat) :
    ∀ (arms : PhiArms),
      lookupArm (arms.map fun ar => (ar.1, ρ ar.2)) p
        = (lookupArm arms p).map ρ
  | [] => rfl
  | (q, s) :: rest => by
      cases hb : (p == q) with
      | true =>
          simp only [lookupArm, List.map_cons, List.lookup, hb,
            Option.map_some]
      | false =>
          simp only [lookupArm, List.map_cons, List.lookup, hb]
          exact lookupArm_map ρ p rest

theorem findAssert_eq {cA : Nat} :
    ∀ {cs : List Cmd}, Cmd.assert cA ∈ cs →
      (∀ r, Cmd.assert r ∈ cs → r = cA) →
      (cs.findSome? fun c => match c with
        | .assert r => some r | _ => none) = some cA
  | [], hmem, _ => absurd hmem List.not_mem_nil
  | c :: cs, hmem, huniq => by
      rw [List.findSome?_cons]
      cases c with
      | assert r =>
          obtain rfl : r = cA := huniq r (List.mem_cons_self ..)
          rfl
      | assign t x e =>
          exact findAssert_eq
            ((List.mem_cons.mp hmem).resolve_left (by intro h; cases h))
            (fun r hr => huniq r (List.mem_cons_of_mem _ hr))
      | havoc t x =>
          exact findAssert_eq
            ((List.mem_cons.mp hmem).resolve_left (by intro h; cases h))
            (fun r hr => huniq r (List.mem_cons_of_mem _ hr))
      | phi t x arms =>
          exact findAssert_eq
            ((List.mem_cons.mp hmem).resolve_left (by intro h; cases h))
            (fun r hr => huniq r (List.mem_cons_of_mem _ hr))
      | assume φ =>
          exact findAssert_eq
            ((List.mem_cons.mp hmem).resolve_left (by intro h; cases h))
            (fun r hr => huniq r (List.mem_cons_of_mem _ hr))

/-- The unique assert of a block is what `assertReg?` finds. -/
theorem assertReg?_eq {Ba : Block} {cA : Nat}
    (hmem : Cmd.assert cA ∈ Ba.cmds)
    (huniq : ∀ r, Cmd.assert r ∈ Ba.cmds → r = cA) :
    Ba.assertReg? = some cA :=
  findAssert_eq hmem huniq

/-! ## The transfer invariant

The witness seed carries both programs' *final* fold states side by
side, so every copy write during the product fold is a self-write
(coadequacy's trick, doubled). `HalfA` is unconditional; `HalfB` is
scoped to `GoodB` registers — those whose B-definitions sit in
A-active blocks or are havocs — because at A-dead blocks the B-copy's
phis select by the product's (= A's) guards and write junk into
exactly the non-`GoodB` registers. -/

def prodSeed (A B : Program) (s0 : State) : State where
  regs := fun t w =>
    if w % 3 = 1 then (denot B s0).regs t (w / 3)
    else (denot A s0).regs t (w / 3)
  blks := fun _ => false

def HalfA (A : Program) (s0 : State) (R : State) : Prop :=
  ∀ (t : Ty) (x : Nat), R.regs t (pv 0 x) = (denot A s0).regs t x

def GoodB (A B : Program) (s0 : State) (t : Ty) (x : Nat) : Prop :=
  ∀ d j, IsDefAt B (t, x) d j →
    (denot A s0).blks d = true
      ∨ ∃ Bd, B.block? d = some Bd ∧ Bd.cmds[j]? = some (.havoc t x)

def HalfB (A B : Program) (s0 : State) (R : State) : Prop :=
  ∀ (t : Ty) (x : Nat), GoodB A B s0 t x →
    R.regs t (pv 1 x) = (denot B s0).regs t x

theorem prodSeed_halfA (A B : Program) (s0 : State) :
    HalfA A s0 (prodSeed A B s0) := by
  intro t x
  show (if pv 0 x % 3 = 1 then _ else _) = _
  rw [if_neg (by unfold pv; omega)]
  unfold pv
  congr 1
  omega

theorem prodSeed_halfB (A B : Program) (s0 : State) :
    HalfB A B s0 (prodSeed A B s0) := by
  intro t x _
  show (if pv 1 x % 3 = 1 then _ else _) = _
  rw [if_pos (by unfold pv; omega)]
  unfold pv
  congr 1
  omega

/-- CHK slots are written only inside their own block's window. -/
theorem product_chk_defs {A B : Program}
    (hlen : A.blocks.length = B.blocks.length) {b i : Nat}
    (hi : i < chkStride B.blocks) {d j : Nat}
    (hd : IsDefAt (product A B) (.bool, chkReg (chkStride B.blocks) b i) d j) :
    d = b := by
  obtain ⟨Bd, c, hBd, hcj, hdef⟩ := hd
  have hdlt : d < A.blocks.length := by
    have := (List.getElem?_eq_some_iff.mp hBd).1
    rwa [product_length hlen] at this
  obtain ⟨Ba', Bb', hBa', hBb', hPB⟩ := product_block?_of_lt hlen hdlt
  obtain rfl : Bd = prodBlock A (chkStride B.blocks) d Ba' Bb' :=
    Option.some.inj (hBd.symm.trans hPB)
  rcases prodBlock_def_target (List.mem_of_getElem? hcj) hdef with
    ⟨x, hx⟩ | ⟨x, hx⟩ | ⟨i', hi'le, hx⟩
  · unfold chkReg at hx
    exact absurd hx (pv_ne (by omega) (by omega) (by omega) _ _)
  · unfold chkReg at hx
    exact absurd hx (pv_ne (by omega) (by omega) (by omega) _ _)
  · have hi' : i' < chkStride B.blocks :=
      Nat.lt_of_le_of_lt hi'le (lt_chkStride hBb')
    exact ((chkReg_inj hi hi' hx).1).symm

/-- CHK slots survive from the end of their block to the final state. -/
theorem product_chk_stable {A B : Program} {σ : State}
    (hlen : A.blocks.length = B.blocks.length) {b i : Nat}
    (hi : i < chkStride B.blocks) (hble : b < A.blocks.length) :
    (denot (product A B) σ).regs .bool (chkReg (chkStride B.blocks) b i)
      = (prefixState (product A B) σ (b + 1)).regs .bool
          (chkReg (chkStride B.blocks) b i) := by
  rw [denot_regs]
  exact prefixState_regs_stable
    (fun d j hd => Nat.lt_succ_of_le (Nat.le_of_eq (product_chk_defs hlen hi hd)))
    (by rw [product_length hlen]; omega)

/-! ## Segment folds

The A-copy fold is the *identity*: with `HalfA` at the input and the
guards of earlier blocks agreeing with A's, every assign/phi recomputes
exactly the value already present (`upd_self`). -/

theorem prodCmdA_fold {A B : Program} {s0 : State} (hwfA : WellFormed A)
    {b : Nat} {Ba : Block} (hBa : A.block? b = some Ba) :
    ∀ (l : List Cmd), (∀ c ∈ l, c ∈ Ba.cmds) →
      ∀ (R : State), HalfA A s0 R →
        (∀ p, p < b → R.blks p = (denot A s0).blks p) →
        (l.flatMap prodCmdA).foldl (denotCmd (product A B)) R = R
  | [], _, R, _, _ => rfl
  | c :: l, hsub, R, hA, hblks => by
      have hcmem : c ∈ Ba.cmds := hsub _ (List.mem_cons_self ..)
      rw [List.flatMap_cons, List.foldl_append]
      have hstep : (prodCmdA c).foldl (denotCmd (product A B)) R = R := by
        cases c with
        | assert r => rfl
        | assume φ => rfl
        | havoc t x => rfl
        | assign t x e =>
            show denotCmd (product A B) R
              (.assign t (pv 0 x) (e.rename (pv 0))) = R
            obtain ⟨i, hci⟩ := List.mem_iff_getElem?.mp hcmem
            have hgfc := guardFree_at hwfA.gf (List.mem_of_getElem? hBa) hcmem
            simp only [cmdGuardFree, List.isEmpty_iff] at hgfc
            have hv : (e.rename (pv 0)).eval R = R.regs t (pv 0 x) :=
              calc (e.rename (pv 0)).eval R
                  = e.eval (R.reindex (pv 0)) := Exp.eval_rename ..
                _ = e.eval (denot A s0) :=
                    eval_congr e (fun p _ => hA p.1 p.2)
                      (fun q hq => by rw [hgfc] at hq; cases hq)
                _ = (denot A s0).regs t x := (denot_assign hwfA hBa hci).symm
                _ = R.regs t (pv 0 x) := (hA t x).symm
            show R.upd t (pv 0 x) ((e.rename (pv 0)).eval R) = R
            rw [hv, State.upd_self]
        | phi t x arms =>
            show denotCmd (product A B) R
              (.phi t (pv 0 x) (arms.map fun a => (a.1, pv 0 a.2))) = R
            have harms := phiOK_at hwfA.phi hBa hcmem
            cases arms with
            | nil => simp [phiArmsOK] at harms
            | cons a rest =>
                have hv : (Vc.phiRhs (product A B) t
                    ((a :: rest).map fun ar => (ar.1, pv 0 ar.2))).eval R
                    = R.regs t (pv 0 x) :=
                  calc (Vc.phiRhs (product A B) t
                        ((a :: rest).map fun ar => (ar.1, pv 0 ar.2))).eval R
                      = (Vc.phiChain (product A B) t (a.1, pv 0 a.2)
                          (rest.map fun ar => (ar.1, pv 0 ar.2))).eval R := by
                        rw [List.map_cons]; rfl
                    _ = (Vc.phiChain A t a rest).eval (R.reindex (pv 0)) :=
                        phiChain_rename_eval (P := A) (Q := product A B)
                          rfl (pv 0) R a rest
                    _ = (Vc.phiRhs A t (a :: rest)).eval (R.reindex (pv 0)) :=
                        rfl
                    _ = (Vc.phiRhs A t (a :: rest)).eval (denot A s0) :=
                        eval_congr _ (fun p _ => hA p.1 p.2)
                          (fun q hq => by
                            obtain ⟨s', hqs⟩ := phiRhs_blkVars q hq
                            exact hblks q (phiArm_lt harms hqs))
                    _ = (denot A s0).regs t x :=
                        (denot_phi hwfA hBa hcmem).symm
                    _ = R.regs t (pv 0 x) := (hA t x).symm
                show R.upd t (pv 0 x) _ = R
                rw [hv, State.upd_self]
      rw [hstep]
      exact prodCmdA_fold hwfA hBa l
        (fun c' hc' => hsub c' (List.mem_cons_of_mem _ hc')) R hA hblks

/-! ## Goodness transfer

A register read by a B-side command of an A-active block is `GoodB`:
its definitions sit in the same (active) block or in a dominator,
dominators are shared with A (same CFG), and dominators of A-active
blocks are A-active. -/

theorem good_of_use {A B : Program} {s0 : State}
    (hwfA : WellFormed A) (hdcA : domClosedOK A = true)
    (htab : domTable A = domTable B) {b i : Nat}
    (hblt : b < A.blocks.length) (hactive : (denot A s0).blks b = true)
    {t : Ty} {x : Nat}
    (hu : useOK (domTable B) (defPositions B (t, x)) b i = true) :
    GoodB A B s0 t x := by
  intro d j hd
  left
  rcases useOK_dom hu d j hd with rfl | hdom
  · exact hactive
  · rw [← show domOf A b = domOf B b by unfold domOf; rw [htab]] at hdom
    have := active_dom_closed hwfA hdcA
      (mem_activeList.mpr ⟨hblt, hactive⟩) hdom
    exact (mem_activeList.mp this).2

theorem good_of_arm {A B : Program} {s0 : State}
    (hwfA : WellFormed A) (hdcA : domClosedOK A = true)
    (htab : domTable A = domTable B) {p : Nat}
    (hplt : p < A.blocks.length) (hactive : (denot A s0).blks p = true)
    {t : Ty} {x : Nat}
    (hu : armUseOK (domTable B) (defPositions B (t, x)) p = true) :
    GoodB A B s0 t x := by
  intro d j hd
  left
  have hdom := armUseOK_dom hu d j hd
  rw [← show domOf A p = domOf B p by unfold domOf; rw [htab]] at hdom
  have := active_dom_closed hwfA hdcA
    (mem_activeList.mpr ⟨hplt, hactive⟩) hdom
  exact (mem_activeList.mp this).2

theorem hasHavoc_exists {P : Program} {t : Ty} {x : Nat}
    (h : hasHavoc P t x = true) :
    ∃ (d : Nat) (Bd : Block) (j : Nat), P.block? d = some Bd
      ∧ Bd.cmds[j]? = some (Cmd.havoc t x) := by
  unfold hasHavoc at h
  obtain ⟨Bd, hBdmem, hin⟩ := List.any_eq_true.mp h
  obtain ⟨c, hcmem, hc⟩ := List.any_eq_true.mp hin
  obtain ⟨d, hBd⟩ := List.mem_iff_getElem?.mp hBdmem
  obtain ⟨j, hcj⟩ := List.mem_iff_getElem?.mp hcmem
  cases c with
  | havoc t' x' =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      exact ⟨d, Bd, j, hBd, hcj⟩
  | assign t' x' e => cases hc
  | phi t' x' arms => cases hc
  | assume φ => cases hc
  | assert r => cases hc

/-- A non-havoc definition in an A-inactive block spoils goodness — the
scoping that makes junk writes harmless. -/
theorem not_goodB_of_inactive_def {A B : Program} {s0 : State}
    {b i : Nat} {Bb : Block} {c : Cmd}
    (hBb : B.block? b = some Bb) (hci : Bb.cmds[i]? = some c)
    {t : Ty} {x : Nat} (hdef : c.def? = some (t, x))
    (hnothavoc : c ≠ .havoc t x)
    (hinactive : (denot A s0).blks b = false) : ¬GoodB A B s0 t x := by
  intro hg
  rcases hg b i ⟨Bb, c, hBb, hci, hdef⟩ with hact | ⟨Bd, hBd, hcj⟩
  · rw [hinactive] at hact
    cases hact
  · obtain rfl : Bb = Bd := Option.some.inj (hBb.symm.trans hBd)
    exact hnothavoc (Option.some.inj (hci.symm.trans hcj))

/-- B-copy emissions write only `pv 1` registers or their own CHK slot. -/
theorem prodCmdB_def_target {A : Program} {Ba : Block} {stride b i : Nat}
    {c c' : Cmd} (hc' : c' ∈ prodCmdB A Ba stride b i c)
    {t : Ty} {w : Nat} (hdef : c'.def? = some (t, w)) :
    (∃ x, w = pv 1 x) ∨ w = chkReg stride b i := by
  cases c with
  | assume φ =>
      simp only [prodCmdB] at hc'
      rcases List.mem_cons.mp hc' with rfl | h
      · cases hdef; exact Or.inr rfl
      · rcases List.mem_singleton.mp h with rfl; cases hdef
  | assert cB' =>
      simp only [prodCmdB] at hc'
      rcases List.mem_cons.mp hc' with rfl | h
      · cases hdef; exact Or.inr rfl
      · rcases List.mem_singleton.mp h with rfl; cases hdef
  | havoc t' x =>
      simp only [prodCmdB] at hc'
      split at hc' <;> rcases List.mem_singleton.mp hc' with rfl
      · cases hdef; exact Or.inl ⟨x, rfl⟩
      · cases hdef; exact Or.inl ⟨x, rfl⟩
  | assign t' x e =>
      simp only [prodCmdB, List.mem_singleton] at hc'
      subst hc'
      cases hdef
      exact Or.inl ⟨x, rfl⟩
  | phi t' x arms =>
      simp only [prodCmdB, List.mem_singleton] at hc'
      subst hc'
      cases hdef
      exact Or.inl ⟨x, rfl⟩

/-- zipIdx carries strictly increasing indices. -/
theorem zipIdx_pairwise {α : Type _} :
    ∀ (l : List α) (k : Nat),
      List.Pairwise (fun (a b : α × Nat) => a.2 < b.2) (l.zipIdx k)
  | [], _ => List.Pairwise.nil
  | x :: l, k => by
      rw [List.zipIdx_cons]
      refine List.pairwise_cons.mpr ⟨fun ci hci => ?_, zipIdx_pairwise l (k + 1)⟩
      have := List.mem_zipIdx hci
      omega

/-! ## The B-copy segment -/

/-- What a CHK slot holds after its block is processed, when the block
is A-active: the B-side semantic value of the checked fact. -/
def DepositAt (A B : Program) (s0 : State) (Ba : Block) (stride b : Nat)
    (R' : State) : Cmd × Nat → Prop
  | (.assume φ, i) => (denot A s0).blks b = true →
      R'.regs .bool (chkReg stride b i) = φ.eval (denot B s0)
  | (.assert c', i) => (denot A s0).blks b = true →
      ∀ cA, Ba.assertReg? = some cA →
        R'.regs .bool (chkReg stride b i)
          = ((denot A s0).regs .bool cA == (denot B s0).regs .bool c')
  | _ => True

/-- One B-side command's emission: invariants are preserved (Good
writes are self-writes, junk writes land on non-Good registers, CHK
writes land outside both halves), and the command's own deposit is
made. -/
theorem prodCmdB_step {A B : Program} {s0 : State}
    (hwfA : WellFormed A) (hwfB : WellFormed B)
    (hcovB : phiCoversOK B = true) (hdcA : domClosedOK A = true)
    (htab : domTable A = domTable B) (hpreds : predsOf A = predsOf B)
    (hentry : A.entry = B.entry)
    {b : Nat} {Ba Bb : Block}
    (hBa : A.block? b = some Ba) (hBb : B.block? b = some Bb)
    (hxfer : ∀ p, p < b → (denot A s0).blks p = true →
      (denot B s0).blks p = true)
    {c : Cmd} {i : Nat} (hci : Bb.cmds[i]? = some c)
    {R : State} (hA : HalfA A s0 R) (hB : HalfB A B s0 R)
    (hblks : ∀ p, p < b → R.blks p = (denot A s0).blks p) :
    ∀ R', R' = (prodCmdB A Ba (chkStride B.blocks) b i c).foldl
        (denotCmd (product A B)) R →
      HalfA A s0 R' ∧ HalfB A B s0 R' ∧ R'.blks = R.blks
        ∧ DepositAt A B s0 Ba (chkStride B.blocks) b R' (c, i) := by
  intro R' hR'
  have hblt : b < A.blocks.length := (List.getElem?_eq_some_iff.mp hBa).1
  have hcmem : c ∈ Bb.cmds := List.mem_of_getElem? hci
  have husec := usesOK_cmd hwfB.uses hBb hci
  cases c with
  | assume φ =>
      -- CHK deposit: `chk := φ₁; assert chk`
      simp only [prodCmdB] at hR'
      have hR'' : R' = R.upd .bool (chkReg (chkStride B.blocks) b i)
          ((φ.rename (pv 1)).eval R) := hR'
      subst hR''
      refine ⟨fun t x => ?_, fun t x hg => ?_, rfl, fun hactive => ?_⟩
      · rw [State.upd_regs_of_ne R
          (pv_chk_pair_ne (j := 0) (by omega) (by omega) x _ _ _)]
        exact hA t x
      · rw [State.upd_regs_of_ne R
          (pv_chk_pair_ne (j := 1) (by omega) (by omega) x _ _ _)]
        exact hB t x hg
      · show (R.upd .bool _ _).regs .bool _ = _
        rw [State.upd_regs_self]
        simp only [cmdUsesOK] at husec
        have hgfc := guardFree_at hwfB.gf (List.mem_of_getElem? hBb) hcmem
        simp only [cmdGuardFree, List.isEmpty_iff] at hgfc
        rw [Exp.eval_rename]
        exact eval_congr φ
          (fun p hp => hB p.1 p.2 (good_of_use hwfA hdcA htab hblt hactive
            (List.all_eq_true.mp husec p hp)))
          (fun q hq => by rw [hgfc] at hq; cases hq)
  | assert cB' =>
      simp only [prodCmdB] at hR'
      cases hreg : Ba.assertReg? with
      | none =>
          rw [hreg] at hR'
          have hR'' : R' = R.upd .bool (chkReg (chkStride B.blocks) b i)
              ((Exp.var .bool (pv 1 cB')).eval R) := hR'
          subst hR''
          refine ⟨fun t x => ?_, fun t x hg => ?_, rfl, fun _ cA hcA => ?_⟩
          · rw [State.upd_regs_of_ne R
              (pv_chk_pair_ne (j := 0) (by omega) (by omega) x _ _ _)]
            exact hA t x
          · rw [State.upd_regs_of_ne R
              (pv_chk_pair_ne (j := 1) (by omega) (by omega) x _ _ _)]
            exact hB t x hg
          · rw [hreg] at hcA
            cases hcA
      | some cA =>
          rw [hreg] at hR'
          have hR'' : R' = R.upd .bool (chkReg (chkStride B.blocks) b i)
              ((Exp.eqB (.var .bool (pv 0 cA)) (.var .bool (pv 1 cB'))).eval R)
            := hR'
          subst hR''
          refine ⟨fun t x => ?_, fun t x hg => ?_, rfl,
            fun hactive cA' hcA' => ?_⟩
          · rw [State.upd_regs_of_ne R
              (pv_chk_pair_ne (j := 0) (by omega) (by omega) x _ _ _)]
            exact hA t x
          · rw [State.upd_regs_of_ne R
              (pv_chk_pair_ne (j := 1) (by omega) (by omega) x _ _ _)]
            exact hB t x hg
          · obtain rfl : cA = cA' := Option.some.inj (hreg.symm.trans hcA')
            show (R.upd .bool _ _).regs .bool _ = _
            rw [State.upd_regs_self]
            show (R.regs .bool (pv 0 cA) == R.regs .bool (pv 1 cB')) = _
            simp only [cmdUsesOK] at husec
            rw [hA .bool cA, hB .bool cB'
              (good_of_use hwfA hdcA htab hblt hactive husec)]
  | havoc t' x =>
      simp only [prodCmdB] at hR'
      split at hR'
      · -- paired havoc: the input equate is a self-write
        rename_i hhav
        have hgood : GoodB A B s0 t' x := fun d j hd => by
          right
          obtain ⟨rfl, rfl⟩ := ssa_unique hwfB.ssa ⟨Bb, _, hBb, hci, rfl⟩ hd
          exact ⟨Bb, hBb, hci⟩
        obtain ⟨dA, BdA, jA, hBdA, hcjA⟩ := hasHavoc_exists hhav
        have hval : R.regs t' (pv 0 x) = (denot B s0).regs t' x := by
          rw [hA t' x, denot_regs_of_havoc_def hwfA.ssa hBdA hcjA,
            ← denot_regs_of_havoc_def hwfB.ssa hBb hci]
        have hR'' : R' = R.upd t' (pv 1 x) (R.regs t' (pv 0 x)) := hR'
        subst hR''
        rw [hval, ← hB t' x hgood, State.upd_self]
        exact ⟨hA, hB, rfl, trivial⟩
      · -- unpaired havoc: identity
        have hR'' : R' = R := hR'
        subst hR''
        exact ⟨hA, hB, rfl, trivial⟩
  | assign t' x e =>
      simp only [prodCmdB, Cmd.rename] at hR'
      have hR'' : R' = R.upd t' (pv 1 x) ((e.rename (pv 1)).eval R) := hR'
      subst hR''
      rcases Bool.eq_false_or_eq_true ((denot A s0).blks b) with hactive | hinact
      · -- A-active: a Good self-write
        have hgood : GoodB A B s0 t' x := fun d j hd => by
          left
          obtain ⟨rfl, rfl⟩ := ssa_unique hwfB.ssa ⟨Bb, _, hBb, hci, rfl⟩ hd
          exact hactive
        simp only [cmdUsesOK] at husec
        have hgfc := guardFree_at hwfB.gf (List.mem_of_getElem? hBb) hcmem
        simp only [cmdGuardFree, List.isEmpty_iff] at hgfc
        have hval : (e.rename (pv 1)).eval R = R.regs t' (pv 1 x) := by
          rw [Exp.eval_rename,
            eval_congr e (fun p hp => hB p.1 p.2
              (good_of_use hwfA hdcA htab hblt hactive
                (List.all_eq_true.mp husec p hp)))
              (fun q hq => by rw [hgfc] at hq; cases hq),
            ← denot_assign hwfB hBb hci, ← hB t' x hgood]
        rw [hval, State.upd_self]
        exact ⟨hA, hB, rfl, trivial⟩
      · -- A-inactive: junk write onto a non-Good register
        have hng := not_goodB_of_inactive_def (A := A) (s0 := s0) hBb hci rfl
          (by intro h; cases h) hinact
        refine ⟨fun t x' => ?_, fun t x' hg => ?_, rfl, trivial⟩
        · rw [State.upd_regs_of_ne R
            (pv_pair_ne (j := 0) (j' := 1) (by omega) (by omega)
              (by omega) x' x)]
          exact hA t x'
        · have hne : ((t, pv 1 x') : Ty × Nat) ≠ (t', pv 1 x) := by
            intro heq
            obtain ⟨rfl, hx⟩ := Prod.mk.injEq .. |>.mp heq
            obtain rfl : x' = x := ((pv_eq_iff (by omega) (by omega)).mp hx).2
            exact hng hg
          rw [State.upd_regs_of_ne R hne]
          exact hB t x' hg
  | phi t' x arms =>
      simp only [prodCmdB, Cmd.rename] at hR'
      have hR'' : R' = R.upd t' (pv 1 x)
          ((Vc.phiRhs (product A B) t'
            (arms.map fun a => (a.1, pv 1 a.2))).eval R) := hR'
      subst hR''
      rcases Bool.eq_false_or_eq_true ((denot A s0).blks b) with hactive | hinact
      · -- A-active: the selection argument — both sides pick the taken
        -- predecessor's arm, and its source is Good
        have hgood : GoodB A B s0 t' x := fun d j hd => by
          left
          obtain ⟨rfl, rfl⟩ := ssa_unique hwfB.ssa ⟨Bb, _, hBb, hci, rfl⟩ hd
          exact hactive
        have harms := phiOK_at hwfB.phi hBb hcmem
        have hbne : b ≠ A.entry := by
          intro heq
          exact no_phi_in_entry hwfB.phi hwfB.entry
            (by rw [← hentry, ← heq]; exact hBb) hcmem
        obtain ⟨p, hpact, hplt, hpE⟩ :=
          denot_active_pred hwfA.fwd hwfA.uses hBa hactive hbne
        have hpA : p ∈ activeList A s0 := mem_activeList.mpr ⟨by omega, hpact⟩
        have hppredA : p ∈ predsOf A b := by
          obtain ⟨cond, hcm, -⟩ := hpE.edge_cond
          exact mem_predsOf.mpr ⟨cond, hcm⟩
        have hppredB : p ∈ predsOf B b := by rw [← hpreds]; exact hppredA
        have hpm := phiCovers_at hcovB hBb hcmem hppredB
        obtain ⟨⟨p', src⟩, hmem', hfst⟩ := List.mem_map.mp hpm
        have hmem : (p, src) ∈ arms := by
          have hp' : p' = p := hfst
          rw [← hp']
          exact hmem'
        have hnd : (arms.map (·.1)).Nodup := by
          simp only [phiArmsOK, Bool.and_eq_true] at harms
          exact of_decide_eq_true harms.1.2
        have hlk := lookup_of_mem_nodup hmem hnd
        -- every non-taken arm's guard is false over A's guards
        have hgq_data : ∀ q s', (q, s') ∈ arms → q ≠ p →
            q ≠ A.entry ∧ q < b ∧ (denot A s0).blks q = false := by
          intro q s' hqarm hqne
          have hqpredB := phiArm_pred harms hqarm
          have hqpredA : q ∈ predsOf A b := by rw [hpreds]; exact hqpredB
          have hqlt : q < b := pred_lt hwfA.fwd hqpredA
          have hqinact : (denot A s0).blks q = false := by
            rcases Bool.eq_false_or_eq_true ((denot A s0).blks q)
              with hq | hq
            · exact absurd (active_pred_unique hwfA hblt hpA hppredA
                (mem_activeList.mpr ⟨by omega, hq⟩) hqpredA) hqne
            · exact hq
          refine ⟨fun hqe => ?_, hqlt, hqinact⟩
          obtain ⟨hentA, -⟩ := denot_hentry hwfA.fwd hwfA.uses hpA
          rw [hqe] at hqinact
          rw [(mem_activeList.mp hentA).2] at hqinact
          cases hqinact
        -- the source register is Good (arm uses are dominated at p)
        simp only [cmdUsesOK] at husec
        have hsrcGood : GoodB A B s0 t' src := by
          have := List.all_eq_true.mp husec (p, src) hmem
          exact good_of_arm hwfA hdcA htab (by omega) hpact this
        -- the product side selects src over A's guards
        cases arms with
        | nil => cases hmem
        | cons a rest =>
            have hval : (Vc.phiRhs (product A B) t'
                ((a :: rest).map fun ar => (ar.1, pv 1 ar.2))).eval R
                = R.regs t' (pv 1 src) := by
              have h1 : (Vc.phiRhs (product A B) t'
                  ((a :: rest).map fun ar => (ar.1, pv 1 ar.2))).eval R
                  = (Vc.phiChain B t' a rest).eval (R.reindex (pv 1)) := by
                rw [List.map_cons]
                exact phiChain_rename_eval (P := B) (Q := product A B)
                  (show (product A B).entry = B.entry by
                    rw [product_entry]; exact hentry) (pv 1) R a rest
              rw [h1]
              refine phiChain_eval_select a rest hlk ?_ ?_
              · unfold Vc.guardOf
                split
                · rfl
                · show R.blks p = true
                  rw [hblks p (by omega)]
                  exact hpact
              · intro q s' hqarm hqne
                obtain ⟨hqentry, hqlt, hqinact⟩ := hgq_data q s' hqarm hqne
                unfold Vc.guardOf
                rw [if_neg (by rw [← hentry]; exact hqentry)]
                show R.blks q = false
                rw [hblks q hqlt]
                exact hqinact
            -- B's own run selects the same arm
            have hown : (denot B s0).regs t' x = (denot B s0).regs t' src := by
              rw [denot_phi hwfB hBb hcmem]
              refine phiChain_eval_select a rest hlk ?_ ?_
              · unfold Vc.guardOf
                split
                · rfl
                · show (denot B s0).blks p = true
                  exact hxfer p (by omega) hpact
              · intro q s' hqarm hqne
                obtain ⟨hqentry, hqlt, hqinact⟩ := hgq_data q s' hqarm hqne
                unfold Vc.guardOf
                rw [if_neg (by rw [← hentry]; exact hqentry)]
                show (denot B s0).blks q = false
                have hbltB : b < B.blocks.length :=
                  (List.getElem?_eq_some_iff.mp hBb).1
                rcases Bool.eq_false_or_eq_true ((denot B s0).blks q)
                  with hq | hq
                · -- q B-active would violate B's at-most-one active pred
                  have hpB : p ∈ activeList B s0 := mem_activeList.mpr
                    ⟨by omega, hxfer p (by omega) hpact⟩
                  have hqB : q ∈ activeList B s0 := mem_activeList.mpr
                    ⟨by omega, hq⟩
                  have hqpredB := phiArm_pred harms hqarm
                  exact absurd (active_pred_unique hwfB hbltB hpB hppredB hqB
                    hqpredB) hqne
                · exact hq
            rw [hval, hB t' src hsrcGood, ← hown, ← hB t' x hgood,
              State.upd_self]
            exact ⟨hA, hB, rfl, trivial⟩
      · -- A-inactive: junk write onto a non-Good register
        have hng := not_goodB_of_inactive_def (A := A) (s0 := s0) hBb hci rfl
          (by intro h; cases h) hinact
        refine ⟨fun t x' => ?_, fun t x' hg => ?_, rfl, trivial⟩
        · rw [State.upd_regs_of_ne R
            (pv_pair_ne (j := 0) (j' := 1) (by omega) (by omega)
              (by omega) x' x)]
          exact hA t x'
        · have hne : ((t, pv 1 x') : Ty × Nat) ≠ (t', pv 1 x) := by
            intro heq
            obtain ⟨rfl, hx⟩ := Prod.mk.injEq .. |>.mp heq
            obtain rfl : x' = x := ((pv_eq_iff (by omega) (by omega)).mp hx).2
            exact hng hg
          rw [State.upd_regs_of_ne R hne]
          exact hB t x' hg

/-- Deposits only mention their own CHK slot. -/
theorem depositAt_congr {A B : Program} {s0 : State} {Ba : Block}
    {stride b : Nat} {R₁ R' : State} (ci : Cmd × Nat)
    (h : R'.regs .bool (chkReg stride b ci.2)
      = R₁.regs .bool (chkReg stride b ci.2))
    (hd : DepositAt A B s0 Ba stride b R₁ ci) :
    DepositAt A B s0 Ba stride b R' ci := by
  obtain ⟨c, i⟩ := ci
  cases c with
  | assume φ => exact fun hact => by rw [h]; exact hd hact
  | assert c' => exact fun hact cA hcA => by rw [h]; exact hd hact cA hcA
  | assign t x e => trivial
  | havoc t x => trivial
  | phi t x arms => trivial

/-- The B-copy segment fold: invariants preserved, one deposit per
B-side command, deposits surviving the rest of the segment (later
emissions write only copy-1 registers or strictly later slots). -/
theorem prodCmdB_fold {A B : Program} {s0 : State}
    (hwfA : WellFormed A) (hwfB : WellFormed B)
    (hcovB : phiCoversOK B = true) (hdcA : domClosedOK A = true)
    (htab : domTable A = domTable B) (hpreds : predsOf A = predsOf B)
    (hentry : A.entry = B.entry)
    {b : Nat} {Ba Bb : Block}
    (hBa : A.block? b = some Ba) (hBb : B.block? b = some Bb)
    (hxfer : ∀ p, p < b → (denot A s0).blks p = true →
      (denot B s0).blks p = true) :
    ∀ (l : List (Cmd × Nat)),
      (∀ ci ∈ l, Bb.cmds[ci.2]? = some ci.1) →
      List.Pairwise (fun (ci cj : Cmd × Nat) => ci.2 < cj.2) l →
      ∀ (R : State), HalfA A s0 R → HalfB A B s0 R →
        (∀ p, p < b → R.blks p = (denot A s0).blks p) →
        ∀ R', R' = (l.flatMap fun ci =>
            prodCmdB A Ba (chkStride B.blocks) b ci.2 ci.1).foldl
              (denotCmd (product A B)) R →
          HalfA A s0 R' ∧ HalfB A B s0 R' ∧ R'.blks = R.blks
            ∧ ∀ ci ∈ l, DepositAt A B s0 Ba (chkStride B.blocks) b R' ci
  | [], _, _, R, hA, hB, hblks, R', hR' => by
      subst hR'
      exact ⟨hA, hB, rfl, fun ci hci => absurd hci List.not_mem_nil⟩
  | (c, i) :: l, hsub, hpw, R, hA, hB, hblks, R', hR' => by
      rw [List.flatMap_cons, List.foldl_append] at hR'
      obtain ⟨hA₁, hB₁, hblks₁, hdep₁⟩ := prodCmdB_step hwfA hwfB hcovB hdcA
        htab hpreds hentry hBa hBb hxfer (hsub _ (List.mem_cons_self ..))
        hA hB hblks _ rfl
      obtain ⟨hA', hB', hblks', hdep'⟩ := prodCmdB_fold hwfA hwfB hcovB hdcA
        htab hpreds hentry hBa hBb hxfer l
        (fun ci hci => hsub ci (List.mem_cons_of_mem _ hci))
        (List.pairwise_cons.mp hpw).2 _ hA₁ hB₁
        (fun p hp => by rw [hblks₁]; exact hblks p hp) R' hR'
      have hilt : i < Bb.cmds.length :=
        (List.getElem?_eq_some_iff.mp (hsub _ (List.mem_cons_self ..))).1
      have histride : i < chkStride B.blocks :=
        Nat.lt_trans hilt (lt_chkStride hBb)
      have hnt : R'.regs .bool (chkReg (chkStride B.blocks) b i)
          = ((prodCmdB A Ba (chkStride B.blocks) b i c).foldl
              (denotCmd (product A B)) R).regs .bool
                (chkReg (chkStride B.blocks) b i) := by
        rw [hR']
        refine cmdsFold_regs_ne (fun c' hc' tx htx => ?_)
        obtain ⟨ci', hci'mem, hc'in⟩ := List.mem_flatMap.mp hc'
        obtain ⟨t', w⟩ := tx
        rcases prodCmdB_def_target hc'in htx with ⟨x, rfl⟩ | rfl
        · exact pv_chk_pair_ne (by omega) (by omega) x _ _ _
        · intro heq
          have hsnd := congrArg Prod.snd heq
          have hi'lt : ci'.2 < Bb.cmds.length :=
            (List.getElem?_eq_some_iff.mp
              (hsub ci' (List.mem_cons_of_mem _ hci'mem))).1
          have hi'stride : ci'.2 < chkStride B.blocks :=
            Nat.lt_trans hi'lt (lt_chkStride hBb)
          have := (chkReg_inj hi'stride histride hsnd).2
          have hlt := (List.pairwise_cons.mp hpw).1 ci' hci'mem
          omega
      refine ⟨hA', hB', by rw [hblks', hblks₁], fun ci hci => ?_⟩
      rcases List.mem_cons.mp hci with rfl | hci'
      · exact depositAt_congr (c, i) hnt hdep₁
      · exact hdep' ci hci'

/-- The branch CHK's deposit and preservation. -/
theorem prodTermChk_fold {A B : Program} {s0 : State}
    (hwfA : WellFormed A) (hwfB : WellFormed B) (hdcA : domClosedOK A = true)
    (htab : domTable A = domTable B)
    {b : Nat} {Ba Bb : Block}
    (hBa : A.block? b = some Ba) (hBb : B.block? b = some Bb)
    {R : State} (hA : HalfA A s0 R) (hB : HalfB A B s0 R) :
    ∀ R', R' = (prodTermChk (chkStride B.blocks) b Ba Bb).foldl
        (denotCmd (product A B)) R →
      HalfA A s0 R' ∧ HalfB A B s0 R' ∧ R'.blks = R.blks
        ∧ (∀ i, i < Bb.cmds.length →
            R'.regs .bool (chkReg (chkStride B.blocks) b i)
              = R.regs .bool (chkReg (chkStride B.blocks) b i))
        ∧ ((denot A s0).blks b = true →
            ∀ cA tA eA cB tB eB, Ba.term = .ifGoto cA tA eA →
              Bb.term = .ifGoto cB tB eB →
              R'.regs .bool (chkReg (chkStride B.blocks) b Bb.cmds.length)
                = ((denot A s0).regs .bool cA
                    == (denot B s0).regs .bool cB)) := by
  intro R' hR'
  have hblt : b < A.blocks.length := (List.getElem?_eq_some_iff.mp hBa).1
  unfold prodTermChk at hR'
  cases hta : Ba.term with
  | ifGoto cA tA eA =>
      cases htb : Bb.term with
      | ifGoto cB tB eB =>
          rw [hta, htb] at hR'
          have hR'' : R' = R.upd .bool
              (chkReg (chkStride B.blocks) b Bb.cmds.length)
              ((Exp.eqB (.var .bool (pv 0 cA))
                (.var .bool (pv 1 cB))).eval R) := hR'
          subst hR''
          refine ⟨fun t x => ?_, fun t x hg => ?_, rfl,
            fun i hi => ?_, fun hactive cA' tA' eA' cB' tB' eB' hta' htb' => ?_⟩
          · rw [State.upd_regs_of_ne R
              (pv_chk_pair_ne (j := 0) (by omega) (by omega) x _ _ _)]
            exact hA t x
          · rw [State.upd_regs_of_ne R
              (pv_chk_pair_ne (j := 1) (by omega) (by omega) x _ _ _)]
            exact hB t x hg
          · rw [State.upd_regs_of_ne R (fun heq => ?_)]
            have hsnd := congrArg Prod.snd heq
            have hstride := lt_chkStride hBb
            have := (chkReg_inj (by omega) (by omega) hsnd).2
            omega
          · obtain ⟨rfl, rfl, rfl⟩ := Terminator.ifGoto.inj hta'
            obtain ⟨rfl, rfl, rfl⟩ := Terminator.ifGoto.inj htb' 
            show (R.upd .bool _ _).regs .bool _ = _
            rw [State.upd_regs_self]
            show (R.regs .bool (pv 0 cA) == R.regs .bool (pv 1 cB)) = _
            have hterm_use := usesOK_term hwfB.uses hBb
            simp only [termUsesOK, htb] at hterm_use
            rw [hA .bool cA, hB .bool cB
              (good_of_use hwfA hdcA htab hblt hactive hterm_use)]
      | halt =>
          rw [hta, htb] at hR'
          subst hR'
          exact ⟨hA, hB, rfl, fun i hi => rfl,
            fun _ _ _ _ _ _ _ _ htb' => by cases htb'⟩
      | goto tB =>
          rw [hta, htb] at hR'
          subst hR'
          exact ⟨hA, hB, rfl, fun i hi => rfl,
            fun _ _ _ _ _ _ _ _ htb' => by cases htb'⟩
  | halt =>
      rw [hta] at hR'
      subst hR'
      exact ⟨hA, hB, rfl, fun i hi => rfl,
        fun _ _ _ _ _ _ _ hta' => by cases hta'⟩
  | goto tA =>
      rw [hta] at hR'
      subst hR'
      exact ⟨hA, hB, rfl, fun i hi => rfl,
        fun _ _ _ _ _ _ _ hta' => by cases hta'⟩

/-- One product block, end to end: invariants advance one block, the
guard lands on A's, and every CHK slot of the block carries its B-side
semantic value (when the block is A-active). -/
theorem prodBlock_run {A B : Program} {s0 : State}
    (hwfA : WellFormed A) (hwfB : WellFormed B)
    (hcovB : phiCoversOK B = true) (hdcA : domClosedOK A = true)
    (htab : domTable A = domTable B) (hpreds : predsOf A = predsOf B)
    (hlen : A.blocks.length = B.blocks.length) (hentry : A.entry = B.entry)
    {b : Nat} {Ba Bb : Block}
    (hBa : A.block? b = some Ba) (hBb : B.block? b = some Bb)
    (hxfer : ∀ p, p < b → (denot A s0).blks p = true →
      (denot B s0).blks p = true)
    {R : State} (hA : HalfA A s0 R) (hB : HalfB A B s0 R)
    (hblks : ∀ p, p < b → R.blks p = (denot A s0).blks p) :
    ∀ R', R' = denotBlock (product A B) R b →
      HalfA A s0 R' ∧ HalfB A B s0 R'
        ∧ (∀ p, p < b + 1 → R'.blks p = (denot A s0).blks p)
        ∧ (∀ ci : Cmd × Nat, Bb.cmds[ci.2]? = some ci.1 →
            DepositAt A B s0 Ba (chkStride B.blocks) b R' ci)
        ∧ ((denot A s0).blks b = true →
            ∀ cA tA eA cB tB eB, Ba.term = .ifGoto cA tA eA →
              Bb.term = .ifGoto cB tB eB →
              R'.regs .bool (chkReg (chkStride B.blocks) b Bb.cmds.length)
                = ((denot A s0).regs .bool cA
                    == (denot B s0).regs .bool cB)) := by
  intro R' hR'
  unfold denotBlock at hR'
  rw [product_block? hlen hBa hBb] at hR'
  set R₂ := (Bb.cmds.zipIdx.flatMap fun ci =>
    prodCmdB A Ba (chkStride B.blocks) b ci.2 ci.1).foldl
    (denotCmd (product A B)) R with hR₂
  set Wc := (prodBlock A (chkStride B.blocks) b Ba Bb).cmds.foldl
    (denotCmd (product A B)) R with hWc
  have hfoldA : (Ba.cmds.flatMap prodCmdA).foldl
      (denotCmd (product A B)) R = R :=
    prodCmdA_fold hwfA hBa Ba.cmds (fun c hc => hc) R hA hblks
  -- decompose the block fold into the three segments
  have hsplit : Wc = (prodTermChk (chkStride B.blocks) b Ba Bb).foldl
      (denotCmd (product A B)) R₂ := by
    rw [hWc, hR₂]
    show ((Ba.cmds.flatMap prodCmdA
      ++ Bb.cmds.zipIdx.flatMap (fun ci =>
          prodCmdB A Ba (chkStride B.blocks) b ci.2 ci.1)
      ++ prodTermChk (chkStride B.blocks) b Ba Bb).foldl
        (denotCmd (product A B)) R) = _
    rw [List.foldl_append, List.foldl_append, hfoldA]
  obtain ⟨hA₂, hB₂, hblks₂, hdeps⟩ := prodCmdB_fold hwfA hwfB hcovB hdcA
    htab hpreds hentry hBa hBb hxfer Bb.cmds.zipIdx
    (fun ci hci => List.mem_zipIdx_iff_getElem?.mp hci)
    (zipIdx_pairwise Bb.cmds 0) R hA hB hblks R₂ hR₂
  obtain ⟨hA₃, hB₃, hblks₃, hkeep, hbranch⟩ := prodTermChk_fold hwfA hwfB
    hdcA htab hBa hBb hA₂ hB₂ Wc hsplit
  have hR2 : R' = { regs := Wc.regs, blks := Function.update Wc.blks b (reach (product A B) Wc b && assumesOK Wc (prodBlock A (chkStride B.blocks) b Ba Bb)) } := hR'
  subst hR2
  have hWcblks : ∀ p, p < b → Wc.blks p = (denot A s0).blks p := by
    intro p hp
    rw [hblks₃, hblks₂]
    exact hblks p hp
  have hguard : (reach (product A B) Wc b
      && assumesOK Wc (prodBlock A (chkStride B.blocks) b Ba Bb))
      = (denot A s0).blks b := by
    rw [reach_product hwfA.fwd hlen hA₃ hWcblks,
      assumesOK_prodBlock hwfA.gf hBa hA₃]
    exact (denot_blks_final_char hwfA hBa).symm
  refine ⟨hA₃, hB₃, fun p hp => ?_, fun ci hci => ?_, hbranch⟩
  · show Function.update Wc.blks b _ p = _
    by_cases hpb : p = b
    · subst hpb
      rw [Function.update_self]
      exact hguard
    · rw [Function.update_of_ne hpb]
      exact hWcblks p (by omega)
  · -- deposits: made in the B segment, preserved by the terminator CHK
    have hilen : ci.2 < Bb.cmds.length :=
      (List.getElem?_eq_some_iff.mp hci).1
    refine depositAt_congr ci (hkeep ci.2 hilen) ?_
    exact hdeps ci (List.mem_zipIdx_iff_getElem?.mpr hci)

/-- The semantic content of an A-active block's CHKs, fully
extracted: B's assumes hold at B's final state, the branch registers
agree, and the assert predicates agree. State-free — facts about the
two final states only. -/
abbrev ChkFacts (A B : Program) (s0 : State) (b : Nat) : Prop :=
  (denot A s0).blks b = true →
    ∀ Ba Bb, A.block? b = some Ba → B.block? b = some Bb →
      assumesOK (denot B s0) Bb = true
      ∧ (∀ cA tA eA cB tB eB, Ba.term = .ifGoto cA tA eA →
          Bb.term = .ifGoto cB tB eB →
          (denot A s0).regs .bool cA = (denot B s0).regs .bool cB)
      ∧ (∀ (iB cB' cA' : Nat), Bb.cmds[iB]? = some (Cmd.assert cB') →
          Ba.assertReg? = some cA' →
          (denot A s0).regs .bool cA' = (denot B s0).regs .bool cB')

theorem product_final_blks {A B : Program} {σ : State}
    (hlen : A.blocks.length = B.blocks.length) {b : Nat}
    (hblt : b < A.blocks.length) :
    (denot (product A B) σ).blks b
      = (prefixState (product A B) σ (b + 1)).blks b := by
  rw [denot_blks_lt (by rw [product_length hlen]; omega),
    prefixState_blks_stable (Nat.lt_succ_self b)
      (by rw [product_length hlen]; omega)]

/-- Extract one CHK's truth from product safety: locate the assert in
the block, transport the slot to the final state, apply `hP`. -/
theorem chk_extract {A B : Program} {σ : State}
    (hP : Safe_denot (product A B))
    (hlen : A.blocks.length = B.blocks.length) {b i : Nat} {Ba Bb : Block}
    (hBa : A.block? b = some Ba) (hBb : B.block? b = some Bb)
    (hi : i < chkStride B.blocks)
    (hassert : Cmd.assert (chkReg (chkStride B.blocks) b i)
      ∈ (prodBlock A (chkStride B.blocks) b Ba Bb).cmds)
    (hblkA : (prefixState (product A B) σ (b + 1)).blks b = true) :
    (prefixState (product A B) σ (b + 1)).regs .bool
      (chkReg (chkStride B.blocks) b i) = true := by
  have hblt : b < A.blocks.length := (List.getElem?_eq_some_iff.mp hBa).1
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hassert
  have hsite : (b, j, chkReg (chkStride B.blocks) b i)
      ∈ Vc.assertSites (product A B) :=
    mem_assertSites.mpr ⟨_, product_block? hlen hBa hBb, hj⟩
  have hfinal := safe_denot_site_true hP σ hsite
    (by rw [product_length hlen]; omega)
    (by rw [product_final_blks hlen hblt]; exact hblkA)
  rw [product_chk_stable hlen hi hblt] at hfinal
  exact hfinal

/-- The transfer invariant: after `k` blocks of the product fold from
the doubled seed, the copies mirror the two final states, the guards
are A's, A-activity transfers to B, and every A-active block's CHK
content is extracted. -/
theorem transfer_inv {A B : Program} {s0 : State}
    (hwfA : WellFormed A) (hwfB : WellFormed B)
    (hcovB : phiCoversOK B = true) (hdcA : domClosedOK A = true)
    (htab : domTable A = domTable B) (hpreds : predsOf A = predsOf B)
    (hlen : A.blocks.length = B.blocks.length) (hentry : A.entry = B.entry)
    (hterm : ∀ {k : Nat} {Ba Bb : Block}, A.block? k = some Ba →
      B.block? k = some Bb → termShapeOK Ba.term Bb.term = true)
    (hP : Safe_denot (product A B)) :
    ∀ k, k ≤ A.blocks.length →
      HalfA A s0 (prefixState (product A B) (prodSeed A B s0) k)
      ∧ HalfB A B s0 (prefixState (product A B) (prodSeed A B s0) k)
      ∧ (∀ b, b < k →
          (prefixState (product A B) (prodSeed A B s0) k).blks b
            = (denot A s0).blks b)
      ∧ (∀ b, b < k → (denot A s0).blks b = true →
          (denot B s0).blks b = true)
      ∧ (∀ b, b < k → ChkFacts A B s0 b)
  | 0, _ => ⟨prodSeed_halfA A B s0, prodSeed_halfB A B s0,
      fun b hb => absurd hb (Nat.not_lt_zero b),
      fun b hb => absurd hb (Nat.not_lt_zero b),
      fun b hb => absurd hb (Nat.not_lt_zero b)⟩
  | k + 1, hk1 => by
      obtain ⟨ihA, ihB, ihblks, ihxfer, ihchk⟩ :=
        transfer_inv hwfA hwfB hcovB hdcA htab hpreds hlen hentry hterm hP
          k (by omega)
      have hklt : k < A.blocks.length := by omega
      obtain ⟨Ba, Bb, hBa, hBb, hPB⟩ := product_block?_of_lt hlen hklt
      obtain ⟨hA', hB', hblks', hdeps, hbranch⟩ := prodBlock_run hwfA hwfB
        hcovB hdcA htab hpreds hlen hentry hBa hBb ihxfer ihA ihB ihblks
        _ (prefixState_succ (product A B) (prodSeed A B s0) k)
      -- ChkFacts at k, extracted from the deposits via hP
      have hchk_k : ChkFacts A B s0 k := fun hactive Ba' Bb' hBa' hBb' => by
        obtain rfl : Ba = Ba' := Option.some.inj (hBa.symm.trans hBa')
        obtain rfl : Bb = Bb' := Option.some.inj (hBb.symm.trans hBb')
        have hblkA : (prefixState (product A B) (prodSeed A B s0)
            (k + 1)).blks k = true := by
          rw [hblks' k (Nat.lt_succ_self k)]
          exact hactive
        refine ⟨?_, ?_, ?_⟩
        · -- B's assumes hold at B's final state
          unfold assumesOK
          rw [List.all_eq_true]
          intro c hc
          cases c with
          | assume φ =>
              obtain ⟨i, hci⟩ := List.mem_iff_getElem?.mp hc
              have hilen : i < Bb.cmds.length :=
                (List.getElem?_eq_some_iff.mp hci).1
              have histride : i < chkStride B.blocks :=
                Nat.lt_trans hilen (lt_chkStride hBb)
              have hdep := hdeps (Cmd.assume φ, i) hci hactive
              have hval := chk_extract hP hlen hBa hBb histride
                (chk_assume_mem hci).2 hblkA
              show φ.eval (denot B s0) = true
              rw [← hdep]
              exact hval
          | assign t x e => trivial
          | havoc t x => trivial
          | phi t x arms => trivial
          | assert r => trivial
        · -- branch registers agree
          intro cA tA eA cB tB eB hta htb
          have hlenstride : Bb.cmds.length < chkStride B.blocks :=
            lt_chkStride hBb
          have hdep := hbranch hactive cA tA eA cB tB eB hta htb
          have hval := chk_extract hP hlen hBa hBb hlenstride
            (chk_branch_mem hta htb).2 hblkA
          rw [hdep] at hval
          exact beq_iff_eq.mp hval
        · -- assert predicates agree
          intro iB cB' cA' hiB hreg
          have hilen : iB < Bb.cmds.length :=
            (List.getElem?_eq_some_iff.mp hiB).1
          have histride : iB < chkStride B.blocks :=
            Nat.lt_trans hilen (lt_chkStride hBb)
          have hdep := hdeps (Cmd.assert cB', iB) hiB hactive cA' hreg
          have hval := chk_extract hP hlen hBa hBb histride
            (chk_assert_mem hiB hreg).2 hblkA
          rw [hdep] at hval
          exact beq_iff_eq.mp hval
      -- guard transfer at k
      have hxfer_k : (denot A s0).blks k = true →
          (denot B s0).blks k = true := by
        intro hactive
        obtain ⟨hassumesB, hbranchfact, -⟩ := hchk_k hactive Ba Bb hBa hBb
        have hreachB : reach B (denot B s0) k = true := by
          unfold reach
          by_cases hke : k = B.entry
          · rw [Bool.or_eq_true]
            exact Or.inl (decide_eq_true hke)
          · rw [Bool.or_eq_true]
            refine Or.inr ?_
            have hkeA : k ≠ A.entry := by rw [hentry]; exact hke
            obtain ⟨p, hpact, hplt, hpE⟩ :=
              denot_active_pred hwfA.fwd hwfA.uses hBa hactive hkeA
            have hpB : (denot B s0).blks p = true := ihxfer p hplt hpact
            obtain ⟨BpA, hBpA, hshape⟩ := hpE
            have hpltB : p < B.blocks.length := by
              have := (List.getElem?_eq_some_iff.mp hBpA).1
              omega
            have hBpB : B.block? p = some B.blocks[p] :=
              List.getElem?_eq_getElem hpltB
            have hshapeOK := hterm hBpA hBpB
            have hEB : EdgeTaken B (denot B s0) p k := by
              refine ⟨B.blocks[p], hBpB, ?_⟩
              rcases hshape with hgoto | ⟨c, t, e, hif, harm⟩
              · left
                cases htb' : (B.blocks[p]).term <;>
                  rw [hgoto, htb'] at hshapeOK <;>
                  simp only [termShapeOK, decide_eq_true_eq] at hshapeOK
                · cases hshapeOK
                · rw [hshapeOK]
                · exact absurd hshapeOK (by simp)
              · right
                cases htb' : (B.blocks[p]).term <;>
                  rw [hif, htb'] at hshapeOK <;>
                  simp only [termShapeOK, Bool.and_eq_true,
                    decide_eq_true_eq] at hshapeOK
                · cases hshapeOK
                · cases hshapeOK
                · rename_i cB tB eB
                  obtain ⟨h1, h2⟩ := hshapeOK
                  subst h1
                  subst h2
                  have hpchk := ihchk p hplt hpact BpA B.blocks[p]
                    hBpA hBpB
                  have hcval := hpchk.2.1 c t e cB t e hif htb'
                  refine ⟨cB, t, e, rfl, ?_⟩
                  rcases harm with ⟨rfl, hc⟩ | ⟨rfl, hc⟩
                  · exact Or.inl ⟨rfl, by rw [← hcval]; exact hc⟩
                  · exact Or.inr ⟨rfl, by rw [← hcval]; exact hc⟩
            obtain ⟨cond, hcm, hcv⟩ := hEB.edge_cond
            refine List.any_eq_true.mpr ⟨(p, cond), hcm, ?_⟩
            rw [Bool.and_eq_true]
            exact ⟨hpB, hcv⟩
        rw [denot_blks_final_char hwfB hBb, Bool.and_eq_true]
        exact ⟨hreachB, hassumesB⟩
      refine ⟨hA', hB', hblks', fun b hb => ?_, fun b hb => ?_⟩
      · rcases Nat.lt_or_ge b k with hbk | hbk
        · exact ihxfer b hbk
        · obtain rfl : b = k := by omega
          exact hxfer_k
      · rcases Nat.lt_or_ge b k with hbk | hbk
        · exact ihchk b hbk
        · obtain rfl : b = k := by omega
          exact hchk_k

/-- Safety transfer — what the rw-eq certificate licenses: if every
CHK of the product holds on every seed and the rewrite `B` is safe,
the original `A` is safe.

The proof is the coadequacy seeding trick doubled: drive the product
with both programs' final fold states side by side (`prodSeed`), so
every copy write is a self-write; the fold induction (`transfer_inv`)
then reduces everything to guard agreement along A's active prefix,
with the CHKs supplying branch agreement, B-assume validity, and the
assert pairing exactly where the argument needs them. -/
theorem product_transfer {A B : Program}
    (hwfA : WellFormed A) (hwfB : WellFormed B)
    (hdcB : domClosedOK B = true) (hcovB : phiCoversOK B = true)
    (hls : lockstep A B = true)
    (hP : Safe_denot (product A B)) (hB : Safe_denot B) :
    Safe_denot A := by
  obtain ⟨hlen, hentry, hterm, hsites⟩ := lockstep_facts hls
  have hpreds : predsOf A = predsOf B := predsOf_eq hlen @hterm
  have htab : domTable A = domTable B := domTable_eq hlen hentry hpreds
  have hdcA : domClosedOK A = true :=
    domClosedOK_transfer htab hentry (allEdges_proj_eq hlen @hterm) hdcB
  intro s0
  rcases Bool.eq_false_or_eq_true ((denot A s0).blks A.blocks.length)
    with hexit | hsafe
  case inr => exact hsafe
  case inl =>
  exfalso
  have hexit' : ReachesExit A s0 := hexit
  obtain ⟨aB, iA, okA, BA, hsitesA, hBA, hcA, -⟩ :=
    singleAssert_shape hwfA.one
  obtain ⟨haBact, hokA⟩ := denot_fail hexit' aB iA okA hsitesA
  obtain ⟨aB', iB, okB, BB, hsitesB, hBB, hcB, -⟩ :=
    singleAssert_shape hwfB.one
  have haB' : aB = aB' := by
    rw [hsitesA, hsitesB] at hsites
    simpa using hsites
  subst haB'
  obtain ⟨-, -, -, hxfer, hchk⟩ := transfer_inv (s0 := s0) hwfA hwfB hcovB
    hdcA htab hpreds hlen hentry @hterm hP A.blocks.length (Nat.le_refl _)
  have haBlt : aB < A.blocks.length := (List.getElem?_eq_some_iff.mp hBA).1
  have haBactA : (denot A s0).blks aB = true := (mem_activeList.mp haBact).2
  have hreg : BA.assertReg? = some okA := by
    refine assertReg?_eq (List.mem_of_getElem? hcA) (fun r hr => ?_)
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hr
    have hmem := mem_assertSites.mpr ⟨BA, hBA, hj⟩
    rw [hsitesA, List.mem_singleton] at hmem
    exact congrArg (·.2.2) hmem
  obtain ⟨-, -, hassertpair⟩ := hchk aB haBlt haBactA BA BB hBA hBB
  have hokBval : (denot B s0).regs .bool okB = false := by
    rw [← hassertpair iB okB okA hcB hreg]
    exact hokA
  have haBltB : aB < B.blocks.length := (List.getElem?_eq_some_iff.mp hBB).1
  have hexitB : (denot B s0).blks B.blocks.length = true := by
    rw [denot_blks_exit]
    unfold reachExit
    rw [hsitesB]
    refine List.any_eq_true.mpr ⟨(aB, iB, okB), List.mem_singleton.mpr rfl, ?_⟩
    rw [Bool.and_eq_true]
    constructor
    · show (prefixState B s0 B.blocks.length).blks aB = true
      rw [← denot_blks_lt haBltB]
      exact hxfer aB haBlt haBactA
    · show (!(prefixState B s0 B.blocks.length).regs .bool okB) = true
      have hv : (prefixState B s0 B.blocks.length).regs .bool okB = false := by
        rw [← denot_regs]
        exact hokBval
      rw [hv]
      rfl
  exact Bool.false_ne_true ((hB s0).symm.trans hexitB)

/-- The operational form: under the full Bool checkers (including
dominance closure and phi coverage on both sides), a safe rewrite plus
a safe product yields operational safety of the original. -/
theorem product_transfer_safe {A B : Program}
    (hwfA : wellFormed A = true) (hwfB : wellFormed B = true)
    (hcovA : phiCoversOK A = true) (hcovB : phiCoversOK B = true)
    (hls : lockstep A B = true)
    (hP : Safe_denot (product A B)) (hB : B.Safe) : A.Safe := by
  obtain ⟨hwfA', -⟩ := wellFormed_iff.mp hwfA
  obtain ⟨hwfB', hdcB⟩ := wellFormed_iff.mp hwfB
  exact (safe_iff_safe_denot hwfA hcovA).mpr
    (product_transfer hwfA' hwfB' hdcB hcovB hls hP
      ((safe_iff_safe_denot hwfB hcovB).mp hB))

end Ttac
