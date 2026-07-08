# Ttac — Lean 4 library for Tiny TAC

The program-independent half of `ttac lean`: the deep embedding of
Tiny TAC with a small-step operational semantics. Generated projects
receive a copy of this library, so it must stay in sync with the
emitter in `src/ctac/ttac/lean/`.

The embedding is *sort-indexed and table-driven*: one `Ty`-indexed
register file and expression type (sorts `int`/`bool`/`map`),
operators as
signature-indexed denotation tables, and commands characterized by
effect tables (`Cmd.def?` write footprint, `Cmd.factB` established
fact). Adding an operator is a table row plus one automatic case in
the fold lemmas — evaluation, the variable collector, the congruence
lemma, and the proof layers never mention individual operators.

## Modules

- `Ttac/Ast.lean` — `Ty` and its denotation, the operator tables
  (`UnOp`/`BinOp`/`TernOp`), the `Ty`-indexed `Exp` (separate `Nat`
  register namespace per sort, so well-typedness holds by
  construction; smart constructors keep familiar operator spellings),
  `Cmd` with its effect tables, `Terminator`, `Block`, `Program`.
- `Ttac/State.lean` — one total register file over `(sort, index)` +
  the cast-free `upd` simp-lemma set.
- `Ttac/Eval.lean` — operator denotations + total evaluation. Division
  is `Int.ediv` (Euclidean, `x / 0 = 0`), matching SMT-LIB `div` and
  the reference interpreter; a `map` value is a total `Int → Int`.
- `Ttac/Vars.lean` — the `(sort, register)` variable inventory, the
  per-sort view, the guard collector, and the congruence lemma
  (evaluation depends only on an expression's variables) — one lemma,
  operator-independent.
- `Ttac/Semantics.lean` — `Config` and the small-step `Step` inductive
  predicate, one rule per command kind. Havoc is a constructor
  argument (nondeterminism); `assume false` is stuck (pruned,
  vacuously safe).
- `Ttac/Safety.lean` — `Steps` (`Relation.ReflTransGen`),
  `Program.Safe`/`Unsafe`. `Unsafe` mirrors "the VC is satisfiable".
- `Ttac/Vc.lean` — the VC (`Vc.VC`: boolean constraints + map
  definitions) and its expected generator for `ttac vc-check`: exact
  Lean mirrors of the Python encoder's constant folds (`mkImp`,
  `mkOr`, `amoClauses`, ...), the lowering mirror, phi right-hand
  sides, `Vc.Sat`/`Vc.Unsat`. Per-command constraints are table-driven
  via `Cmd.factB` (`factConstraints`); phi equations are unguarded,
  and map definitions are the encoder's `define-fun`s, satisfied as
  `Prop`-level function equalities.
- `Ttac/VcCheck.lean` — `checkVC`: decidable well-formedness (single
  assert last-in-block, pure SSA, forward edges, phi shape, the
  critical-edge side condition, guard-free program expressions, a
  checked dominator certificate; block guards are a dedicated
  `Exp.blk` atom, disjoint from program registers by construction)
  plus per-constraint and per-map-definition membership in the
  expected sets. Definition and use checks run uniformly over
  `(sort, register)` pairs via `Cmd.def?` and `Exp.vars`. The Prop
  bundle `WellFormed P` (via `wellFormed_iff`) packages the eight
  program-shape conjuncts so proof statements take one `hwf` and
  project fields (`hwf.ssa`, …); `domClosedOK` is deliberately NOT a
  field — it stays an explicit hypothesis, so "takes `hdc`" marks the
  dominance boundary in the signature language (only adequacy does).
- `Ttac/VcLemmas.lean` — evaluation lemmas for the fold constructors
  (`eval_mkImp`, `eval_mkOr`, `eval_mkIte`, ...) and the
  semantics-preservation of the lowering mirror (`eval_lower`).
- `Ttac/VcTrace.lean` — the Prop layer over the Bool well-formedness
  checks: definition sites and position order (`IsDefAt`,
  `DefsBefore`, `ssa_unique`), the visited chain (`Chained`,
  `EdgeTaken`, ordering, `visited_amo`), per-command final-state facts
  (`CmdFact`, `CmdFact.factB_eval`), the single-assert shape, and the
  dominator bridges (`dom_visited`).
- `Ttac/VcFacts.lean` — shared characterization lemmas: bridges from
  the well-formedness checks (`useOK_dom`, `guardFree_at`,
  `guard_eval`, `edge_cond_vars`), constraint-shape characterizations
  (`mem_cmdConstraints`, `mem_expectedMapDefs`, ...), and the variable
  inventories of the fold constructors and phi right-hand sides
  (`phiChain_vars`, `phi_src_lt`).
- `Ttac/VcPrefix.lean` — the operational-facts producer and the
  annotated VC. `forwardTrace`/`forwardStructural` reduce a failing
  execution, by one forward induction over the prefix, to structural
  facts (visited list in execution order, taken-edge chain,
  per-command `CmdFact`s) with a local per-step SSA freeze
  (`cmdFact_freeze`/`edgeTaken_freeze`) — no global stability.
  `VcAdequacy` consumes these to seed the denotational fold. Also
  home to `Vc.AnnVC`, the site-tagged VC the untrusted annotator
  emits, and `cfgConstraintsFor`, the per-block CFG generator.
- `Ttac/VcCfgPath.lean` — the CFG constraints and the guarded command
  facts discharged against *any* state whose guards are the
  reachability valuation of a real forward path
  (`cfgConstraints_sat` / `factConstraints_sat`). No dominator table
  in the signatures: against one concrete path state an edge condition
  is simply true and a command fact simply holds — there is no
  quantified witness class to freeze registers across.
- `Ttac/VcDenot.lean` — the denotational semantics and the soundness
  proof. `denot P s0` executes every block in index order (inactive blocks
  are identity except phis, which always compute the guard-selected
  `phiRhs` — so the unguarded phi equations hold by construction);
  guards fold in `assume`-feasibility (`reach ∧ assumesOK`: active
  means every assume executed-true, stuck means the guard is false),
  and safety is last-block unreachability (`Safe_denot`; `assert c`
  reads as `assume c`, the only EXIT in-edge is the failing branch).
  Lemma B (`denot_sat_of_path`) shows a path state models the whole VC
  via the `VcCfgPath` lemmas; the by-construction half derives the
  fold's equations (`FoldFact` freeze + `prefixState` stability), and
  the reachability core (`denot_adj_edge`) shows the active set is a
  single taken-edge chain — its engine is `edgeTaken_unique`, needing
  neither `amoSideOK` nor dominance. The soundness statement is
  factored through the semantic admission criterion `DenotSound`
  ("weak enough": every failing denotational run models the VC) —
  `safe_denot_of_denotSound` needs nothing else, and the expected set
  is demoted to one decidable certificate (`denotSound_of_expected`);
  looser certificates (a per-site weakening table) can be added
  without touching soundness. Main results, sorry-free: `denot_sat`
  and `checkVC_safe_denot` (`checkVC` accepts ∧ VC unsat ⇒
  `Safe_denot`) — the proof never constructs a witness and never
  consults the dominator table. `Adequacy` (operational failure ⇒
  denotational EXIT reached) is the factored-out bridge to
  `Program.Safe` (`safe_of_safe_denot`), proven in `VcAdequacy`. The
  SAT direction is `not_safe_denot_of_seed`: `denot` is a computable
  fold, so a solver model transpiled into a seed state refutes
  `Safe_denot` by evaluation (`native_decide`) — no trace, no proof
  object; a wrong seed fails to certify, never certifies wrongly
  (`ttac cex-check`).
- `Ttac/VcWeaken.lean` — the weakening-table admission checker.
  `checkVC` admits a constraint only byte-identical to `expected P`, so
  every encoder fold must be mirrored exactly; `checkVCW` instead
  accepts any constraint that **weakens from** some anchor. Two tables,
  two growth axes: the *anchor* table is the existing per-instruction
  machinery (`Cmd.factB` → `cmdConstraints`, ...; adding a command = a
  `factB` row + its `denot` case), and the *closure* table
  (`Vc.weakensFrom`: reflexivity, trivial-true, or-introduction,
  hypothesis-introduction; adding a vcgen simplification = a row here)
  carries one obligation per row — its case in `weakensFrom_sound`:
  if a formula is accepted as a weakening, it is a weakening. Complex
  simplifications will carry witnesses (rewrite chains replayed row by
  row) in the VC syntax. Soundness composes through `DenotSound`:
  `denotSound_of_checkVCW` and `checkVCW_safe_denot`. Strictly
  generalizes `checkVC`'s admission (membership = the reflexivity row).
  The site-tagged variant `checkVCWAnn` (over `Vc.AnnVC` buckets)
  consults only the tagged site's own anchors — `cfgConstraintsFor P b`
  / the block's `cmdConstraints` / the block's `cmdMapDef?` outputs /
  the objective pair — so the checker never computes the global
  `Vc.expected` or `Vc.expectedMapDefs` at all; the expected sets
  survive only proof-side (per-site anchors embed into them,
  `denot_sat`/`denot_mapDef` supply their truth). Map definitions are
  equalities, so their table (`Vc.mapDefFrom`) is a *sound-rewrite*
  table — rows must be eval-equalities (v1: reflexivity; future rows
  admit vcgen's map-side simplifications such as shadowed-store
  elimination). `checkVCWAnn_safe_denot`, and operationally
  `checkVCWAnn_safe` (`VcAdequacy`).
- `Ttac/VcAdequacy.lean` — the adequacy proof: an operational failure
  reaches EXIT denotationally (`adequacy : wellFormed P → Adequacy P`).
  The seed is the final operational state σ; *clean* registers (every
  fold-writing definition site visited) agree with σ through the whole
  fold — the site's `CmdFact` gives the operational equation and its
  reads are dominated-hence-visited-hence-clean (`dom_visited`; the
  no-leak fact, and where the dominator table earns its keep in the
  denotational story) — and guards match visitedness below the fail
  block (a visited predecessor's edge to an unvisited block cannot be
  the taken one: taken edges are unique). Blocks above the fail block
  may activate spuriously (its terminator never ran) and nothing below
  reads them. Closes the operational chain: `checkVCW_safe` and
  `checkVC_safe_via_denot` — the `checkVC_safe` statement by a fully
  independent path, with no witness construction.
- `Ttac/VcCoadequacy.lean` — the converse: a seed reaching EXIT
  denotationally replays as a real failing execution
  (`unsafe_of_seed`), completing the picture
  (`safe_iff_safe_denot : P.Safe ↔ Safe_denot P`). The run is seeded
  with `denot P s0` *itself*, so every write is a self-write
  (`State.upd_self`) and the state is constant along the run — no
  agreement invariant and, unlike adequacy, **no dominance**
  (`domClosedOK` unused). Needs one check beyond `wellFormed`:
  `phiCoversOK` (every predecessor of a phi block has an arm; kept out
  of `wellFormed` since the soundness direction never needs it).
  Coverage is genuinely necessary — at an uncovered taken predecessor
  the machine is stuck at the phi while the fold falls through to the
  unguarded last arm, so `denot` strictly over-approximates there.
- `Ttac/Product.lean` — the idealized rw-eq product (lockstep
  fragment) and its verified safety transfer:
  `product_transfer : Safe_denot (product A B) → Safe_denot B →
  Safe_denot A` (operational form `product_transfer_safe`). Two copies
  in disjoint register namespaces (`pv j i = 3*i + j`), CHKs only at
  the observables (branch agreement, B-assume validity, assert
  pairing), paired havocs equated (`x₁ := x₀` — the simulation's input
  correspondence). Proof: the coadequacy self-write seeding, doubled —
  the A-copy fold is the identity, B-copy junk is confined to
  registers defined in A-dead blocks and isolated by dominance (the
  table is shared with A under lockstep). Dominance and phi coverage
  are needed on `B` only — the asymmetry mirrors adequacy vs.
  coadequacy.
- `Ttac/ProductStutter.lean` — the rw-eq product under CFG surgery
  (stuttering mode): the rewrite drops single-predecessor fall-through
  blocks (`cfg-simplify`'s shape); the block matching is untrusted
  witness data validated by the decidable `surgeryOK` (the Lean-side
  `sim_precheck`), and B-copy phis are re-keyed on A's CFG with
  sources routed through each predecessor's owning matched block.
  `stutter_transfer` proves the safety transfer with *fewer*
  hypotheses than lockstep predicted: no `domClosedOK A` (A-side
  dominance is replaced by walking B's closure facts along the
  matched projection of A's active path) and no `phiCoversOK B` (the
  routing check subsumes coverage). The implementation's DEST/IN_DEST
  ghost flags turn out to be unnecessary in the idealized fragment —
  the shape that needs them requires a critical edge, which
  `amoSideOK` forbids.
- `TtacExamples/Diamond.lean` — golden deep + shallow embeddings of the
  scalar diamond, shallow safety theorem proved. The Python test suite
  pins the emitter against these shapes; keep them in sync.
- `TtacExamples/DiamondVc.lean` — the diamond's real `ttac vcgen`
  output, hand-transcribed, accepted by `checkVC` via `native_decide`
  (and a tampered variant rejected); pins the fold mirror against the
  Python encoder.
- `TtacExamples/BytemapVc.lean` — the same for the bytemap-phi example
  (`safe_bytemap_phi.ttac`): stores, a map phi, and a select, with the
  encoder's `define-fun`s as `mapDefs`; pins the map side of the
  mirror (and rejects a tampered store).
- `TtacExamples/DiamondAnnVc.lean` — the diamond's annotated VC
  (`Vc.AnnVC`) accepted by `checkVCWAnn` via `native_decide`, threaded
  through `checkVCAnn_safe` (and a tampered annotation rejected);
  confirms the forward checker accepts a real program's buckets.
- `TtacExamples/DiamondCex.lean` — counterexample certificate for an
  unsafe diamond variant: a seed reaching EXIT certified by
  `native_decide` and lifted to `¬ Safe_denot` via
  `not_safe_denot_of_seed`, then to operational `prog.Unsafe` via
  `unsafe_of_seed` (converse adequacy; `wellFormed` + `phiCoversOK`
  checked by `native_decide`). A non-driving seed is shown not to
  certify. Pins the `ttac cex-check` emitter's shapes.

## Building

```
lake exe cache get   # fetch mathlib oleans (first time)
lake build           # must be green, zero sorries
```

The toolchain pin (`lean-toolchain`) must byte-match the pinned mathlib
release tag in `lakefile.toml`; the generator copies both (plus
`lake-manifest.json`) into generated projects so they cannot skew.
