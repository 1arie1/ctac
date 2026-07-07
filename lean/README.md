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
  via `Cmd.factB` (`factConstraints`); phis and map assignments
  contribute *unguarded definitions* (`unguardedDef?` — shared with
  the witness construction; map definitions are the encoder's
  `define-fun`s, satisfied as `Prop`-level function equalities).
- `Ttac/VcCheck.lean` — `checkVC`: decidable well-formedness (single
  assert last-in-block, pure SSA, forward edges, phi shape, the
  critical-edge side condition, guard-free program expressions, a
  checked dominator certificate; block guards are a dedicated
  `Exp.blk` atom, disjoint from program registers by construction)
  plus per-constraint and per-map-definition membership in the
  expected sets. Definition and use checks run uniformly over
  `(sort, register)` pairs via `Cmd.def?` and `Exp.vars`.
- `Ttac/DefExt.lean` — the generic definitional-extension lemma,
  independent of any encoding: a state satisfying ψ *robustly*
  (invariant under changes to a register set `W`), extended by an
  ordered definition list with targets in `W`, satisfies ψ ∧ EQ
  (`sat_extend`). Robustness is semantic, not syntactic
  non-occurrence; the syntactic form survives as the bridge
  `robust_of_avoids`.
- `Ttac/VcLemmas.lean` / `VcTrace.lean` / `VcReplay.lean` /
  `VcSound.lean` — the soundness proof, factored along the extension:
  a failing execution abstracts to a `Suffix` of final-state facts
  (`VcTrace`; one stability lemma over `(sort, register)` pairs, one
  case per command kind, and the effect-table law
  `CmdFact.factB_eval`); the unvisited-phi equations form an ordered
  definition list (`VcReplay` — the *unguarded definitions* of
  unvisited blocks: phis of any sort and map assignments; SSA gives
  distinct targets, dominated uses the lexicographic ordering); every
  other expected constraint and every visited map definition is
  robust with respect to those targets (`VcSound` — every `factB`
  command shares the ONE `robust_cmd_fact` case, and the visited-phi
  fact `visited_phi_defHolds` serves boolean phi constraints and map
  phis alike); `sat_extend`/`sat_extend_defs` close both halves at
  the witness. Main results, all sorry-free: `checkVC_sound` (failing
  execution ⇒ VC satisfiable) and `checkVC_safe` (`checkVC` accepts ∧
  VC unsat ⇒ `Program.Safe`).
- `Ttac/VcPrefix.lean` — an independent *forward* (prefix-induction)
  soundness proof, parallel to `VcSound`. Instead of the backward
  `Suffix`, `forwardTrace` does one induction over the execution prefix
  (the `ReflTransGen` tail recursor), producing the visited list in
  execution order, the taken-edge chain, and per-command facts — with a
  local per-step SSA freeze (`cmdFact_freeze`/`edgeTaken_freeze`) rather
  than a global stability lemma, and no transfer to a final state.
  `forwardStructural` splits off the failing `assertFalse` step and
  packages this into the structural facts the *encoding-generic* leaves
  (`robust_cmd_fact`, `visited_phi_defHolds`, `visited_amo`,
  `dom_visited`, `sat_extend`) consume — those are shared verbatim with
  `VcSound`. The VC is a site-annotated, per-block bucketed `Vc.AnnVC`
  validated locally by `Vc.checkVCAnn` against the encoder's own
  generators (a wrong annotation fails the cheap local check — a
  completeness loss, never unsound). Main results, sorry-free:
  `checkVCAnn_sound` and `checkVCAnn_safe`, the forward analogues of
  `checkVC_sound`/`checkVC_safe`.
- `Ttac/VcCfgPath.lean` — the CFG constraints and the guarded command
  facts discharged against *any* state whose guards are the
  reachability valuation of a real forward path
  (`cfgConstraints_sat` / `factConstraints_sat`). No `domClosedOK`, no
  `usesOK`, no `DefExt`, no `Robust` in the signatures: the dominator
  table in `VcSound`/`VcPrefix` exists only to freeze registers across
  the `Robust` witness class, and against one concrete path state
  there is no class to freeze across.
- `Ttac/VcDenot.lean` — a third, *denotational* soundness proof.
  `denot P s0` executes every block in index order (inactive blocks
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
  `Safe_denot`) — the proof never mentions `DefExt`, the dominator
  table, or a witness construction. `Adequacy` (operational failure ⇒
  denotational EXIT reached) is the deliberately factored-out bridge
  to `Program.Safe` (`safe_of_safe_denot`).
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
  independent path, no `DefExt`, no witness construction.
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
  (`Vc.AnnVC`) accepted by `checkVCAnn` via `native_decide`, threaded
  through `checkVCAnn_safe` (and a tampered annotation rejected);
  confirms the forward checker accepts a real program's buckets.

## Building

```
lake exe cache get   # fetch mathlib oleans (first time)
lake build           # must be green, zero sorries
```

The toolchain pin (`lean-toolchain`) must byte-match the pinned mathlib
release tag in `lakefile.toml`; the generator copies both (plus
`lake-manifest.json`) into generated projects so they cannot skew.
