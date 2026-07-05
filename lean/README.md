# Ttac — Lean 4 library for Tiny TAC

The program-independent half of `ttac lean`: the deep embedding of
Tiny TAC with a small-step operational semantics. Generated projects
receive a copy of this library, so it must stay in sync with the
emitter in `src/ctac/ttac/lean/`.

The embedding is *sort-indexed and table-driven*: one `Ty`-indexed
register file and expression type (sorts `int`/`bool`/`map`; the
checker currently accepts the scalar fragment), operators as
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
- `Ttac/Vc.lean` — the expected-constraint generator for `ttac
  vc-check`: exact Lean mirrors of the Python encoder's constant folds
  (`mkImp`, `mkOr`, `amoClauses`, ...), the lowering mirror, phi
  right-hand sides, `Vc.Sat`/`Vc.Unsat`. Per-command constraints are
  table-driven via `Cmd.factB` (`factConstraints`); only phi is
  special.
- `Ttac/VcCheck.lean` — `checkVC`: decidable well-formedness (single
  assert last-in-block, pure SSA, forward edges, phi shape, the
  critical-edge side condition, guard-free program expressions, a
  checked dominator certificate; block guards are a dedicated
  `Exp.blk` atom, disjoint from program registers by construction)
  plus per-constraint membership in the expected set. Definition and
  use checks run uniformly over `(sort, register)` pairs via
  `Cmd.def?` and `Exp.vars`.
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
  definition list (`VcReplay` — SSA gives distinct targets, the
  phi-arm rule the ordering, all sort-generically); every other
  expected constraint is robust with respect to those targets
  (`VcSound` — every `factB` command shares the ONE `robust_cmd_fact`
  case); `sat_extend` closes both halves at the witness. Main results,
  all sorry-free: `checkVC_sound` (failing execution ⇒ VC satisfiable)
  and `checkVC_safe` (`checkVC` accepts ∧ VC unsat ⇒ `Program.Safe`).
- `TtacExamples/Diamond.lean` — golden deep + shallow embeddings of the
  scalar diamond, shallow safety theorem proved. The Python test suite
  pins the emitter against these shapes; keep them in sync.
- `TtacExamples/DiamondVc.lean` — the diamond's real `ttac vcgen`
  output, hand-transcribed, accepted by `checkVC` via `native_decide`
  (and a tampered variant rejected); pins the fold mirror against the
  Python encoder.

## Building

```
lake exe cache get   # fetch mathlib oleans (first time)
lake build           # must be green, zero sorries
```

The toolchain pin (`lean-toolchain`) must byte-match the pinned mathlib
release tag in `lakefile.toml`; the generator copies both (plus
`lake-manifest.json`) into generated projects so they cannot skew.
