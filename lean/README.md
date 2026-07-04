# Ttac — Lean 4 library for Tiny TAC

The program-independent half of `ttac lean`: the deep embedding of
Tiny TAC (scalar fragment) with a small-step operational semantics.
Generated projects receive a copy of this library, so it must stay in
sync with the emitter in `src/ctac/ttac/lean/`.

## Modules

- `Ttac/Ast.lean` — `IExp`/`BExp` (mutually inductive; int and bool
  registers are separate `Nat` namespaces, so well-typedness holds by
  construction), `Cmd`, `Terminator`, `Block`, `Program`.
- `Ttac/State.lean` — total register files + `updI`/`updB` simp lemmas.
- `Ttac/Eval.lean` — total expression evaluation. Division is
  `Int.ediv` (Euclidean, `x / 0 = 0`), matching SMT-LIB `div` and the
  reference interpreter.
- `Ttac/Semantics.lean` — `Config` and the small-step `Step` inductive
  predicate. Havoc is a constructor argument (nondeterminism);
  `assume false` is stuck (pruned, vacuously safe).
- `Ttac/Safety.lean` — `Steps` (`Relation.ReflTransGen`),
  `Program.Safe`/`Unsafe`. `Unsafe` mirrors "the VC is satisfiable".
- `TtacExamples/Diamond.lean` — golden deep + shallow embeddings of the
  scalar diamond, shallow safety theorem proved. The Python test suite
  pins the emitter against these shapes; keep them in sync.

## Building

```
lake exe cache get   # fetch mathlib oleans (first time)
lake build           # must be green, zero sorries
```

The toolchain pin (`lean-toolchain`) must byte-match the pinned mathlib
release tag in `lakefile.toml`; the generator copies both (plus
`lake-manifest.json`) into generated projects so they cannot skew.
