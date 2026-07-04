# Tiny TAC examples

`ttac` programs for trying the toolchain end to end. The `safe_*` programs are
small feature demos; the `practical_*` programs are reduced from larger TAC
programs and keep the main computation while dropping bv256/chunking noise.
**UNSAT** means the assertion always holds; **SAT** means the assertion can fail,
and the solver finds a counterexample.

| File | Verdict | What it shows |
|---|---|---|
| `safe_core.ttac` | unsat | branches, `assume`, an assert that only runs on a feasible path |
| `safe_bytemap.ttac` | unsat | bytemap store-then-load (`M[i:=v]`, `M[i]`) |
| `safe_borrow_mut.ttac` | unsat | mutable borrow + `put_ref`/`release` (references) |
| `unsafe_assert.ttac` | sat | a plain assertion that need not hold |
| `unsafe_bytemap.ttac` | sat | reading havoced memory |
| `unsafe_borrow_mut.ttac` | sat | a wrong assertion after a borrowed write |
| `practical_share_burn_monotonicity.ttac` | unsat | reduced share-burn monotonicity: proportional conversion, exact-balance branches, min caps |
| `practical_withdrawal_summary.ttac` | unsat | reduced withdrawal summary: utilization branch, mode selection, capped withdrawal |
| `practical_delegate_clear.ttac` | sat | reduced account delegate-clear flow: unpack state, authorize, repack, assert delegate cleared |

## Commands

First look — what's in a program (command kinds, bytemap capability,
borrows, types):

```
ttac stats safe_core.ttac --plain
```

Run it concretely (zero-havoc), with a per-step trace:

```
ttac run safe_core.ttac --trace
```

Generate the VC and solve it (`sat` = unsafe, `unsat` = safe):

```
ttac vcgen safe_core.ttac --solve
```

`--solve` finds z3 via `--z3 PATH`, the `CTAC_Z3` environment variable,
or `z3` on `PATH` (in that order):

```
ttac vcgen safe_core.ttac --solve --z3 /path/to/z3
```

The `*_borrow_*` programs use references, which `vcgen` does not encode
directly — desugar them first (a `ttac -> ttac` pass that lowers borrows
to plain assignments + a prophecy `assume`):

```
ttac desugar safe_borrow_mut.ttac | ttac vcgen - --solve
```

## Lean project (`ttac lean`)

Transpile a program into a self-contained Lean 4 project with two
embeddings — *deep* (a term of the `Ttac` inductive types from
`<repo>/lean/`, with a small-step semantics, for proving properties of
VCGen) and *shallow* (per-block `Prop` definitions in native Lean, for
proving properties of the program itself):

```
ttac lean prog.ttac -o out/prog
cd out/prog && lake exe cache get && lake build
```

The project contains `<Name>/Deep.lean` and `<Name>/Shallow.lean`
(regenerated on `--force`) plus `<Name>/Proofs.lean` with `sorry`
theorem stubs (generated once, never overwritten — proofs written there
survive regeneration). `--build` runs the lake build directly.
`--no-deep` / `--no-shallow` select a single embedding; a shallow-only
project is pure core Lean (no `Ttac` library, no mathlib) and builds in
under a second.

v1 accepts only the scalar fragment: `int`/`bool` registers, pure SSA
(phi fine, no dynamic definitions), loop-free CFG, no use-before-def.
Bytemaps and references are rejected, so the examples in this directory
are outside the fragment for now; the reference scalar program is the
diamond in `lean/TtacExamples/Diamond.lean` (hand-written golden twin of
the generated output, with the shallow safety theorem proved).

## Counterexamples (model replay)

For an unsafe program, ask the solver for a model and replay it
concretely — `run` reproduces the assertion failure:

```
ttac vcgen unsafe_bytemap.ttac --solve --model m.txt
ttac run  unsafe_bytemap.ttac --model m.txt        # assert_fail: 1
```

For a borrow program, desugar first and replay on the desugared form:

```
ttac desugar unsafe_borrow_mut.ttac > unsafe_borrow_mut.lowered.ttac
ttac vcgen unsafe_borrow_mut.lowered.ttac --solve --model m.txt
ttac run  unsafe_borrow_mut.lowered.ttac --model m.txt
```

Note: free-running a borrow program *without* a model (e.g.
`ttac run safe_borrow_mut.ttac`) stops at a release's prophecy
`assume` — the promised value cannot be guessed by forward execution.
That is inherent to the reference semantics; supply a model to replay a
specific execution.
