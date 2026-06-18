# Tiny TAC examples

Small `ttac` programs for trying the toolchain end to end. The `safe_*`
programs are **UNSAT** (the assertion always holds); the `unsafe_*`
programs are **SAT** (the assertion can fail, and the solver finds a
counterexample).

| File | Verdict | What it shows |
|---|---|---|
| `safe_core.ttac` | unsat | branches, `assume`, an assert that only runs on a feasible path |
| `safe_bytemap.ttac` | unsat | bytemap store-then-load (`M[i:=v]`, `M[i]`) |
| `safe_borrow_mut.ttac` | unsat | mutable borrow + `put_ref`/`release` (references) |
| `unsafe_assert.ttac` | sat | a plain assertion that need not hold |
| `unsafe_bytemap.ttac` | sat | reading havoced memory |
| `unsafe_borrow_mut.ttac` | sat | a wrong assertion after a borrowed write |

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
