# Tiny TAC examples

`ttac` programs for trying the toolchain end to end. The `safe_*` programs are
small feature demos; the `practical_*` programs are reduced from larger TAC
programs and keep the main computation while dropping bv256/chunking noise.
**UNSAT** means the assertion always holds; **SAT** means the assertion can fail,
and the solver finds a counterexample.

| File | Verdict | What it shows |
|---|---|---|
| `safe_core.ttac` | unsat | branches, `assume`, an assert that only runs on a feasible path |
| `safe_scalar_diamond.ttac` | unsat | scalar-only diamond (havoc, branch, phi); the `ttac lean` v1 fragment |
| `safe_bytemap.ttac` | unsat | bytemap store-then-load (`M[i:=v]`, `M[i]`) |
| `safe_bytemap_phi.ttac` | unsat | bytemap stores on both branches merged by a bytemap phi |
| `safe_borrow_mut.ttac` | unsat | mutable borrow + `put_ref`/`release` (references) |
| `unsafe_assert.ttac` | sat | a plain assertion that need not hold |
| `unsafe_bytemap.ttac` | sat | reading havoced memory |
| `unsafe_borrow_mut.ttac` | sat | a wrong assertion after a borrowed write |
| `practical_share_burn_monotonicity.ttac` | unsat | reduced share-burn monotonicity: proportional conversion, exact-balance branches, min caps |
| `practical_withdrawal_summary.ttac` | unsat | reduced withdrawal summary: utilization branch, mode selection, capped withdrawal |
| `practical_delegate_clear.ttac` | sat | reduced account delegate-clear flow: unpack state, authorize, repack, assert delegate cleared |
| `nla_muldiv_roundtrip.ttac` | unsat | floor/ceil mul-div round-trip `ceil(floor(a*b/c)*c/b) <= a`; nonlinear, no guarding assume |
| `nla_muldiv_monotone.ttac` | unsat | floor mul-div monotone in the numerator: `sa<=sb => floor(sa*p/q)<=floor(sb*p/q)` |
| `nla_muldiv_superadd.ttac` | unsat | same-denominator superadditivity: `floor(x*p/q)+floor(y*p/q)<=floor((x+y)*p/q)` |
| `nla_toassets_additivity.ttac` | unsat | ERC4626 `toAssetsDown` additivity with adjusted totals (nested mul-divs) |
| `nla_convert_cap.ttac` | unsat | multi-block: exact/proportional branch + phi, `assets <= total_assets` (nonlinear on one arm) |
| `nla_share_burn_unguarded.ttac` | unsat | `practical_share_burn` with the ordering `assume` removed: branch-derived div monotonicity across phi merges |
| `nla_fee_waterfall.ttac` | unsat | large (34 blocks): 8-stage waivable-fee waterfall, solvency `0 <= v_final` |

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
ttac lean safe_scalar_diamond.ttac -o out/diamond
cd out/diamond && lake exe cache get && lake build
```

The project contains `<Name>/Deep.lean` and `<Name>/Shallow.lean`
(regenerated on `--force`) plus `<Name>/Proofs.lean` with `sorry`
theorem stubs (generated once, never overwritten — proofs written there
survive regeneration). `--build` runs the lake build directly.
`--no-deep` / `--no-shallow` select a single embedding; a shallow-only
project is pure core Lean (no `Ttac` library, no mathlib) and builds in
under a second.

`ttac lean` accepts the scalar fragment: `int`/`bool` registers,
loop-free CFG, no use-before-def. Dynamic (multi-block) definitions are
converted to phi form automatically (a DSA->SSA precondition pass), so
the `practical_*` and `nla_*` scalar programs transpile directly
without hand-rewriting the merges. Bytemaps and references are still
rejected (the shallow embedding has no map story yet).

Worked shallow proofs for three of these programs live as a package in
the repo's Lean project, `lean/TtacShallow/` (open `lean/` in VS Code):

The proofs trace a difficulty ladder — from a one-shot tactic on the
assume-guarded programs, through core-Lean division lemmas, to a
`nlinarith` search:

The `z3` column is the solve time on the `ttac vcgen` output (best of 5,
z3 4.17.0; also recorded in each Lean file header):

| Module | Source | z3 | Proof | Needs |
|---|---|--:|---|---|
| `TtacShallow/ShareBurn.lean` | `practical_share_burn_monotonicity.ttac` | ~6ms | `unfold; simp; omega` one-shot (assume-guarded; linear after abstraction) | core |
| `TtacShallow/Withdrawal.lean` | `practical_withdrawal_summary.ttac` | ~6ms | same one-shot (+ `Bool.and_eq_true`) | core |
| `TtacShallow/Monotone.lean` | `nla_muldiv_monotone.ttac` | ~8ms | `Int.ediv_le_ediv` ∘ `mul_le_mul_of_nonneg_right` (two lemmas) | core |
| `TtacShallow/Superadd.lean` | `nla_muldiv_superadd.ttac` | ~9ms | two floor lower bounds + `le_ediv_iff_mul_le`, `omega` glue | core |
| `TtacShallow/Roundtrip.lean` | `nla_muldiv_roundtrip.ttac` | ~10ms | floor lower bound + `Int.ediv_le_iff_le_mul`; `omega` alone fails | core |
| `TtacShallow/ConvertCap.lean` | `nla_convert_cap.ttac` | ~9ms | *multi-block*: branch split, `exact` arm `omega`, `prop` arm the div upper bound behind a phi | core |
| `TtacShallow/ShareBurnU.lean` | `nla_share_burn_unguarded.ttac` | ~17ms | *multi-block*: shared min-cap lemma + 4-way branch split, each deriving the ordering differently (2 vacuous, 1 div bound, 1 div monotone) | core |
| `TtacShallow/Additivity.lean` | `nla_toassets_additivity.ttac` | ~28ms | tight (depends on the div remainders); the two full div characterizations + `nlinarith` | Mathlib |
| `TtacShallow/FeeWaterfall.lean` | `nla_fee_waterfall.ttac` | ~345ms | *large, 34 blocks*: bottom-up per-stage lemma, linear in the 8 stages (no 2^8 branch blow-up) | core |

Every nonlinear obligation defeats `omega` alone (it abstracts the
`ediv`/`mul` atoms). The `nla_muldiv_*`, `ConvertCap`, `ShareBurnU`, and
`FeeWaterfall` proofs stay in core Lean by supplying the
`Int.ediv`/`Int.emod` identities and letting `omega` finish the linear
part; `Additivity` is tight enough that it needs `nlinarith` (hence
Mathlib). Each file keeps the `ttac lean`-emitted `Shallow` embedding
verbatim and adds a hand-written `shallow_safe` theorem; all are
axiom-clean. The single-embedding golden twin for the diamond is
`lean/TtacExamples/Diamond.lean`.

## Verified VC validation (`ttac vc-check`)

Validate that a VC really is a correct verification condition for its
program, with a machine-checked Lean proof instead of trust in the
encoder:

```
ttac vcgen safe_scalar_diamond.ttac -o d.smt2
ttac vc-check safe_scalar_diamond.ttac d.smt2 -o out/check
```

The command transpiles the program to the deep embedding and the smt2
asserts to a deep formula list, generates a Lean project, and runs
`lake build` (default; `--no-build` to skip). The build proves
`vc_ok : checkVC prog vc = true` by `native_decide` and
instantiates the library's once-and-for-all soundness theorem as
`vc_implies_safe : Unsat vc → prog.Safe`. Success prints
`vc-check: validated`.

What that buys: the logical gap between "z3 said unsat" and "the
program is safe" is closed by proof — every failing execution of the
program would be a satisfying assignment of the transpiled VC
(`Ttac.checkVC_sound`, sorry-free). The remaining trust surface is the
Lean toolchain, z3's unsat verdict, and two dumb syntactic translations
pinned by golden tests. A Python-side precheck (`--no-precheck` to
skip) diagnoses mismatches with exact line numbers before the build;
the build stays authoritative.

Unlike `ttac lean`, `vc-check` also accepts **bytemaps** — stores,
selects, aliases, and bytemap phis. The encoder's `define-fun`s (a
store's pointwise ite, an alias, a phi's merge over predecessor
guards) transpile to first-class map definitions checked and proved
alongside the boolean constraints:

```
ttac vcgen safe_bytemap_phi.ttac -o b.smt2
ttac vc-check safe_bytemap_phi.ttac b.smt2 -o out/bcheck
```

Its hand-transcribed golden twin is `lean/TtacExamples/BytemapVc.lean`.

Fragment: `int`/`bool`/`bytemap` registers, pure SSA, loop-free,
no use-before-def, references desugared; exactly one assert (run
`ttac ua --strategy merge` first), the assert last in its block, blocks
in topological source order, every block reachable. bwd0 encoding only.

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
