# ctac ✈️

Python library and CLI for Certora TAC program dumps (`.tac` and
`.sbf.json`). SeaTac vibes: taxiway maps for TAC CFGs. 🛫🛬

A quick map of what `ctac` gives you beyond `grep`:

| Purpose | Commands |
|---|---|
| **Inspect** a TAC file | `stats`, `parse`, `pp`, `cfg`, `search` (alias: `grep`) |
| **Compare** two builds | `op-diff`, `cfg-match`, `bb-diff` |
| **Analyze** data-flow | `df` |
| **Transform** TAC | `rw` (rewrites + DCE), `ua` (uniquify asserts) |
| **Verify** | `run` (concrete interpreter), `smt` (SMT-LIB VC + z3) |
| **Validate** the rewriter | `rw-valid` |

Every command has its own `--help` (full flags + examples in the
epilog) and `--agent` (terse agent-oriented guidance with
"why beat manual" framing). The rest of this README is a map, not a
manual — drill into `--help` for flag-level detail.

## Environment 🧳

Python **3.13+** (3.14 is fine). From the repo root:

```bash
python3.14 -m venv .venv
.venv/bin/pip install -U pip
.venv/bin/pip install -e ".[dev]"
```

Run tools with `.venv/bin/ctac` or `source .venv/bin/activate`.

**Shell completion** (one-time setup; tab-completes commands,
subcommands, flag values — and `ctac search`'s pattern against the
TAC operator name set):

```bash
ctac --install-completion       # auto-detects zsh / bash / fish / powershell
# restart shell
```

## Typical pipelines 🛫

**Solve an assertion end-to-end:**

```bash
ctac stats f.tac --plain                              # first look (memory capability, block/cmd counts)
ctac rw f.tac -o opt.tac --plain                      # simplify (div/bitfield/Ite rewrites + DCE)
ctac ua opt.tac -o sa.tac --plain                     # fold all asserts into one __UA_ERROR block
ctac smt sa.tac --plain --run --model m.txt           # generate VC, invoke z3, write SAT model
ctac run sa.tac --plain --model m.txt --trace         # replay the model concretely
```

**Compare two builds (did the encoder drift?):**

```bash
ctac op-diff a.tac b.tac --plain                      # per-stat frequency delta, grouped by section
ctac cfg-match a.tac b.tac --plain                    # block correspondence (for bb-diff)
ctac bb-diff a.tac b.tac --plain --drop-empty         # per-block semantic delta
```

**Validate the rewriter itself:**

```bash
ctac rw-valid -o /tmp/rwv --plain                     # emit per-rule SMT soundness scripts
for f in /tmp/rwv/*.smt2; do echo -n "$(basename $f): "; z3 "$f" -T:5; done
# expected `unsat` on every script
```

## Commands 🗺️

### Inspect

```bash
ctac stats f.tac --plain                              # blocks/cmds/metas/ops + memory capability
ctac stats path/to/output-dir --plain                 # auto-resolves outputs/*.tac

ctac pp f.tac --plain                                 # humanized TAC (slices, ceil-div, etc.)
ctac pp f.tac --plain --from A --to B                 # slice on a CFG path
ctac pp f.tac -o out.htac                             # write pretty-printed text

ctac cfg f.tac --plain                                # goto-style CFG text (default)
ctac cfg f.tac --plain --style edges                  # one `src -> dst` per line — grep-friendly
ctac cfg f.tac --plain --style dot | dot -Tsvg -o cfg.svg
ctac cfg f.tac --plain --style blocks                 # one block id per line — for shell loops

ctac search f.tac 'BWAnd' --plain --count             # count op usage (pattern tab-completes)
ctac search f.tac 'BWAnd' --plain -C 2                # grep-style context (-B / -A / -C)
ctac search f.tac '0x[0-9a-f]+' --plain --count-by-match  # frequency table of distinct matches
ctac search f.tac 'BWAnd' --plain -q --count          # pipeable; `awk '/^matches:/ {print $2}'`
```

`cfg`, `pp`, `search`, and `df` all share the same filter grammar —
`--from`, `--to`, `--only`, `--id-contains`, `--id-regex`,
`--cmd-contains`, `--exclude` — combining with AND.

### Compare two builds

```bash
ctac op-diff a.tac b.tac --plain                      # per-stat delta, headline finding in one shot
ctac op-diff a.tac b.tac --plain --show expression_ops
ctac op-diff a.tac b.tac --json                       # machine-readable

ctac cfg-match a.tac b.tac --plain --const-weight 0.2
ctac bb-diff  a.tac b.tac --plain --drop-empty --max-diff-lines 120
```

`op-diff` is the fastest way to spot encoder-level drift between two
Prover versions (it's built on top of `ctac stats`). Reach for
`cfg-match` + `bb-diff` for block-level structural / semantic diffs.

### Analyze data-flow

```bash
ctac df f.tac --plain                                 # all analyses, summary
ctac df f.tac --plain --show dsa                      # validate DSA form (rejecter for sea_vc)
ctac df f.tac --plain --show dce --details            # per-item dead-code listing
ctac df f.tac --plain --json                          # machine-readable
```

Available analyses: `def-use`, `liveness`, `dce`, `use-before-def`,
`dsa`, `control-dependence`, `uce` (useless-assume elimination).

### Transform TAC

```bash
ctac rw f.tac --plain --report                        # simplify + print per-rule hit counts
ctac rw f.tac -o small.tac --plain                    # write a round-trippable .tac
ctac rw f.tac -o small.htac --plain                   # write pretty-printed .htac
ctac rw f.tac --no-purify-div --plain                 # disable R4a; other rules still run

ctac ua f.tac -o f_ua.tac --plain                     # fold every assert into one __UA_ERROR block
ctac ua f.tac -o f_ua.tac --plain --report            # + counts
```

`rw` runs the iterated simplification pipeline (N1–N4 bit-op
canonicalization, R1–R4 div rules, R6 ceil-div collapse, boolean/Ite
cleanup, CSE, copy-prop). `--purify-div` / `--purify-ite` /
`--purify-assert` / `--purify-assume` control post-DCE naming phases.
Soundness of every rule is documented by `ctac rw-valid`.

`ua` is the prerequisite for `ctac smt` on multi-assert TAC: it
emits `if (P) goto GOOD else goto __UA_ERROR` for each assert, with
`assume P` opening the GOOD continuation — Floyd-Hoare style, no
inversion.

### Verify

```bash
ctac run f.tac --plain                                # concrete interpreter, zero-havoc
ctac run f.tac --plain --model m.txt --trace          # replay a z3 model (TAC or SMT-LIB format)
ctac run f.tac --plain --model m.txt --validate       # compare computed values vs model

ctac smt f.tac --plain                                # emit SMT-LIB VC to stdout
ctac smt f.tac --plain -o out.smt2                    # write .smt2
ctac smt f.tac --plain --run                          # invoke z3
ctac smt f.tac --plain --run --model out.model.txt    # write SAT model in TAC format
ctac smt f.tac --plain --run --unsat-core             # name asserts, print core on unsat
```

`ctac smt` requires loop-free, single-assert TAC (run `ua` first),
and bytemap-free / bytemap-ro memory capability (check with
`ctac stats`). The sole encoder is `sea_vc` — QF_UFNIA, DSA +
block-reachability, sound bv256 domain constraints, bytemap-as-UF
with a per-application range axiom.

`ctac run` interprets the program concretely — `assume` failures stop
the run silently (infeasible path), `assert` failures continue and
count toward `assert_fail`. Bytemap symbols load from model entries
(both TAC and raw z3 formats) and feed `Select` lookups.

### Validate the rewriter

```bash
ctac rw-valid -o /tmp/rwv --plain                     # emit all per-rule SMT specs
ctac rw-valid -o /tmp/rwv --plain --rule R4a          # one rule only
```

Emits a self-contained `.smt2` per rule (plus `manifest.json`) whose
expected outcome is `unsat`. Currently covers R4 (5 operator variants),
R4a (base + signed), R6 (base + signed). Other rules are listed in
`manifest.json:missing`.

## Directory input conventions

- **TAC inputs**: a directory argument is scanned as
  `<dir>/outputs/*.tac`, ignoring `-rule_not_vacuous` files. If
  multiple candidates remain, ctac warns and picks deterministically.
- **Model inputs** (`run --model <dir>`, `--fallback <dir>`): resolved
  from `<dir>/Reports/ctpp_<rule>-Assertions.txt` for the selected
  TAC's rule. Non-`Assertions` suffixes emit a warning and are
  skipped.
- **Text commands** (`parse`, `stats`, `search`, `cfg`, `pp`,
  `cfg-match`, `bb-diff`) accept either `.tac` or `.sbf.json`
  directly.

## Library 🏗️

The Python API mirrors the CLI surface. Major modules:

```python
from ctac.parse     import parse_path          # .tac / .sbf.json -> TacFile
from ctac.graph     import Cfg, CfgFilter      # CFG with filtering + rendering
from ctac.analysis  import (                   # data-flow passes + classifiers
    analyze_dsa, analyze_liveness, eliminate_dead_assignments,
    classify_bytemap_usage, BytemapCapability,
)
from ctac.rewrite   import rewrite_program     # rewrite driver
from ctac.rewrite.rules import simplify_pipeline, purify_pipeline
from ctac.ua        import uniquify_asserts, merge_asserts
from ctac.eval      import RunConfig, run_program, parse_model_path, MemoryModel
from ctac.smt       import build_vc, render_smt_script
```

One worked example — slice a CFG between two blocks:

```python
from ctac.parse import parse_path
from ctac.graph import Cfg, CfgFilter

tac = parse_path("f.tac")
cfg = Cfg(tac.program)
sliced, warnings = cfg.filtered(CfgFilter(from_id="entry", to_id="exit"))
print(f"{len(sliced.blocks)} blocks on some path from entry to exit")
```

End-to-end — rewrite, uniquify, build VC:

```python
import dataclasses
from ctac.parse import parse_path
from ctac.rewrite import rewrite_program
from ctac.rewrite.rules import default_pipeline
from ctac.ua import uniquify_asserts
from ctac.smt import build_vc, render_smt_script

tac = parse_path("f.tac")
rw  = rewrite_program(tac.program, default_pipeline)
ua  = uniquify_asserts(rw.program)
vc  = build_vc(dataclasses.replace(tac, program=ua.program))
print(render_smt_script(vc))
```

## Authors

- Arie Gurfinkel <arie@certora.com>

### AI collaborators

This project was built in close collaboration with generative-AI
coding tools. Design decisions, scope control, and final review rest
with the human authors above; AI agents contributed implementation,
tests, and documentation under direction.

- **Cursor** (premium model, likely OpenAI Codex) — initial
  scaffolding and first ~three days of development. Visible in
  per-commit `Made-with: Cursor` trailers spanning the first 43
  commits (the initial TAC toolkit, ctac CLI structure, stats,
  search, cfg, pp, run, cfg-match, bb-diff, df, and the sea_vc
  foundations).
- **Claude Code** (Anthropic Claude Opus 4.x) — primary coding
  collaborator from mid-April 2026 onward. Visible in per-commit
  `Co-Authored-By: Claude Opus 4.x ...` trailers. Delivered the
  rewrite pipeline validation (`rw-valid`), bytemap-ro SMT + run
  support, `ua` uniquify-asserts, `op-diff`, the search sub-features
  (`-C`, `--count-by-match`, `-q`, `--printer auto`,
  pattern tab-completion), shell completion wiring, and the
  README / `--help` / `--agent` overhaul.
- Occasional use of other assistants (editor-integrated
  autocompletion, model-backed search) that do not appear in commit
  trailers.

All AI contributions were reviewed and committed by the human authors.

## License

MIT. See `LICENSE`.
