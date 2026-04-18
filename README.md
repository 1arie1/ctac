# ctac ✈️

Python library and CLI for Certora **TAC** program dumps (`.tac` files).  
SeaTac vibes: taxiway maps for TAC CFGs. 🛫🛬

## Environment (recommended) 🧳

Use Python **3.13+** (3.14 is fine). From the repo root:

```bash
python3.14 -m venv .venv
.venv/bin/pip install -U pip
.venv/bin/pip install -e ".[dev]"
```

Then run tools with `.venv/bin/ctac` or `source .venv/bin/activate`.

## Usage 🛫

```bash
# agent-focused guidance (plain text, terse)
ctac --agent
ctac stats --agent

ctac stats path/to/file.tac
# compact/legacy-style stats only:
ctac stats path/to/file.tac --top-blocks 0 --no-by-cmd-kind
# stats now also include expression-op counts and non-linear mul/div counters.
# directory input is allowed (Certora Prover output dir); ctac auto-picks a non-vacuity TAC from outputs/
ctac stats path/to/EvmOutput3-good --plain
# parse command prints the same stats payload:
ctac parse path/to/file.tac

# control-flow graph (goto-style text, default) 🗺️
ctac cfg path/to/file.tac
# one edge per line
ctac cfg path/to/file.tac --style edges
# first 50 blocks only
ctac cfg path/to/file.tac --max-blocks 50

# filters (combine with AND): path to a block, between two blocks, allow-list, …
ctac cfg file.tac --to 236_1_0_0_0_0
ctac cfg file.tac --from 0_0_0_0_0_0 --to 236_1_0_0_0_0
ctac cfg file.tac --only 0_0_0_0_0_0,236_1_0_0_0_0
ctac cfg file.tac --id-contains 236_1 --cmd-contains AssumeExpCmd
ctac cfg file.tac --id-regex '^[0-9]+_1_' --exclude 0_0_0_0_0_0

# pretty-print TAC as a goto program 🛬
ctac pp file.tac
# choose backend printer (`human` skips AnnotationCmd/LabelCmd, `raw` keeps dump lines)
ctac pp file.tac --printer human
ctac pp file.tac --printer raw
# pp supports the same filters as cfg
ctac pp file.tac --from 0_0_0_0_0_0 --to 236_1_0_0_0_0

# search command lines (alias: `ctac grep`)
ctac search file.tac 'assume R[0-9]+ <= \\[2\\^64-1\\]'
# literal substring mode
ctac search file.tac 'assert' --literal
# print only block ids that matched
ctac grep file.tac 'if .* < .*' --blocks-only
# optimization hunt: detect self-compare candidates like A < A
ctac search file.tac 'if (R[0-9]+) < \\1' --regex
# optimization hunt: bool-temp equality checks constrained true (candidate: inline into assume)
ctac search file.tac 'if .* == .* \\{ 1 \\} else \\{ 0 \\}' --regex
# hotspot triage: where many repeated u64 guards appear (count + constrained path slice)
ctac search file.tac 'assume R[0-9]+ <= \\[2\\^64-1\\]' --count --from A --to B

# interpret TAC program (assume-fail stops, assert-fail continues) 🧪
ctac run file.tac
# trace execution with per-instruction values and taken branches
ctac run file.tac --trace
# havoc strategy: zero (default), random, ask
ctac run file.tac --havoc-mode random
# use TAC model values for havoc; missing values use sentinel fallback
ctac run file.tac --model path/to/Assertions.txt
# if PATH is a prover-output directory, ctac run auto-attempts model resolution from the same directory
ctac run path/to/EvmOutput3-bad --plain
# directory model input is allowed; ctac resolves Reports/ctpp_<rule>-Assertions.txt
ctac run path/to/EvmOutput3-bad --model path/to/EvmOutput3-bad --trace --plain
# optional second model for havoc fallback (when --model has no value)
ctac run file.tac --model primary.txt --fallback secondary.txt
# validate computed assignments against the model
ctac run file.tac --model path/to/Assertions.txt --validate

# SMT VC dump (requires loop-free TAC with exactly one AssertCmd, last in its block)
# semantics: SAT iff failing assertion is reachable
ctac smt file.tac --plain
# default encoding is sea_vc (simplified DSA+reachability, QF_NIA/QF_UFNIA)
# semantics: static assignments as top-level equalities, dynamic defs as ITEs
ctac smt file.tac --encoding sea_vc
# alternative path-predicate encoding (QF_BV)
ctac smt file.tac --encoding vc-path-predicates
# write SMT-LIB to file
ctac smt file.tac --output out.smt2

# coarse CFG matching (weighted structure + source/function/snippet signals) 🛰️
ctac cfg-match a.tac b.tac
# tighten/relax accepted matches
ctac cfg-match a.tac b.tac --min-score 0.60
# tune how much literal constants influence matching
ctac cfg-match a.tac b.tac --const-weight 0.35

# basic-block semantic comparison on top of CFG matches 🧭
ctac bb-diff a.tac b.tac
# include source lines and show more changed blocks
ctac bb-diff a.tac b.tac --with-source --max-blocks 50
# cap per-block diff verbosity for huge blocks
ctac bb-diff a.tac b.tac --max-diff-lines 80
```

Directory input behavior:
- For TAC path arguments, if a directory is passed, ctac scans `<dir>/outputs/*.tac`,
  ignores files containing `-rule_not_vacuous`, and picks one TAC deterministically.
- If multiple TAC files remain, ctac prints an input warning and continues.
- For `run --model <dir>` (and `--fallback <dir>`), ctac resolves models from `<dir>/Reports/`
  using `ctpp_<rule>-Assertions.txt`, where `<rule>` comes from the selected TAC name.
- Non-`Assertions` model suffixes are ignored; ctac prints an input warning.

## Library 🏗️

```python
from ctac.parse import parse_path
from ctac.graph import Cfg, CfgFilter

tac = parse_path("file.tac")
print(len(tac.program.blocks))
cfg = Cfg(tac.program)
only_path, _ = cfg.filtered(CfgFilter(from_id="entry", to_id="exit"))
print(len(only_path.blocks))
```

## Authors

- Arie Gurfinkel <arie@certora.com>

## License

MIT. See `LICENSE`.
