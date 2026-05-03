# AGENTS.md

Use `ctac` in plain mode unless color is required.

## Quick Rules

- Run tests with the repo venv: `python3 -m venv .venv && .venv/bin/pip install -e ".[dev]"` once, then `.venv/bin/pytest` (see [README.md](README.md) setup).
- Prefer `--plain` for deterministic output.
- Use `--agent` for terse, plain-text command guidance (`ctac --agent`, `ctac <subcmd> --agent`).
- First step on unknown file: `ctac stats <file> --plain`.
- TAC path args accept files or Certora output directories.
- Directory TAC resolution: scan `<dir>/outputs/*.tac`, ignore `-rule_not_vacuous`, pick one, warn if multiple.
- `ctac stats` now includes command-kind counts and top blocks by default.
- `ctac stats` also includes expression-op counts and non-linear mul/div counters.
- Use `ctac stats <file> --plain --top-blocks 0 --no-by-cmd-kind` for compact stats.
- If parse fails with `Missing line 'Program {'`, input is not a full `.tac` file.
- For focused views, use `pp`/`cfg` with `--from` and `--to`.
- For cross-build comparison, start with `op-diff` (per-stat delta);
  drill into blocks with `cfg-match` + `bb-diff`.
- For CFG reasoning, prefer structured text (edges + block summaries), not images.
- Before `ctac smt`: run `ctac ua` to ensure single-assert TAC, and
  check `memory.capability` in `ctac stats` (must be `bytemap-free`
  or `bytemap-ro`).
- Soundness of rewrite rules: `ctac rw-valid -o <dir>` emits per-rule
  SMT specs; run z3 on each (expected `unsat`).

## CFG Communication Format (Agent-First)

- Do not rely on rendered CFG pictures.
- Provide:
  - entry block id
  - relevant node ids
  - edge list (`src -> dst`)
  - block summaries (key `assume`/`assert`/branch condition + critical assignments)
  - target question (e.g. assert reachability, mismatch cause)
- Keep scope sliced (`--from/--to`) before analysis.

Minimal extraction:

1. `ctac cfg f.tac --plain --style edges --from <a> --to <b>`
2. `ctac pp f.tac --plain --from <a> --to <b>`
3. Use outputs as structured context for reasoning.

Prompt template:

- "Given this edge list and block summaries, determine whether `<assert_block>` is reachable and identify the branch/assume that causes divergence."

## Core Commands

- `ctac stats <file> --plain`
  - Cheap sanity: blocks, commands, metas (+ command kinds + top blocks by default).
  - Also prints expression-op frequencies and non-linear arithmetic counters.
  - Compact mode: `--top-blocks 0 --no-by-cmd-kind`.

- `ctac pp <file> --plain`
  - Humanized TAC as goto program.
  - Supports filters:
    - `--from <NBID>`
    - `--to <NBID>`
    - `--only <id1,id2,...>`
    - `--id-contains <s>`
    - `--id-regex <re>`
    - `--cmd-contains <s>`
    - `--exclude <id1,id2,...>`

- `ctac cfg <file> --plain`
  - CFG-only text.
  - `--style goto|edges|dot|blocks`
    - `goto`: default, block-oriented (`label: ...; goto <succ>`).
    - `edges`: one `src -> dst` line per edge (grep-friendly).
    - `dot`: Graphviz digraph (`| dot -Tsvg -o cfg.svg`).
    - `blocks`: one block id per line, no preamble (shell loops).
  - Same filters as `pp`.

- `ctac search <file> <pattern> --plain` (alias: `ctac grep`)
  - Search command lines in TAC blocks (regex by default; use `--literal` for substring).
  - Pattern positional tab-completes to TAC operator names
    (`BWAnd`, `Mod`, `Select`, `AssignExpCmd`, ...) after
    `ctac --install-completion`.
  - Useful flags:
    - `--blocks-only`
    - `--count`
    - `--count-by-match` — frequency table of distinct matches
      (replaces `| grep -oE ... | sort | uniq -c | sort -rn`).
    - `-C N` / `-B N` / `-A N` — grep-style context within a block.
    - `-q` / `--quiet` — drop `#`-prefixed preamble + footers (pipeable).
    - `--max-matches <n>` (use `0` for unlimited).
    - `--printer auto|raw|human` — default `auto` picks `raw` under
      `--plain` (so TAC op names match as typed) and `human` otherwise.
  - Supports same structural filters as `pp` (`--from/--to/--only/...`).
  - Useful analysis examples:
    - `ctac search f.tac 'if (R[0-9]+) < \1' --plain`
      - Finds tautological-false self-compare candidates (optimization opportunities).
    - `ctac search f.tac 'if .* == .* \{ 1 \} else \{ 0 \}' --plain`
      - Finds bool-temp equality checks often followed by `assume ... == 1` (canonicalization opportunities).
    - `ctac search f.tac 'assume R[0-9]+ <= \[2\^64-1\]' --plain --count --from <a> --to <b>`
      - Quantifies repeated range guards inside a path slice.
    - `ctac search f.tac '0x[0-9a-f]+' --plain --count-by-match`
      - Frequency table of distinct hex constants.

- `ctac slice <file> -c <SPEC> --plain`
  - Backward static slice through data and control dependences.
    Pure display filter (slices are not encodable; for that, use the
    upcoming `sem-slice`).
  - Criterion forms:
    - `SYM` — every def of canonical SYM (in DSA usually a single
      point; for dynamic registers, all sibling defs).
    - `SYM@BLK` — def(s) of SYM in block BLK (disambiguates dynamic
      registers).
    - `BLK:assert` — the last `AssertCmd` in BLK.
    - `BLK` — every cmd in BLK as a seed.
  - We deliberately do NOT expose `BLK:IDX` — annotations occupy
    command slots, so cmd indices are unstable for users.
  - Key flags:
    - `--data/--no-data`, `--control/--no-control` — toggle the
      dependence kinds independently.
    - `--depth N` — bound on slicing rounds (`0` = seeds only).
    - `--show pp|points|stats|json` — output mode. `pp` (default) is
      a sliced htac the VSCode plugin can render.
    - `--mark drop|elide|gray` — how non-selected commands render.
      `drop` (default) hides them; `elide` collapses runs to `...`;
      `gray` shows them dimmed (or `# ` prefixed under `--plain`).
    - `--include-weak` — include `AnnotationCmd` weak refs.
    - Pre-slice `--from/--to/--only/--id-contains/--id-regex/--cmd-contains/--exclude` (same shape as `pp`).
  - Useful examples:
    - `ctac slice f.tac -c B1054 --plain` — backward slice rooted at
      a boolean assertion variable; bytemap chains
      (`Select(M ...) -> Store(M' ...)`) fall out automatically.
    - `ctac slice f.tac -c B1054 --no-control --plain` — data-only
      chain; cleaner view of the bytemap pipeline.
    - `ctac slice f.tac -c <blk>:assert --plain` — slice from the
      assert in a block.
    - `ctac slice f.tac -c M1031 --show stats --plain` — heat-map
      "how many cmds touch this bytemap?".

- `ctac cfg-match <left> <right> --plain`
  - Coarse block mapping across programs.
  - Key flags:
    - `--min-score <0..1>`
    - `--const-weight <0..1>`
    - `--max-rows <n>`

- `ctac bb-diff <left> <right> --plain`
  - Per-matched-block semantic diff.
  - Key flags:
    - `--min-score <0..1>`
    - `--const-weight <0..1>`
    - `--normalize-vars/--raw-vars`
    - `--drop-empty/--keep-empty`
    - `--with-source/--no-source`
    - `--max-blocks <n>`
    - `--max-diff-lines <n>`
    - `--context <n>`

- `ctac op-diff <left> <right> --plain`
  - Per-stat frequency delta between two TAC files (grouped by
    section: `expression_ops`, `command_kinds`, `memory`, ...).
    Built on top of `ctac stats`; fastest way to spot encoder-level
    drift between Prover versions.
  - Key flags:
    - `--show <sections>` — comma-separated list to restrict output.
    - `--show-unchanged` — include zero-delta stats (audit view).
    - `--json` — machine-readable.

- `ctac df <file> --plain`
  - Data-flow analyses: `def-use`, `liveness`, `dce`,
    `use-before-def`, `dsa`, `control-dependence`, `uce`
    (useless-assume elimination).
  - Key flags:
    - `--show <analyses>` — comma-separated list (default: all).
    - `--details` — per-item listing (e.g. DCE dead items).
    - `--json` — machine-readable.
  - `dsa.status: invalid` means `ctac smt` will reject — check this
    before running the VC.

- `ctac types <file> --plain`
  - Sound, possibly-incomplete kind inference for TAC registers
    over the lattice `Top (= Int+Ptr) | Int | Ptr | Bot`.
    Pointer kind comes from use as a `Select`/`Store` index;
    integer kind comes from operand position of arithmetic ops
    (`Mul`, `Div`, `IntMul`, `IntDiv`, `Shift*`, `BWXOr`, `BNot`).
    `narrow` and `BWAnd`/`BWOr` with a constant operand are
    identity (passthrough); `R = SymRef(R')` and
    `assume R == R'` unify classes; `Add`/`IntAdd` of one Ptr
    and one Int is Ptr.
  - Soundness contract: never tags `Int` for a register that is
    actually a pointer, or vice-versa. Abstains to `Top` when
    evidence is insufficient.
  - Key flags:
    - `--show ptr|int|top|bot|all` — filter the table by kind.
    - `--by-class` — group by union-find equivalence class.
    - `--include-memory` — include `bytemap`/`ghostmap` rows.
    - `--json` — machine-readable.
  - `Bot` indicates a contradictory class (used as both index
    and arithmetic operand) — investigate as a soundness signal.

- `ctac rw <file> --plain`
  - TAC -> TAC simplification: div / bitfield / Ite rewrites + DCE,
    plus optional div and bool-name purification.
  - Key flags:
    - `-o <path>` — write round-trippable `.tac` or pretty-printed
      `.htac` (extension decides).
    - `--report` — per-rule hit counts.
    - `--no-purify-div` / `--no-purify-ite` / `--no-purify-assert` /
      `--no-purify-assume` — disable individual post-DCE naming phases.
  - Soundness of every rewrite rule is documented by `ctac rw-valid`.

- `ctac ua <file> --plain`
  - Uniquify assertions: fold every `AssertCmd` into a single
    `__UA_ERROR` block so the output satisfies `ctac smt`'s
    one-assert precondition. Predicates are used verbatim — no
    inversion, Floyd-Hoare style.
  - Key flags:
    - `-o <path>` — write `.tac` / `.htac` output.
    - `--report` — counts.
  - Single-assert input is a no-op (`was_noop: true`).

- `ctac pin <file> --plain`
  - Specialize a TAC: drop blocks (with cleanup), bind variables to
    constants, enumerate splits as cases. Library-first; CLI is a
    thin façade over `ctac.transform.pin`.
  - Output contract: every block remaining is on an entry-to-exit
    path (no orphans, no dangling halts). DSA + use-before-def
    preserved.
  - Key flags:
    - `--drop BLK1,BLK2` — repeatable; remove blocks from the CFG.
      RC vars for dropped blocks fold to false automatically.
    - `--bind VAR=VALUE` — repeatable; substitute a variable.
      RC variables (`ReachabilityCertora*`) are rejected — use
      `--drop` instead.
    - `--split BLK` — repeatable; enumerate one case per
      predecessor of `BLK`. Output becomes a directory with one
      `.tac` per case + `manifest.json`.
    - `-o PATH` — output file (single-case) or directory
      (multi-case with `--split`).
    - `--show` — render an existing manifest directory's summary
      (also implicit when the positional is a directory with
      `manifest.json`).
    - `--name-style descriptive|index` — case filename style.
    - `--no-cleanup` — skip the cleanup rewriter pass.
    - `--trace PATH` — JSONL trace of pin decisions and edits
      (debug-only; `-` for stdout).
  - Library: `from ctac.transform.pin import PinPlan, apply,
    enumerate, bind, compute_dead_blocks`.

- `ctac rw-valid --plain`
  - Emit per-rule SMT-LIB soundness specs (one `.smt2` per rule +
    `manifest.json`). Does NOT invoke z3 — run the solver yourself.
  - Currently covers R4 (4 op variants), R4a (base + signed), R6
    (base + signed). Other rules listed under `manifest.json:missing`.
  - Key flags:
    - `-o <dir>` (required) — output directory.
    - `--rule <NAME>` (repeatable) — emit specs for named rules only.
  - Expected solver result: `unsat` on every script. `sat` is a
    counterexample (bug); `unknown` means escalate (tactics, Lean).

- `ctac run <file> --plain`
  - Concrete interpreter.
  - Key flags:
    - `--trace`
    - `--havoc-mode zero|random|ask`
    - `--model <path>`
    - `--fallback <path>`
    - `--validate`
  - Model directory resolution:
    - When PATH is a directory and `--model` is omitted, ctac auto-attempts model resolution from the same directory.
    - `--model <dir>` resolves `<dir>/Reports/ctpp_<rule>-Assertions.txt` for the selected TAC rule.
    - Non-`Assertions` suffix models are ignored with an input warning.

- `ctac smt <file> --plain`
  - Emit SMT-LIB VC. Encoder: `sea_vc` (QF_UFNIA, DSA +
    block-reachability, sound bv256 domain constraints,
    bytemap-as-UF with per-application range axiom; currently the
    only supported encoder).
  - Preconditions: loop-free TAC, exactly one `AssertCmd` (run
    `ctac ua` first to merge), `AssertCmd` must be the last command
    in its block, and memory capability must be `bytemap-free` or
    `bytemap-ro` (check with `ctac stats`).
  - VC semantics: SAT iff assertion-failure state is reachable.
  - Solver mode: `--run` invokes z3 and reports `sat|unsat|unknown|timeout`.
  - SAT model export: `--model <path>` writes TAC model text compatible with `ctac run --model`.
  - Unsat-core mode: `--unsat-core` names asserts and prints the core on UNSAT.
  - Static-def guarding: `--guard-statics` emits one
    `(=> BLK_<bid> (and (= lhs1 rhs1) (= lhs2 rhs2) ...))` per
    defining block — a single block guard shared across that
    block's static equalities — instead of the default bare
    `(= lhs rhs)` per def. Off by default; entry-block defs are
    unaffected (entry guard is `true`).
  - Dynamic-def guarding: `--guard-dynamics` encodes each dynamic
    (DSA-merged) assignment as a per-defining-block guarded
    equality `(=> BLK_<bid> (= lhs rhs))` instead of the default
    `(= lhs (ite cond rhs ...))` ITE-merge form. One assertion per
    defining block (deduped by RHS) vs. one assertion per symbol.
  - CFG-constraint encoding: `--cfg-encoding
    {bwd0,bwd1,fwd,fwd-bwd,fwd-edge,bwd-edge}` selects the
    constraint shape over block-reachability variables.
    `bwd0` (default) — predecessor-oriented edge-feasibility
    OR-of-ANDs. `bwd1` — predecessor per-edge clausal
    implications (sound under AMO). `fwd` — successor
    one-way implications. `fwd-bwd` — `fwd` plus backward
    immediate-dominator clauses `BLK_i => BLK_idom(i)` for
    each non-entry block, giving BCP a 1-hop backward
    propagation path (logically redundant given `fwd`'s
    transitive chain, but shorter). `fwd-edge` / `bwd-edge`
    — introduce per-edge Bool variables `e_<i>_<j>` and use
    a biconditional block-existence over those variables.
  - Bytemap Store-over-Store reduction: `--store-reduce` builds a
    per-map chain data structure during encoding. Prunes shadowed
    `Store` entries when a later Store at the same key supersedes
    an earlier one (sound by the array Store/Select axiom);
    preserves the `(ite ... (M_old idx))` shared-sibling form
    when no shadow fires; and drops `define-fun` lines for
    bytemap symbols not reachable from any `Select` query (their
    content is inlined into the chain that reads them). Off by
    default — preserves byte-identical output for the existing
    eager emission.
  - Z3 knobs: `--timeout` (seconds), `--seed`, `--tactic`, and passthrough `--z3-args`.
  - Debug mode: `--debug` prints z3 stdin/stdout/stderr and a replay command.

## Project (HEAD-tracked workspace)

A *project* is a working directory with a `.ctac/` sidecar that
tracks "the current TAC" through a multi-step pipeline. Content is
content-addressed under `.ctac/objects/<sha[:2]>/<sha[2:]>`; the
project root carries friendly-name symlinks (`base.tac`,
`base.rw.tac`, ...) for quick access.

- `ctac prj init <FILE> -o <DIR> --plain`
  - Create a project at DIR with FILE as the base. HEAD is set to
    the base; label `base` points at the same sha.
  - `--label NAME` overrides the default `base` label.
  - `--force` overwrites an existing `.ctac/`.

- `ctac prj list <DIR> [<OBJ_ID>] --plain`
  - Tabular list of all objects (sha, kind, command, names). With
    `OBJ_ID`, falls through to `prj info` for that one object.

- `ctac prj info <DIR> <OBJ_ID> --plain [--recursive]`
  - Full provenance record. `--recursive` walks the parent chain.
  - `OBJ_ID` accepts: full sha, unique sha prefix (>= 4 hex chars),
    label name, friendly symlink name, or a project-relative path.

Phase-1 status: existing TAC commands (`rw`, `ua`, `smt`, `pp`)
do **not** yet accept a project directory in place of a `.tac`
argument — that's phase 2. For now, run them on the explicit
object path (`mytac/base.tac`) and re-add the result with the
`ctac.project.Project.add(...)` library API.

## Repo Structure (Key Paths)

- VSCode extension for `.htac` lives under `tools/vscode-tac/`.
- Extension entrypoint: `tools/vscode-tac/extension.js`.
- TextMate grammar (syntax highlighting): `tools/vscode-tac/syntaxes/htac.tmLanguage.json`.
- Language config (brackets/comments/etc): `tools/vscode-tac/language-configuration.json`.
- Preview theme used for scopes: `tools/vscode-tac/themes/tac-preview-color-theme.json`.

## Minimal Workflows

- Inspect one program:
  1. `ctac stats f.tac --plain`
  2. `ctac pp f.tac --plain --from <a> --to <b>`
  3. `ctac cfg f.tac --plain --from <a> --to <b>`
  4. `ctac types f.tac --plain --show ptr` — list provable pointers.

- Compare two programs:
  1. `ctac op-diff a.tac b.tac --plain` — per-stat frequency delta,
     headline finding in one shot.
  2. `ctac cfg-match a.tac b.tac --plain --const-weight 0.2`
  3. `ctac bb-diff a.tac b.tac --plain --const-weight 0.2 --drop-empty --max-diff-lines 120`
  4. Raise `--const-weight` if symmetric blocks are cross-matched.

- Solve an assertion end-to-end:
  1. `ctac stats f.tac --plain` — confirm memory capability +
     block/cmd counts.
  2. `ctac rw f.tac -o opt.tac --plain` — simplify.
  3. `ctac ua opt.tac -o sa.tac --plain` — fold to single assert.
  4. `ctac smt sa.tac --plain --run --model m.txt` — z3 + TAC model.
  5. `ctac run sa.tac --plain --model m.txt --trace` — replay
     concretely.

- Validate runtime against model:
  1. `ctac run f.tac --plain --model model.txt --validate`
  2. Add `--trace` when mismatch localization is needed.

## Practical Defaults

- Use:
  - `--plain`
  - `--drop-empty` for `bb-diff`
  - `--normalize-vars` for cross-build diff
  - `--const-weight 0.2` baseline
- Increase `--const-weight` when constants are strong anchors.
