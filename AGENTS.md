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
- Before `ctac smt`: run `ctac ua` to ensure single-assert TAC. Any
  bytemap capability is fine (`bytemap-rw` is encoded via Store/Select);
  the single-assert precondition is the usual blocker.
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

- `ctac sbf-tac <sbf.json> <tac> --plain`
  - Joins each SBF instruction with the TAC commands at the same
    `sbf_bytecode_address` (or `sbf.bytecode.address`). Three
    columns: address, SBF instruction, TAC command. The first row of
    each address group carries the SBF instruction; continuation
    rows leave the SBF column blank for additional TAC cmds. TAC
    cmds without an SBF address are not shown.
  - Useful for debugging the SBF → TAC lowering, and for propagating
    annotations from TAC back to SBF (`grep <addr>` on the joined
    view).
  - Key flags:
    - SBF CFG filters (same set as `ctac pp`, applied to the SBF
      side only): `--from`, `--to`, `--only`, `--id-contains`,
      `--id-regex`, `--cmd-contains`, `--exclude`.
    - `--address-range LO-HI` — keep only SBF rows whose bytecode
      address is in the inclusive window (same flag spelling as
      `ctac pp --address-range`).
    - `--printer human|raw`, `--strip-var-suffix`, `--human` —
      identical defaults to `ctac pp`.
    - `-o PATH` — write joined output to a file.

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
    (`Mul`, `Div`, `IntMul`, `IntDiv`, `Shift*`, `BWXOr`, `BWNot`).
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

- `ctac cfg-simplify <file> --plain`
  - Drop annotation-only fall-through blocks (single declared
    successor, body only `AnnotationCmd`/`LabelCmd`) and rewire each
    unique predecessor to the successor.
  - Key flags:
    - `-o <path>` — write `.tac` / `.htac` output.
    - `--report` — drop / rewire / skip counts.
  - Soundness verifiable via `ctac rw-eq`.

- `ctac ua <file> --plain`
  - Uniquify assertions so the output satisfies `ctac smt`'s
    one-assert precondition. Predicates are used verbatim — no
    inversion, Floyd-Hoare style.
  - Key flags:
    - `-o <path>` — write `.tac` / `.htac` output.
    - `--strategy merge|split` (default `merge`) — `merge` folds
      every `AssertCmd` into a single `__UA_ERROR` block; `split`
      emits one `.tac` per assertion.
    - `--report` — counts.
  - Single-assert input is a no-op (`was_noop: true`).

- `ctac strip <file> --plain`
  - Strip client-specific metadata (spec file paths, embedded source,
    function/crate names, call-trace snippets, assert ids) so a TAC
    dump can be published as an open benchmark. Default is
    allowlist-keep: generic structural metadata survives
    (`sbf.bytecode.address`, `tac.*` markers, `overflow.rewrite`,
    `debug.sbf.external_call` intrinsics); unknown keys are dropped
    (default-deny) and listed in `--report`. Assert messages become
    sequential generic `"assert <n>"` strings; `LabelCmd` lines are
    kept.
  - Key flags:
    - `-o <path>` — write `.tac` / `.htac` output.
    - `--all` — maximal anonymity: empty Metas, drop every
      `AnnotationCmd`, remove all `:N` meta suffixes.
    - `--report` — per-key kept/dropped counts + unknown-key list.
  - Audit before publishing:
    `grep -iE 'specFile|filepath|mangledName|displayMessage' out.tac`
    should be empty.

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
  - Currently covers R1, R4 (5 op variants), R4a (base + signed),
    R6 (base + signed), and ADD_BV_MAX_TO_ITE. Other rules listed
    under `manifest.json:missing`.
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
  - Emit SMT-LIB VC. Default encoder: `sea_vc` (QF_UFNIA, DSA +
    block-reachability, sound bv256 domain constraints,
    bytemap-as-UF with per-application range axiom). Select others
    via `--encoding`: `leino`, `sea`, `sea_gate`, `sea_vc`.
  - Preconditions: loop-free TAC, exactly one `AssertCmd` (run
    `ctac ua` first to merge), and `AssertCmd` must be the last command
    in its block. Any bytemap capability is supported (`bytemap-rw` is
    encoded via Store/Select); there is no `bytemap-free`/`bytemap-ro`
    requirement.
  - VC semantics: SAT iff assertion-failure state is reachable.
  - Encoder selection: `--encoding {leino,sea,sea_gate,sea_vc}`
    (default `sea_vc`). `--coi {thin,coarse,aggressive}` tunes the
    `sea_gate` cone-of-influence pruning (ignored for other
    encoders); `aggressive` is sound only for UNSAT.
  - Solver mode: `--run` invokes z3 and reports `sat|unsat|unknown|timeout`.
  - SAT model export: `--model <path>` writes TAC model text compatible with `ctac run --model`.
  - Unsat-core mode: `--unsat-core` names asserts and prints the core on UNSAT.
  - Static-def guarding: `--guard-statics` emits one
    `(=> BLK_<bid> (and (= lhs1 rhs1) ... cond1 cond2 ...))` per
    defining block — a single block guard shared across that
    block's static equalities **and assume conditions** —
    instead of the default bare `(= lhs rhs)` per static and
    `(=> BLK cond)` per assume. The combined conjunction lets
    `solve-eqs` extract equalities nested in assumes (e.g.
    `assume R == 0`) under the same guard. Off by default;
    entry-block defs/assumes are unaffected (entry guard is
    `true`, so the conjunction is bare).
  - Dynamic-def guarding: `--guard-dynamics` encodes each dynamic
    (DSA-merged) assignment as a per-defining-block guarded
    equality `(=> BLK_<bid> (= lhs rhs))` instead of the default
    `(= lhs (ite cond rhs ...))` ITE-merge form. One assertion per
    defining block (deduped by RHS) vs. one assertion per symbol.
  - Axiom guarding: `--guard-axioms` wraps each per-application UF
    axiom assertion in `(=> (or BLK_b1 BLK_b2 ...) <axiom>)`, where
    the disjunction collects every block whose top-level expression
    triggered the instance. Covers the expensive UF axioms
    (`bv256_xor`, `int_ceil_div`, `int_mul_div`). Memory bv256-range
    axioms on leaf bytemap UFs are *not* guarded — they are generic
    and cheap, always sound to assert. Entry-block-only triggers
    stay bare (entry guard is `true`). Off by default.
  - CFG-constraint encoding: `--cfg-encoding
    {bwd0,bwd1,fwd,fwd-bwd,fwd-edg,fwd-edg1,fwd-edg2,bwd-edge}`
    selects the constraint shape over block-reachability variables.
    `bwd0` (default) — predecessor-oriented edge-feasibility
    OR-of-ANDs. `bwd1` — predecessor per-edge clausal
    implications (sound under AMO). `fwd` — successor
    one-way implications. `fwd-bwd` — `fwd` plus backward
    immediate-dominator clauses `BLK_i => BLK_idom(i)` for
    each non-entry block, giving BCP a 1-hop backward
    propagation path (logically redundant given `fwd`'s
    transitive chain, but shorter). `fwd-edg` / `bwd-edge`
    — introduce per-edge Bool variables `e_<i>_<j>` and use
    a biconditional block-existence over those variables
    (edge vars at single-succ/pred blocks collapse to the
    block guard). `fwd-edg1` — edge variables for **every**
    edge (no collapse); biconditional written forward as
    `e_uv ⇔ (BLK_u ∧ g)`, per-non-entry block reachability
    as `BLK_v ⇔ ⋁ in-edges`, plus redundant AMO/ALO over
    outgoing edges as BCP fuel. `fwd-edg2` — `fwd-edg` plus
    pairwise AMO over incoming edges at merge blocks
    (mixed edge/block atoms; sound by the single-succ collapse).
  - bv256 Add/Sub axiomatization:
    `--bv-add-sub-no-mod-axiom` (default) emits a single-wrap ITE
    for TAC `Add` and `Sub`:
    `(ite (<= (+ a b) BV256_MAX) (+ a b) (- (+ a b) BV256_MOD))`
    for `Add` and the symmetric 2's-complement form for `Sub`.
    Both arms are linear in the operands, so LRA / solve-eqs /
    ctx-simplify can push through. `--bv-add-sub-mod-axiom`
    recovers the prior opaque `(mod (op a b) BV256_MOD)` form for
    A/B comparison or byte-identical legacy output. Affects only
    `Add`/`Sub`; `Mul` (multi-wrap) and `IntAdd`/`IntSub`
    (unwrapped) are unchanged.
  - Scalar inlining: `--inline-scalars` substitutes the RHS of
    static `AssignExpCmd` defs at every use site for a conservative
    set of "simple linear" shapes — `ConstExpr`, `SymbolRef` (alias),
    binary `Add`/`Sub`/`IntAdd`/`IntSub`/`Mul`/`IntMul` with at
    least one constant operand and a `SymbolRef` other operand,
    optionally wrapped by `safe_math_narrow_bvN`. Equality and
    `declare-const` for the inlined symbol are dropped. Useful for
    eliminating named-index intermediates so EUF and LIA see
    offsets directly in `M(_)` reads. Skips dynamic (DSA-merged)
    defs, havocs, map symbols, JumpiCmd conditions, and any RHS
    with non-`SymbolRef` / non-`ConstExpr` operand or a non-linear
    op between two non-consts. Under `--narrow-range` the bv256-
    domain axiom is re-instantiated on the inlined RHS rather than
    the eliminated symbol. Off by default — inlining can move
    terms into NL contexts (harming the NLA tactic) or duplicate
    subexpressions.
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

- `ctac smtlib <subcommand> <file> --plain`
  - Inspect and pretty-print existing SMT-LIB v2 files (the OUTPUT
    format `ctac smt` produces, or any external .smt2). Distinct
    from `ctac smt`, which is the TAC→SMT encoder.
  - Subcommands:
    - `ctac smtlib stats <file>` — command-kind counts, declare-const
      sort distribution, bytemap chain link count + depth distribution
      (min/median/max), unique UF-arg variables (the alias-cover T set).
      Use as the first step on an unknown .smt2.
    - `ctac smtlib pp <file> --width N` — pretty-print via a Wadler-style
      Doc algebra. Short forms stay flat; `and`/`or`/`=>`/`ite` break
      one-per-line when too wide. `-o PATH` writes to a file;
      `--no-comments` drops `;`-blocks.
    - `ctac smtlib roundtrip <file>` — parse then emit; reports
      byte-identical or the first diff position. Sanity check for
      the parser; useful when bisecting suspected emit bugs.
    - `ctac smtlib slice <file> --kinds K1,K2 --range I-J` — view a
      subset of statements; combine `--kinds` (Assert, DeclareConst,
      DefineFun, ...) with a `--range I-J` (0-based, inclusive)
      index window. `-o PATH` writes the slice to a file.
  - The library at `ctac.solver.smt2` powers more transformations
    (memory_abstract, scan_uf_arguments, name_asserts, append_assert)
    that aren't yet CLI-surfaced — used internally by alias-cover work.

- `ctac z3 <file.smt2> --plain`
  - Run z3 on an SMT-LIB file with classification + parallel
    seed / config racing. Default is a single run with a live
    progress panel + bottleneck signature (fast-close /
    lp-bp-blowup / nlsat-stuck / nlsat-dominant / etc.).
  - Useful modes:
    - `ctac z3 f.smt2 --seeds 0-7 -j 4` — seed sweep; first verdict
      wins, others SIGKILL'd. Cheap nudge when one seed is unlucky.
    - `ctac z3 f.smt2 --configs default,alt-then,bp-off --seeds 0-3
      -j auto` — configs × seeds parallel race.
    - `ctac z3 --list-configs` — see what's available (defaults +
      any `.ctac-z3-configs.json` discovered upward).
    - `ctac z3 ... --show-output` — print winner's z3 stdout (model,
      get-info, unsat-core, stats — whatever the .smt2 asked for).
    - `ctac z3 ... --save-rerun PATH` — executable bash script that
      reproduces the winning invocation.
    - `--z3 PATH` / `CTAC_Z3` env / `$PATH` — binary resolution.

- `ctac cover-cfg <file> --plain`
  - Sound CFG cover for a single-assert TAC VC: bottom-up
    path-decomposition via probe sampling + K-medoid clustering +
    a PB linear-path completeness probe. First SAT slice wins;
    otherwise runs the completeness CEGAR loop to a sound UNSAT
    verdict (or reports residual subgoals on timeout).
  - Key flags:
    - `-o <path>` — write the cover certificate (manifest JSON).
    - `--samples`, `--k`, `--budget`, `--absorb-budget`,
      `--absorb-threshold`, `--completeness-iter`,
      `--completeness-budget` — cover-loop tuning.
    - `--workers`, `--seed`, `--abort-on-timeout`,
      `--core-forbids/--no-core-forbids`.
    - `--z3 PATH`, `--ctac BIN`.

- `ctac verify-cover <cover.json> --plain`
  - Independent re-verifier: reads a cover manifest, re-runs every
    recorded z3 invocation, and confirms the verdicts match. Exits
    0 on full match; passing here implies the cover verdict is
    sound regardless of bugs in the producing loop.
  - Key flags:
    - `--z3 PATH` — override the z3 binary.
    - `--rederive-timeout <s>` — budget for pin / rw / smt
      re-derivation steps.
    - `--timeout-multiplier <x>` / `--timeout-slack <s>` —
      per-z3-step budget = `recorded wall_s * x + slack`.
    - `--ctac BIN` — ctac binary for re-derivation + SAT replay.
    - `--strict-validation` — SAT replay must have zero havoc
      fallbacks (default lax).

## Project (HEAD-tracked workspace)

A *project* is a working directory with a `.ctac/` sidecar that
tracks "the current TAC" through a multi-step pipeline. Content is
content-addressed under `.ctac/objects/<sha[:2]>/<sha[2:]>`; the
project root carries friendly-name symlinks (`base.tac`,
`base.rw.tac`, ...) for quick access. Friendly names derive from
the project label, not the (often long) original filename; the
original path is kept as `source` provenance, visible in
`prj list` / `prj info`.

- `ctac prj init <FILE> -o <DIR> --plain`
  - Create a project at DIR with FILE as the base. HEAD is set to
    the base; label `base` points at the same sha; the friendly
    link is `<label>.<ext>` (`base.tac`), with FILE's path recorded
    as the object's `source`.
  - `--label NAME` overrides the default `base` label (and the
    link stem: `NAME.tac`).
  - `--force` overwrites an existing `.ctac/`.

- `ctac prj list <DIR> [<OBJ_ID>] --plain`
  - Tabular list of all objects (sha, kind, command, names; rows
    ingested from outside show `<- <original filename>`). With
    `OBJ_ID`, falls through to `prj info` for that one object.

- `ctac prj info <DIR> <OBJ_ID> --plain [--recursive]`
  - Full provenance record. `--recursive` walks the parent chain.
  - `OBJ_ID` accepts: full sha, unique sha prefix (>= 4 hex chars),
    label name, friendly symlink name, or a project-relative path.

- `ctac prj set-head <DIR> <REF> --plain`
  - Move HEAD to `<REF>`. Special form `<set-ref>:<member-name>`
    materializes a fileset member as a fresh single-file object
    whose parent is the fileset, then moves HEAD to it.

- `ctac prj rewind <DIR> --plain`
  - Move HEAD back to the base object to try a different pipeline.
    Derived objects and links are kept for comparison: a re-run
    with different output gets a collision-suffixed name
    (`base.rw.2.tac`); identical output reuses the same object.

- `ctac prj reset <DIR> --plain`
  - Return the project to its init state: derived objects, their
    symlinks, and labels pointing at them are deleted; HEAD moves
    to the base. The base lives in the object store, so no re-init
    (and no access to the original source file) is needed.

- `ctac prj label <DIR> <OBJ_ID> <LABEL> --plain`
  - Attach a user-visible name to an object. Labels resolve like
    any other ref (sha / short sha / friendly name / label).

- `ctac prj export-path <DIR> [<REF>] --plain`
  - Print the absolute path to an object's content (default: HEAD).
    Output is one line, undecorated — designed for shell composition:
    ``cat $(ctac prj export-path mytac)``.

- `ctac prj archive <DIR> -o <FILE> --plain`
  - Pack `.ctac/` into a tarball. Compression by extension:
    `.tar.gz` / `.tgz` -> gzip; anything else -> plain tar.

- `ctac prj clone <SRC> -o <DST> [--force] --plain`
  - Duplicate a project. `<SRC>` is either an existing project
    directory or a tarball produced by `prj archive`; either way
    `.ctac/` is copied / extracted into `<DST>` and friendly-name
    symlinks are rebuilt from the manifest.

Project-aware commands (give the project dir in place of a `.tac`):

- HEAD-moving single-file producers (no `-o` ingests + advances
  HEAD): `rw`, `ua --strategy merge`, `pin` (without `--split`).
- HEAD-moving fileset producers: `pin --split`, `ua --strategy
  split`. Output is a tac-set (directory of cases + manifest);
  HEAD advances to the fileset object, friendly name
  `<stem>.<command>.split` (e.g. `base.pin.split/`,
  `base.ua.split/`).
- Sibling-producing (no `-o` ingests as a non-HEAD-advancing
  object whose parent is HEAD): `pp` writes `.htac`, `smt`
  writes `.smt2`.
- Explicit `-o PATH` always bypasses project ingestion; the user
  gets the file at PATH, the project is untouched.

When HEAD is a fileset, single-file consumers (`rw`, `ua`, `pp`,
`smt`) refuse to run — focus a member first:

```bash
ctac prj set-head mytac base.ua.split:assert_01.tac
ctac smt mytac --plain
```

Typical pipeline:

```bash
ctac prj init f.tac -o mytac --plain         # HEAD = base.tac (source: f.tac)
ctac rw mytac --plain                        # HEAD -> base.rw.tac
ctac ua mytac --strategy split --plain       # HEAD -> base.rw.ua.split/
ctac prj list mytac base.rw.ua.split --plain # show members + hint
ctac prj set-head mytac base.rw.ua.split:assert_01.tac --plain
ctac smt mytac --plain                       # writes assert_01.smt2
```

Other commands (`stats`, `cfg`, `search`, `slice`, `df`, `types`,
`run`, `cfg-match`, `bb-diff`, `op-diff`, `split-crit`, `absint`,
`rw-eq`) still take an explicit TAC path; routing them through
the project is on the follow-up list.

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
