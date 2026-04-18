# AGENTS.md

Use `ctac` in plain mode unless color is required.

## Quick Rules

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
- For cross-build comparison, use `cfg-match` then `bb-diff`.
- For CFG reasoning, prefer structured text (edges + block summaries), not images.

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
  - `--style goto|edges`
  - Same filters as `pp`.

- `ctac search <file> <pattern> --plain` (alias: `ctac grep`)
  - Search command lines in TAC blocks (regex by default; use `--literal` for substring).
  - Useful flags:
    - `--blocks-only`
    - `--count`
    - `--max-matches <n>`
  - Supports same structural filters as `pp` (`--from/--to/--only/...`).
  - Useful analysis examples:
    - `ctac search f.tac 'if (R[0-9]+) < \1' --plain --regex`
      - Finds tautological-false self-compare candidates (optimization opportunities).
    - `ctac search f.tac 'if .* == .* \{ 1 \} else \{ 0 \}' --plain --regex`
      - Finds bool-temp equality checks often followed by `assume ... == 1` (canonicalization opportunities).
    - `ctac search f.tac 'assume R[0-9]+ <= \[2\^64-1\]' --plain --count --from <a> --to <b>`
      - Quantifies repeated range guards inside a path slice.

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
  - Emit SMT-LIB VC (default encoding: `sea_vc`).
  - Alternative encoding: `--encoding vc-path-predicates` (QF_BV path-predicate style).
  - Current preconditions: loop-free TAC, exactly one `AssertCmd`, and assert must be last in its block.
  - VC semantics: SAT iff assertion-failure state is reachable.

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

- Compare two programs:
  1. `ctac cfg-match a.tac b.tac --plain --const-weight 0.2`
  2. `ctac bb-diff a.tac b.tac --plain --const-weight 0.2 --drop-empty --max-diff-lines 120`
  3. Raise `--const-weight` if symmetric blocks are cross-matched.

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
