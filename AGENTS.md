# AGENTS.md

Use `ctac` in plain mode unless color is required.

## Quick Rules

- Prefer `--plain` for deterministic output.
- First step on unknown file: `ctac stats <file> --plain`.
- `ctac stats` now includes command-kind counts and top blocks by default.
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
