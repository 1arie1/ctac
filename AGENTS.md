# AGENTS.md

Use `ctac` in plain mode unless color is required.

## Quick Rules

- Prefer `--plain` for deterministic output.
- First step on unknown file: `ctac stats <file> --plain`.
- If parse fails with `Missing line 'Program {'`, input is not a full `.tac` file.
- For focused views, use `pp`/`cfg` with `--from` and `--to`.
- For cross-build comparison, use `cfg-match` then `bb-diff`.

## Core Commands

- `ctac stats <file> --plain`
  - Cheap sanity: blocks, commands, metas.

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
