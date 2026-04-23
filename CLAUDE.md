@AGENTS.md

# Contributing to ctac

Guidelines for human and AI contributors. AGENTS.md (above) is the
structured CLI reference for agent use; the rest of this file is the
contribution contract.

## Quickstart

```bash
python3.14 -m venv .venv
.venv/bin/pip install -e ".[dev]"
.venv/bin/pytest -q              # tests must be green
.venv/bin/ruff check src tests   # lint must be clean
```

Both must be green before you commit.

## Scope discipline

- Design observations are questions, not authorizations. Before
  adding a new rewrite rule, CLI flag, module, or pass the user
  didn't explicitly ask for, confirm first.
- Fix the bug in front of you; don't bundle adjacent cleanup. A bug
  fix commit contains the fix and its test, nothing else.
- No hypothetical error paths — validate at system boundaries (CLI
  inputs, external formats), trust internal invariants elsewhere.
- No placeholder / half-finished abstractions, no feature-flag-gated
  dead code, no `TODO:` notes for later. Remove until the real need
  arrives.

## Code style

- Prefer editing existing files over creating new ones. Only add a
  file when the new surface is genuinely distinct.
- No emojis in code or docs unless the user explicitly requests
  them.
- Default to no comments. Write WHY for non-obvious invariants and
  workarounds; don't write WHAT — well-named identifiers cover that.
  Don't mention the current ticket / PR / commit in comments; those
  references belong in the commit message and rot in source.

## Rewrite rules

`claude/CLAUDE.md` holds rule-writing conventions (LHS reuse for
havoc rewrites, `T` prefix for fresh vars, gate on `at_cmd_top()`).
If you change a rule's soundness argument, update the matching
`*_validation.py` sibling so `ctac rw-valid` stays in sync.

## CLI conventions

- New commands sit under the appropriate `rich_help_panel` panel
  constant in `src/ctac/tool/cli_runtime.py` (INSPECT / COMPARE /
  ANALYZE / TRANSFORM / VERIFY / VALIDATE).
- Prefer short command names (`rw-valid`, `ua`, `pp`, `cfg`). Full
  spellings live in `--help` prose, not the invocation.
- Every command exposes `--agent` (terse, agent-oriented) and
  `--help` (full reference) via `agent_option()`. Keep the docstring
  one line; put examples and longer prose in the `--help` epilog so
  they stay visible after the options panel.
- `--plain` is the agent / scripting mode. Commands should produce
  deterministic, ASCII-only output under it.
- Reuse `FILTER_*_HELP` constants for the shared CFG-slice filters.
  Don't invent parallel flag names.
- Choice-valued flags get `autocompletion=complete_choices([...])`
  (or a dedicated completer); dynamic ones pull from a live registry
  so they don't go stale.

## Testing

- New CLI commands: add `tests/test_<name>.py` with
  `typer.testing.CliRunner` invocations. Pin the interesting rows,
  not the full console text.
- New analyses / rewrite rules: unit-test the pure function plus a
  small synthetic TAC end-to-end.
- Real-target regression pins (e.g. `examples/kev-flaky/`) are
  welcome when they guard an investigation-worthy regression.

## Commits

- One logical change per commit. Tests + docs that belong to a
  feature go in the same commit as the feature; unrelated cleanup
  gets its own.
- Title: imperative mood, ≤72 chars. Body explains the *why* —
  problem, chosen approach, alternatives rejected.
- Keep messages generic. Don't quote private test data, internal
  corpus names, or customer identifiers.
- Never skip hooks (`--no-verify`), bypass signing, or force-push to
  `main` without explicit sign-off.
- Create new commits rather than amending. A failed pre-commit hook
  means the commit didn't happen; fix and re-commit, don't `--amend`
  (that would touch the previous commit).

## Documentation

- **README** is the map, not the manual. Commands grouped by
  purpose, 2–3 example invocations each; flag-level detail lives in
  `--help`.
- **`--help` epilog** carries the usage examples and the detailed
  prose (renders after the options panel, stays visible).
- **`--agent` guide** is per-command terse agent-oriented guidance
  with "why beat manual" framing.
- **AGENTS.md** is the structured CLI reference for agents and
  scripting.
- **`claude/CLAUDE.md`** is subdirectory-specific (rewrite rule
  conventions live there).

## AI collaboration

- Use of generative-AI coding tools is expected and welcomed. Tag
  your commits with the appropriate trailer (`Co-Authored-By:` for
  Claude Code, `Made-with:` for Cursor, or your tool's convention).
- Design decisions, scope control, and final review are human
  responsibilities. AI output must be reviewed and committed by a
  human.
- Aggregate credit lives in README's Authors section; per-change
  attribution lives in the git trailers — don't duplicate the list
  in prose, it rots.
