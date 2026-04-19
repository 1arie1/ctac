from __future__ import annotations

import os
import sys
from typing import Any

import typer
from rich.console import Console

from ctac.ast.highlight import TAC_THEME

app = typer.Typer(no_args_is_help=True, add_completion=False)

_AGENT_GUIDE_MAIN = """ctac agent guide (plain, terse)

Use ctac when you need TAC-aware structure, not raw text scraping.
Key use-cases:
- Fast sanity: `ctac stats <file(.tac|.sbf.json)> --plain`
- Slice/control-flow: `ctac cfg|pp <file(.tac|.sbf.json)> --from A --to B --plain`
- Cross-build drift: `ctac cfg-match` then `ctac bb-diff`
- Concrete replay/model checks: `ctac run --model ... --trace --plain`
- Pattern mining in commands: `ctac search <file> <pattern> --plain`
- SMT VC dump (assert-failure query): `ctac smt <file> --plain`

Why better than plain text tools:
- Parses TAC structure (blocks, commands, CFG), so filters are semantic.
- Handles block/path slicing directly (`--from/--to/--only/...`).
- Produces deterministic, grep-friendly plain output.

If you must use plain text tools first, start from `ctac pp --plain` output.
If functionality is missing, say it explicitly and request the exact feature.
"""

_AGENT_GUIDE_BY_CMD: dict[str, str] = {
    "stats": """ctac stats --agent

Use for quick TAC sanity and complexity triage.
Gives: block/command/meta counts, command-kind counts, top dense blocks,
expression op frequencies, and non-linear mul/div counters.
Start here on unknown files.
""",
    "parse": """ctac parse --agent

Same output shape as `ctac stats`.
Use when you want an explicit parse-oriented entrypoint.
""",
    "cfg": """ctac cfg --agent

Use for control-flow only.
Best flags: `--style edges --from A --to B --plain`.
Use `--only`/`--id-*`/`--exclude` to narrow scope.
""",
    "pp": """ctac pp --agent

Use for block-level TAC reasoning with humanized commands.
Best flags: `--from A --to B --plain`.
If external text tooling is needed, use `ctac pp --plain` as the source.
""",
    "search": """ctac search --agent

Use to find command patterns in parsed TAC/SBF blocks.
Defaults to regex; use `--literal` for substring.
Useful: `--blocks-only`, `--count`, `--max-matches`, and path filters.
Alias: `ctac grep`.
""",
    "grep": """ctac grep --agent

Alias of `ctac search`.
Use exactly like `search`; defaults to regex.
""",
    "cfg-match": """ctac cfg-match --agent

Use for coarse block mapping between two TACs (or two `.sbf.json` files).
Run before `bb-diff` to understand structural correspondence.
Tune with `--const-weight` and `--min-score`.
""",
    "bb-diff": """ctac bb-diff --agent

Use for semantic deltas in matched basic blocks (TAC or `.sbf.json`).
Typical: `--drop-empty --normalize-vars --max-diff-lines N --plain`.
Run after `cfg-match`.
""",
    "run": """ctac run --agent

Use for concrete execution/replay.
Model replay: `--model ... --trace --plain`.
Validation mode: add `--validate`.
Use `--fallback` only with `--model`.
""",
    "smt": """ctac smt --agent

Use for SMT-LIB VC generation from loop-free TAC.
Preconditions: exactly one `AssertCmd`, and it must be last in its block.
Current semantics: SAT iff a failing assertion is reachable.
Solver mode: add `--run` to invoke z3, and `--model <path>` to write SAT model in TAC format.
Unsat cores: `--unsat-core` names TAC asserts and appends `(get-unsat-core)`; with `--run`, prints the core on `unsat`. Do not combine with `--model`.
Z3 knobs: `--timeout` (seconds), `--seed`, `--tactic`, `--z3-args`.
Debugging: add `--debug` to print z3 stdin/stdout/stderr and a replayable shell command.
Default encoding: `sea_vc`; set with `--encoding`.
Alternative: `vc-path-predicates` for the QF_BV path-predicate encoding.
""",
}


def _agent_guide_text(ctx: typer.Context | None) -> str:
    if ctx is None:
        return _AGENT_GUIDE_MAIN
    path = (ctx.command_path or "").strip().split()
    cmd = path[-1] if path else "ctac"
    return _AGENT_GUIDE_BY_CMD.get(cmd, _AGENT_GUIDE_MAIN)


def _agent_callback(ctx: typer.Context, _param: Any, value: bool) -> bool:
    if not value:
        return value
    guide = _agent_guide_text(ctx).rstrip()
    path = (ctx.command_path or "").strip().split()
    if not path:
        help_cmd = "ctac --help"
    elif len(path) == 1:
        help_cmd = "ctac --help"
    else:
        help_cmd = f"ctac {path[-1]} --help"
    print(f"{guide}\n\nNeed full flag reference? run: {help_cmd}\n")
    raise typer.Exit(0)


def agent_option() -> Any:
    return typer.Option(
        False,
        "--agent",
        help="Show terse agent-focused usage guidance and exit.",
        is_eager=True,
        callback=_agent_callback,
    )


@app.callback(invoke_without_command=True)
def _app_callback(
    ctx: typer.Context,
    agent: bool = agent_option(),
) -> None:
    _ = (ctx, agent)


def console(plain: bool) -> Console:
    force_terminal = False if plain else None
    return Console(
        force_terminal=force_terminal,
        no_color=plain or bool(os.environ.get("NO_COLOR")) or not sys.stdout.isatty(),
        highlight=False,
        theme=TAC_THEME,
    )


def plain_requested(plain: bool) -> bool:
    return plain or os.environ.get("CTAC_PLAIN", "").lower() in ("1", "true", "yes")


PATH_KW = dict(exists=True, dir_okay=True, readable=True)
PLAIN_HELP = "Plain text only (no Rich styling); also set CTAC_PLAIN=1 or NO_COLOR."
