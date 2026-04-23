from __future__ import annotations

import os
import sys
from typing import Any

import typer
from rich.console import Console

from ctac.ast.highlight import TAC_THEME

_MAIN_EPILOG = (
    "[bold green]What is TAC?[/bold green]  Three-address code — the "
    "intermediate form Certora produces on the way to SMT. [bold]ctac[/bold] "
    "parses it and exposes structural, semantic, and solver-backed views, "
    "saving you from grepping raw dumps.\n\n"
    "[bold green]Typical pipeline[/bold green]  [cyan]ctac stats f.tac[/cyan] → "
    "[cyan]ctac rw f.tac -o opt.tac[/cyan] → "
    "[cyan]ctac ua opt.tac -o sa.tac[/cyan] → "
    "[cyan]ctac smt sa.tac --run[/cyan]\n\n"
    "[bold green]Compare two builds[/bold green]  "
    "[cyan]ctac op-diff a.tac b.tac[/cyan] for a per-stat frequency delta "
    "(fastest way to spot encoder drift between Prover versions); "
    "[cyan]ctac cfg-match[/cyan] + [cyan]ctac bb-diff[/cyan] for block-level "
    "structural / semantic diffs.\n\n"
    "[bold green]Accepted inputs[/bold green]  [bold].tac[/bold], "
    "[bold].sbf.json[/bold], or a Certora output directory (auto-resolves "
    "to [cyan]<dir>/outputs/*.tac[/cyan]).\n\n"
    "[bold green]Shell completion[/bold green]  One-time setup for tab "
    "completion of commands, subcommands, and flag values:\n\n"
    "[cyan]ctac --install-completion[/cyan]"
    "  [dim]# auto-detects zsh / bash / fish / powershell; restart shell after[/dim]\n\n"
    "[cyan]ctac --show-completion[/cyan]"
    "  [dim]# print the script without installing (inspect / source manually)[/dim]\n\n"
    "[bold green]Drill down[/bold green]  Run [cyan]ctac <command> --help[/cyan] "
    "for per-command examples and full flag reference, or "
    "[cyan]ctac [--agent|<command> --agent][/cyan] for terse agent-oriented guidance."
)


app = typer.Typer(
    no_args_is_help=True,
    # Typer auto-registers ``--install-completion`` and ``--show-completion``
    # so users can wire shell completion with a single one-time command
    # (see the epilog for instructions).
    add_completion=True,
    rich_markup_mode="rich",
    help=(
        "[bold]ctac[/bold] — inspect, analyze, transform, and verify Certora TAC."
    ),
    epilog=_MAIN_EPILOG,
)


INSPECT_PANEL = "Inspect"
COMPARE_PANEL = "Compare two builds"
ANALYZE_PANEL = "Analyze data-flow"
TRANSFORM_PANEL = "Transform TAC"
VERIFY_PANEL = "Verify"
VALIDATE_PANEL = "Validate the rewriter"

_AGENT_GUIDE_MAIN = """ctac agent guide (plain, terse)

WHAT: ctac parses Certora TAC (three-address code) and SBF outputs so you
can reason about block structure, control flow, data flow, expressions,
and VC generation — semantically, not via grep over the raw dump.

WHY USE IT OVER MANUAL APPROACHES:
- Saves tokens: emits only the slice you ask for (`--from/--to/--only`
  instead of dumping every block). One command often replaces a chain of
  grep/sed that would take many context-budget-heavy tool calls.
- Prevents errors: the slicer understands CFG reachability, the
  data-flow analyses check DSA/liveness correctness, the SMT encoder
  produces provably-sound VCs. Ad-hoc regex will silently miss cases.
- Deterministic, copy-paste-friendly plain output with `--plain`.

CANONICAL WORKFLOWS:
- Unknown file, first look: `ctac stats <path> --plain`.
- Block-level code review: `ctac pp <path> --from A --to B --plain`.
- CFG reasoning: `ctac cfg <path> --style edges --from A --to B --plain`.
- Find patterns: `ctac search <path> <regex> --plain` (alias: `grep`).
- Data-flow triage: `ctac df <path> --plain`.
- Compare two builds: `ctac op-diff a.tac b.tac` for per-stat frequency
  delta; `ctac cfg-match` then `ctac bb-diff` for block-level diffs.
- Replay a z3 model: `ctac run <path> --model M --trace --plain`.
- Simplify TAC: `ctac rw <path> --plain`.
- Multi-assert to single-assert: `ctac ua <path> -o out.tac`.
- SMT VC dump: `ctac smt <path> --plain` (add `--run` to invoke z3).
- Rewrite-rule soundness: `ctac rw-valid -o DIR`.

ACCEPTED INPUTS: `.tac`, `.sbf.json`, or a Certora output directory
(auto-resolves to `<dir>/outputs/*.tac`).

ALWAYS: pass `--plain` for deterministic, ASCII-only output the agent
can parse reliably. Environment `CTAC_PLAIN=1` or `NO_COLOR=1` works too.

DISCOVERY: every subcommand has its own `--agent` guide (how to use it)
and `--help` (full flag reference). Run `ctac <subcmd> --agent` first
before building complex pipelines — the per-command guide explains when
that tool beats manual alternatives and names the typical flag combos.
"""

_AGENT_GUIDE_BY_CMD: dict[str, str] = {
    "stats": """ctac stats --agent

FIRST LOOK on any unknown TAC/SBF file. One-shot sanity check.

WHY BEAT MANUAL: `wc -l` tells you lines; this tells you what matters
(block count, command count per kind, top-N dense blocks, expression op
frequencies, non-linear mul/div counters, bytemap/memory capability).
Saves multiple grep passes and gives you a complexity budget for
downstream work.

TYPICAL:
  ctac stats f.tac --plain                      # full stats
  ctac stats f.tac --plain --top-blocks 0 --no-by-cmd-kind   # compact
  ctac stats <certora-output-dir> --plain        # auto-resolves a .tac

WATCH: `memory.capability` — if `bytemap-rw`, ctac smt will reject; if
`bytemap-ro`, sea_vc needs the memory range axiom (already emitted).
""",
    "parse": """ctac parse --agent

Same output as `ctac stats`. Use when you want to emphasize the
parse-error path (a failing `ctac parse` means the TAC doesn't round-trip).
If you're just exploring, prefer `stats`.
""",
    "cfg": """ctac cfg --agent

Control-flow only, no command listings. Use to reason about reachability,
branch structure, and block-id topology.

WHY BEAT MANUAL: regex over `Block <id> Succ [<list>]` is brittle
(multi-line blocks, nested braces, comments). The CFG view is parsed
and filtered semantically — `--from A --to B` keeps blocks on some path
from A to B (intersection with other filters via AND).

STYLES:
  --style goto     # block label + `goto <succ>` — default, block-oriented
  --style edges    # one `src -> dst` line per edge — grep-friendly
  --style dot      # Graphviz digraph — pipe to `dot -Tpng` for a picture

TYPICAL:
  ctac cfg f.tac --plain --style edges --from entry --to assert_block

FILTERS: `--from/--to/--only/--id-contains/--id-regex/--cmd-contains/
--exclude` all combine with AND. For CFG reasoning prefer `edges` +
`pp` output, not rendered images.
""",
    "pp": """ctac pp --agent

Block-level TAC reading with humanized expressions (bitfield slices
rewritten as `X[lo..hi]`, shifted masks normalized, etc.).

WHY BEAT MANUAL: raw TAC RHS is `Mul(Mod(Div(X 0x400) 0x100) 0x400)`;
pp shows that as `X[10..17]`. When reading TAC by hand, the humanized
form typically cuts a 3-5x readability overhead.

TYPICAL:
  ctac pp f.tac --plain --from A --to B           # slice on a CFG path
  ctac pp f.tac --plain --only blk1,blk2          # specific blocks
  ctac pp f.tac -o out.htac                       # write .htac (pp text)

FILTERS: identical shape to `ctac cfg`. Combine with `--cmd-contains`
to zero in on assumes/asserts involving a symbol.
""",
    "search": """ctac search --agent

Pattern search inside parsed TAC commands (regex by default; `--literal`
for substring). Works on `.tac` and `.sbf.json`.

WHY BEAT MANUAL grep: regex matches are anchored to one command at a
time (no cross-command false positives), respect block structure, and
honor the same `--from/--to/--only` filters as `pp`/`cfg`. `--count`
and `--blocks-only` keep output compact.

PRINTER DEFAULT: `--printer auto` is the default. Under `--plain` it
picks `raw` so TAC operator names (`BWAnd`, `Mod`, `Select`,
`safe_math_narrow_bv256:bif`, ...) match as typed — the `human`
printer would rewrite them into slice/mod syntax and silently return
0 matches. Without `--plain`, it picks `human` for readable output.

DESIGN: search matches against exactly the text it shows you — no
hidden discrepancy between "what's searched" and "what's displayed".
Under `--plain`, both are raw TAC, so `grep` and `ctac search` stay
interchangeable (you can mix them in one pipeline). Without `--plain`,
both are humanized so interactive "find" and "read" line up.

TYPICAL:
  ctac search f.tac 'BWAnd' --plain --count              # count op usage
  ctac search f.tac 'BWAnd' --plain --count -q           # pipeable, no `#` header
  ctac search f.tac 'BWAnd' --plain -C 2                 # grep-style context lines
  ctac search f.tac '0x[0-9a-f]+' --plain --count-by-match  # frequency table
  ctac search f.tac 'if \\(R[0-9]+\\) < \\\\1' --plain   # tautological self-compare
  ctac search f.tac 'assume.*\\[2\\^64' --plain --count  # range-guard hits
  ctac search f.tac Eq --plain --literal                 # substring

ALIAS: `ctac grep` accepts the same flags. Useful when thinking in
`grep` terms out of habit.
""",
    "grep": """ctac grep --agent

Alias of `ctac search`. Same flags, same semantics. Use whichever name
is ergonomic.
""",
    "cfg-match": """ctac cfg-match --agent

Coarse block correspondence between two builds (TAC vs TAC, or
.sbf.json vs .sbf.json). Output: `left_id  right_id  score`.

WHY BEAT MANUAL: eyeballing two CFGs for drift is O(N^2) and token-
expensive. cfg-match scores pairs by command+constant signature so you
see which blocks moved vs really changed. Pair with bb-diff for
command-level deltas.

TYPICAL:
  ctac cfg-match a.tac b.tac --plain --const-weight 0.2
  ctac cfg-match a.tac b.tac --plain --min-score 0.6   # only strong pairs

TUNING: raise `--const-weight` when constants are strong anchors;
raise `--min-score` to cut noisy low-confidence matches.
""",
    "bb-diff": """ctac bb-diff --agent

Semantic per-block diff between matched blocks from two builds.

WHY BEAT MANUAL: a raw `diff a.tac b.tac` is useless (DSA-renaming
makes every line look different). bb-diff runs cfg-match first, then
normalizes variable names and shows only substantive deltas.

TYPICAL:
  ctac bb-diff a.tac b.tac --plain --drop-empty --max-diff-lines 120
  ctac bb-diff a.tac b.tac --plain --const-weight 0.2 --normalize-vars

KEY FLAGS: `--drop-empty` hides blocks that are identical, `--context N`
shows N lines of unchanged context, `--normalize-vars` (default) maps
DSA-renamed regs to canonical names before diffing.
""",
    "op-diff": """ctac op-diff --agent

Per-stat frequency delta between two TAC files. Parses each side,
runs the `ctac stats` collector, and prints the differences grouped
by section (`expression_ops`, `command_kinds`, `memory`, etc.).

WHY BEAT MANUAL: `diff <(ctac stats a.tac) <(ctac stats b.tac)` is
possible but noisy — block-id renumbering and file-path lines dominate
the output. op-diff filters to only the stats that actually changed.
Dedicated command so you never have to reach for the shell pipeline
again.

TYPICAL:
  ctac op-diff a.tac b.tac --plain
  ctac op-diff a.tac b.tac --plain --show expression_ops
  ctac op-diff a.tac b.tac --json

WHEN TO USE: a user reports that verification got slower between two
Prover versions; `op-diff` surfaces the encoder-level differences in
one shot (fewer Mods, more BWAnds, extra commands, symbol-table
growth). Much faster than hand-comparing `ctac stats` outputs.
""",
    "df": """ctac df --agent

TAC data-flow analyses: def-use, liveness, DCE, use-before-def, DSA
validation, control-dependence, useless-assume elimination.

WHY BEAT MANUAL: these analyses encode concrete program semantics
(liveness is a fixed-point; DSA-static vs DSA-dynamic partitions matter
for rw correctness). Computing them by eye is error-prone and
token-expensive.

TYPICAL:
  ctac df f.tac --plain                                # summary, all modes
  ctac df f.tac --plain --show dce --details           # only DCE, detailed
  ctac df f.tac --plain --show dsa                     # validate DSA form
  ctac df f.tac --plain --json                         # machine-readable

WATCH: `dsa.status: invalid` means sea_vc will reject the program.
Check this before running `ctac smt` on a suspected-broken TAC.
""",
    "rw": """ctac rw --agent

TAC -> TAC simplification: div/bitfield/ite rewrites + iterated DCE,
optional div purification (R4a) and bool-name purification
(PURIFY_ASSERT, ITE_PURIFY).

WHY BEAT MANUAL: the simplification pipeline is a proven set of
algebraic identities (see `ctac rw-valid`). Hand-simplifying TAC by
editing registers is a soundness risk and token-expensive. rw produces
a smaller, more solver-friendly program in one pass.

TYPICAL:
  ctac rw f.tac --plain --report                   # stdout pp + rule hits
  ctac rw f.tac -o small.tac --plain               # write a round-trippable .tac
  ctac rw f.tac -o small.htac --plain              # write pretty-printed (.htac)
  ctac rw f.tac --no-purify-div --plain            # disable R4a

PIPELINE: always runs simplify_pipeline (R1-R4, N1-N4, Ite/Bool, CSE,
CP). `--purify-div` adds R4a (default on), `--purify-ite` runs a post-DCE
phase to name Ite conditions (default on). Check `--report` for which
rules fired and how often.
""",
    "rw-valid": """ctac rw-valid --agent

Emit per-rule SMT-LIB soundness scripts. One `.smt2` per registered
validation case + `manifest.json` into the output directory. Does NOT
invoke z3 itself — the user drives the solver (possibly with custom
tactics or Lean) and inspects results.

WHY BEAT MANUAL: rewrite-rule soundness is easy to get wrong on paper
(R4, R4a, R6 are algebraic — off-by-one in a ceil formula silently
changes semantics). rw-valid produces a human-auditable .smt2 per rule
so the claim can be z3-discharged, inspected, and version-controlled.

TYPICAL:
  ctac rw-valid -o /tmp/rwv --plain                # emit all specs
  ctac rw-valid -o /tmp/rwv --rule R4a --plain     # one rule only
  for f in /tmp/rwv/*.smt2; do z3 "$f"; done       # run them

EXPECTED: `unsat` on every script means the rule is sound. `sat` is a
counterexample (bug). `unknown` means escalate (tactics, Lean).
Currently covers R4, R4a, R6 (9 cases); other rules are listed under
`manifest.json`:`missing`.
""",
    "run": """ctac run --agent

Concrete TAC interpreter. Executes deterministically, optionally
replaying havoc values from a model and/or comparing against a
reference.

WHY BEAT MANUAL: simulating TAC by hand means tracking DSA renames,
havoc semantics, and assume-fail vs assert-fail (they behave
differently! assume-fail stops silently, assert-fail continues). The
interpreter gets those right and emits a per-instruction trace.

TYPICAL:
  ctac run f.tac --plain                           # zero-havoc run
  ctac run f.tac --model m.txt --plain --trace     # replay a z3 model
  ctac run f.tac --model m.txt --validate --plain  # compare against model
  ctac run dir/ --plain                            # auto-resolve .tac + model

INPUTS: `--model` accepts both TAC-format models (from `ctac smt
--model`) and raw SMT-LIB models (z3 stdout). Bytemap entries in both
formats load into memory for `Select` lookups.

STATUS CODES: 0 ok, 2 assume-failed/stopped, 3 error/max_steps.
""",
    "smt": """ctac smt --agent

Emit an SMT-LIB VC from loop-free single-assert TAC. Default encoding
is `sea_vc` (QF_UFNIA, DSA + reachability).

WHY BEAT MANUAL: hand-writing a VC for a TAC program is error-prone
(DSA renaming, block guards, bv256 domain constraints, bytemap-as-UF
with range axiom). sea_vc guarantees a sound encoding; the emitted
script is directly z3-runnable.

TYPICAL:
  ctac smt f.tac --plain                           # print SMT-LIB
  ctac smt f.tac --plain -o out.smt2               # write file
  ctac smt f.tac --plain --run                     # invoke z3
  ctac smt f.tac --plain --run --model m.txt       # write TAC-format model
  ctac smt f.tac --plain --run --unsat-core        # name asserts, print core

PRECONDITIONS: exactly one `AssertCmd` (run `ctac ua` first if you
have multiple); loop-free; bytemap usage must be `bytemap-free` or
`bytemap-ro` (run `ctac stats` to check).

Z3 KNOBS: `--timeout` (seconds), `--seed`, `--tactic`,
`--z3-args "<raw>"`. Use `--debug` to see z3 stdin/stdout and a
replayable command line.
""",
    "ua": """ctac ua --agent

Uniquify assertions: fold every `AssertCmd` into a single `__UA_ERROR`
block so the output satisfies `ctac smt`'s one-assert precondition.

WHY BEAT MANUAL: multi-assert TAC can't go through `ctac smt` directly.
Rewriting by hand (splitting blocks, redirecting asserts, threading the
predicate as an assume into the continuation) is fiddly; ua does it in
one pass with PURIFY_ASSERT + `remove_true_asserts` preprocessing built
in. Each assertion's predicate is used verbatim — no inversion.

TYPICAL:
  ctac ua f.tac -o f_ua.tac --plain                # merge, write .tac
  ctac ua f.tac -o f_ua.tac --plain --report       # merge + counts

PIPELINE: drops `assert true`, purifies compound predicates into fresh
`TA<N>:bool` vars, then merges. Single-assert input is a no-op
(`was_noop: true`).

FOLLOWUP: `ctac smt f_ua.tac --run` to verify.
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


# --- shell-completion helpers -------------------------------------------------
# Typer calls these during tab-completion; they return a list of candidate
# values (optionally ``(value, help)`` tuples). Each helper is a tiny factory
# so the command definition only needs ``autocompletion=complete_*()``.

def complete_choices(values: list[str]):
    """Return a Typer autocompletion function that yields a fixed list."""
    vals = list(values)

    def _complete(incomplete: str):
        return [v for v in vals if v.startswith(incomplete)]

    return _complete


def complete_rule_names():
    """Tab-complete rule names for ``ctac rw-valid --rule``."""
    def _complete(incomplete: str):
        # Local import to avoid a cycle during module init.
        from ctac.rewrite.rules import validation_cases
        names = sorted({vc.name for vc in validation_cases})
        return [n for n in names if n.startswith(incomplete)]

    return _complete


def complete_smt_encodings():
    """Tab-complete encoding names for ``ctac smt --encoding``."""
    def _complete(incomplete: str):
        from ctac.smt.encoding import available_encodings
        names = sorted(available_encodings())
        return [n for n in names if n.startswith(incomplete)]

    return _complete

# CFG slicing filter help strings. Reused across cfg / pp / search / df.
FILTER_FROM_HELP = (
    "Keep only blocks reachable from NBID (successor cone). Combines with "
    "--to via AND."
)
FILTER_TO_HELP = (
    "Keep only ancestors of NBID (predecessor cone). Combines with --from "
    "via AND; together they give the slice on some path from --from to --to."
)
FILTER_ONLY_HELP = (
    "Comma-separated explicit block-id whitelist. Only these blocks survive."
)
FILTER_ID_CONTAINS_HELP = (
    "Substring match on block ids. Keeps blocks whose id contains this."
)
FILTER_ID_REGEX_HELP = (
    "Regex match on block ids. Keeps blocks whose id matches the pattern."
)
FILTER_CMD_CONTAINS_HELP = (
    "Keep only blocks that have at least one command containing this substring."
)
FILTER_EXCLUDE_HELP = (
    "Comma-separated block-id blacklist. These blocks are dropped after "
    "other filters apply."
)
