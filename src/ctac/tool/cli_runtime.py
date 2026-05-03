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
    "completion of commands, subcommands, flag values, and "
    "[cyan]ctac search[/cyan]'s pattern positional (TAC operator names "
    "— BWAnd, Mod, Select, safe_math_narrow_bv256:bif, AssignExpCmd, ...):\n\n"
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
PROJECT_PANEL = "Manage a project"

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
- Find / count / context: `ctac search <path> <regex> --plain` — alias
  `ctac grep`. `-C N` for grep-style context, `--count-by-match` for a
  frequency table of distinct values, `-q` for pipeable output (no `#`
  preamble). Pattern tab-completes to TAC operator names.
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
  --style dot      # Graphviz digraph — pipe to `dot -Tsvg` for a picture
  --style blocks   # one block id per line, no preamble — for shell loops

TYPICAL:
  ctac cfg f.tac --plain --style edges --from entry --to assert_block
  for b in $(ctac cfg f.tac --plain --style blocks); do
      ctac search f.tac BWAnd --plain -q --only $b
  done

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
    "slice": """ctac slice --agent

Backward static slice through data and control dependences. Pure
display filter (slices need not be encodable). Output is valid htac
so the VSCode plugin renders it; for analysis, prefer `ctac sem-slice`
(separate command, when available).

WHY BEAT MANUAL: tracing `B1054` back through `Le(R618 R1053)` -> ...
-> `Select(M1031 0x...)` -> the bytemap `Store` chain by hand is
tens of `grep` invocations. `slice` follows the def-use closure plus
control dependence in one pass.

CRITERION FORMS:
  SYM            every def of canonical SYM (in DSA, usually one
                 point; for dynamic registers, all sibling defs)
  SYM@BLK        the def(s) of SYM in block BLK (disambiguates
                 dynamic registers)
  BLK:assert     the last AssertCmd in BLK
  BLK            every cmd in BLK as a seed

We deliberately do NOT expose `BLK:IDX` — annotations occupy command
slots, so cmd indices are unstable for users. Use SYM/SYM@BLK.

TYPICAL:
  ctac slice f.tac -c B1054 --plain                    # full backward slice
  ctac slice f.tac -c B1054 --no-control --plain       # data-only chain
  ctac slice f.tac -c 19_1_0_0_0_0:assert --plain      # from the assert
  ctac slice f.tac -c R10@5_2_0 -c R11@7_0_1 --plain   # multi-seed
  ctac slice f.tac -c M1031 --show stats --plain       # bytemap heat-map
  ctac slice f.tac -c B1054 --depth 1 --plain          # one hop only

OUTPUT MODES (`--show`):
  pp     sliced htac (default; readable, valid htac)
  points machine-friendly `BLK:cmd_idx` lines
  stats  selected_cmds / total_cmds / rounds
  json   full SliceResult

`--mark drop` (default) hides non-selected cmds; `elide` collapses
into `...`; `gray` keeps them as `# ` prefixed comments under --plain.

FILTERS: same `--from/--to/--only/...` shape as `pp`/`cfg`. They
pre-scope the program before the slice runs (helpful on 30k-line dumps).
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

KEY FLAGS (each replaces a shell-pipeline workflow):

  --count-by-match   Frequency table of distinct matches (sorted desc
                     by count, then alphabetic). If the regex has a
                     capture group, the first group is the tally key;
                     otherwise the whole match is. Replaces
                     `| grep -oE ... | sort | uniq -c | sort -rn`.

  -C N / -B N / -A N Grep-style context lines within the same block.
                     Match rows keep `:` separator, context rows use
                     `-`, non-adjacent hit groups get a `--` separator.
                     Context never crosses block boundaries. Replaces
                     `| awk '/Block N/,/Block M/' | grep -C`.

  -q / --quiet       Suppress the `#`-prefixed preamble + footers so
                     the output is just numeric results, tally rows, or
                     block ids. Pair with `--count` for a two-line
                     result that `awk '/^matches:/ {print $2}'` parses.
                     Replaces `| tail -2 | head -1 | awk '{print $2}'`.

  --pattern <TAB>    With shell completion installed, the pattern
                     positional tab-completes to TAC operator names
                     (BWAnd, Mod, Select, safe_math_narrow_bv256:bif,
                     AssignExpCmd, ...). `ctac --install-completion`
                     once; then `ctac search f.tac B<TAB>`.

TYPICAL:
  ctac search f.tac 'BWAnd' --plain --count              # count op usage
  ctac search f.tac 'BWAnd' --plain --count -q           # pipeable, no `#` header
  ctac search f.tac 'BWAnd' --plain -C 2                 # grep-style context
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
    "absint": """ctac absint --agent

Abstract-interpreter-driven analyses over post-rewrite TAC. v1 exposes
polynomial degree (a stats case that ranks the program's non-linear
expressions). Most absint work supports other transformations; this
command surfaces the analyses with useful standalone reports.

WHY BEAT MANUAL: degree of every TAC variable falls out of a single
forward pass over the DSA, loop-free CFG; computing it by hand on a
medium-sized program is hopeless. The top-non-linear table points at
the multiply-divide chains and bitwise transforms that drive solver
cost — a cheap pre-flight before `ctac smt`.

TYPICAL:
  ctac absint f.tac --plain                            # summary
  ctac absint f.tac --plain --details                  # top non-linear table
  ctac absint f.tac --plain --details --min-degree 3   # cubic and up only
  ctac absint f.tac --plain --json                     # machine-readable

OUTPUT: `degree.distribution.deg_<k>` shows how many vars at each
degree; `degree.saw_top` flags any unrecognized operators (e.g. SBF
intrinsics not yet in the operator table — sound over-approximation).
""",
    "types": """ctac types --agent

Sound, possibly-incomplete kind inference for TAC registers. Lattice
`Top (= Int+Ptr) | Int | Ptr | Bot`. Pin every register to one of the
four kinds based on its structural use: index of `Select`/`Store` ->
Ptr; operand of `Mul`/`Div`/`IntMul`/`IntDiv`/`Shift*`/`BWXOr`/`BNot`
-> Int; `narrow` and `BWAnd`/`BWOr` with a constant operand are
identity (passthrough); `R = SymRef(R')` and `assume R == R'` unify
classes; `Add`/`IntAdd` of one Ptr and one Int is Ptr.

WHY BEAT MANUAL: the pointer / integer split is buried in the TAC
operator surface — you'd grep `Select` indices, then chase narrow /
copy-propagation chains by hand. `ctac types` runs a union-find +
lattice-meet to fixed point and tells you which registers are
provably pointers. Sound: it never claims `Int` for an actual pointer
or `Ptr` for an actual integer; abstains to `Top` when evidence is
insufficient.

TYPICAL:
  ctac types f.tac --plain                       # full table + counts
  ctac types f.tac --plain --show ptr            # only the pointer registers
  ctac types f.tac --plain --by-class            # grouped by union-find class
  ctac types f.tac --plain --json                # machine-readable
  ctac types f.tac --plain --trace - --trace-symbol R1015
                                                 # diagnose why R1015 is Top/Bot

INTERPRETATION: `Bot` is a classifier-flagged contradiction — a class
has structural evidence both for Ptr (used as index somewhere) and
Int (operand of Mul / Shift / etc.). Either the program is genuinely
ill-typed or two distinct values were canonicalized into the same
class by a copy/narrow chain that crosses kinds; both are sound
report-out values worth investigating. `Top` is "no commitment" —
sound to leave alone or to use as the polymorphic case for v2 region
refinement.

DIAGNOSE: `--trace PATH` writes a JSONL constraint-event log to PATH
(use `-` for stdout). One record per `meet` (constraint applied to a
class), `union` (two classes merged), and `rhs-eval` (per-AssignExpCmd
summary showing what the RHS evaluated to). Fields: `phase, iteration,
block_id, cmd_index, kind, rule, symbols, before, after, detail,
changed`. Filter to events on a specific class with `--trace-symbol
SYM[,SYM...]` (canonical names — DSA suffixes auto-stripped). For
"why is X `Top`?" the trace shows every constraint that touched X's
class and what kind it tried to apply; an empty trace means no rule
ever constrained X — sound, no structural use, defaults to Top.

DEFAULT: scalar symbols only. `--include-memory` adds the
`bytemap`/`ghostmap` rows (always Top in v1; the lattice is for
scalars).
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
  ctac rw f.tac --plain --report                   # stdout pp + per-rule hit counts
  ctac rw f.tac --plain --trace -                  # per-fire JSONL on stdout
  ctac rw f.tac --plain --trace fires.jsonl        # per-fire JSONL to file
  ctac rw f.tac -o small.tac --plain               # write a round-trippable .tac
  ctac rw f.tac -o small.htac --plain              # write pretty-printed (.htac)
  ctac rw f.tac --no-purify-div --plain            # disable R4a

PIPELINE: chain-recognition (R6) -> early CSE -> simplify_pipeline
(R1-R4, N1-N4, Ite/Bool, CP) -> DCE -> optional purify (ITE_PURIFY,
PURIFY_ASSERT, ...) -> late CSE -> CP cleanup -> DCE. CSE runs in its
own phases (never alongside rules that mutate registered RHSes) so
its per-iteration RHS index is a real snapshot. `--purify-div` adds
R4a (default on); `--purify-ite` enables the post-DCE phase (default
on).

INTROSPECTION: `--report` aggregates (which rules fired, how often,
plus DCE stats); `--trace` emits one JSONL record per fire (phase,
iteration, block_id, cmd_index, host_lhs, rule, before, after) so you
can see *where* a rule fired or confirm a missed-fire site. Rule-
driven phases only — DCE / ITE-purify restructuring / materialize-
assumes don't appear in the trace.
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
    "rw-eq": """ctac rw-eq --agent

End-to-end equivalence check between an orig TAC and its `ctac rw`
output. Emits one merged TAC where every site at which orig and rw
differ becomes an `assert (CHK<n>)`. Hand off the merged file to
`ua --strategy split` + `ctac smt --run`; every emitted assert
should discharge `unsat`. A `sat` is a real soundness bug in the
rwriter (rw-eq found one in CSE — alias source's def-block didn't
dominate the use site).

WHY BEAT MANUAL: hand-checking that `ctac rw`'s output preserves the
orig's semantics on a real-world TAC is impractical. rw-valid covers
per-rule soundness in isolation; rw-eq covers a specific (orig, rw)
pair — catches rule-interaction bugs that per-rule specs miss.

TYPICAL:
  ctac rw orig.tac -o rw.tac --plain
  ctac rw-eq orig.tac rw.tac -o eq.tac --plain --report
  ctac ua eq.tac --strategy split -o split --plain
  for f in split/*.tac; do ctac smt "$f" --plain --run --timeout 30; done
  # expect every line to be `unsat`. `sat` = soundness bug.

INPUTS CONTRACT: orig and rw must share block ids and successor
lists per block. Variable names are preserved; only rule 6 (rehavoc,
R4A pattern) mints fresh `X__rw_eq<n>` shadow vars.

WALKER RULES (code-execution order; first match wins):
  9   eos lhs                  R is None                       emit L,        advance L
  8   eos rhs                  L is None                       emit R,        advance R
  7   terminator               both at Jump/Jumpi (paired)     emit one,      advance both
  6   rehavoc window           L: X=e, R: havoc X              shadow window, advance both
  1   identical (non-assert)   cmd_equiv(L, R) and not Assert  emit L,        advance both
  2   same-lhs assignment      both AssignExp, same lhs        CHK + assert + L,                advance both
  5a  paired assumes           both AssumeExp                  CHK + assert + assume L [+ R],   advance both
  5b  paired asserts           both AssertCmd                  CHK + assert + assume L [+ R],   advance both
  9b  lhs-only DCE             L is AssignExp, L.lhs ∉ rhs     emit L,        advance L
  4   rhs-only assume          R is AssumeExp                  CHK + assert,  advance R
  4b  lhs-only assume          L is AssumeExp                  CHK + assert,  advance L
  3   rhs-only fresh assign    R is AssignExp, R.lhs ∉ lhs     emit R,        advance R
  10  no-match abort           nothing matched                 raise

The merged program is post-processed per-block to hoist any static
CHK assignment that landed after a dynamic (parallel-phi) assignment
into the static prologue — DSA shape requires
`(static)*(dynamic)*terminator`.

SOUNDNESS NOTES:
- Rule 6 admits the rwriter's post-havoc assumes without a joint
  satisfiability check. Pass `--check-feasibility` to insert per-
  window probes; pass `--strict` to abort instead.
- Rule 4b assumes the rwriter is allowed to drop only useless
  assumes (implied by other constraints). The CHK catches a future
  rule that drops a load-bearing assume.
- A successful assert is automatically an assume downstream (the
  split step converts non-selected asserts to assumes), so rules 4
  and 4b emit no explicit assume after their CHK.

FLAGS:
  --strict                abort on rule-6 trigger (exit 2)
  --check-feasibility     insert per-rehavoc-window `assert false` probes
  --report                print rule-hit counts + rehavoc sites
  -o PATH, --output PATH  write merged TAC here

WALKER SOURCE: src/ctac/rw_eq/transform.py — module docstring is
authoritative; this guide is a summary.
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

DEFAULT-VALUE SENTINEL: when a havoc'd symbol is not covered by
`--model` (or `--fallback`), the interpreter substitutes the
unconstrained-default sentinel `12345678` (decimal-grouped as
`1234_5678`, hex `0xbc614e`). In `--trace`, that line is tagged with
a trailing `(default)` marker so it is unambiguous which values came
from the SMT model and which are filler. Treat `(default)` values as
arbitrary: do not cite them when reasoning about Ite arms, asserts,
or branch conditions. The summary line `# model havoc:
hits=K, fallback_hits=K, sentinel_fallback=K (value=12345678)`
counts how many of each kind occurred.

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

BYTEMAP STORE-REDUCE: `--store-reduce` (off by default) builds a
per-map chain data structure during encoding, prunes shadowed Store
entries (later Store at the same key supersedes earlier),
preserves `(ite ... (M_old idx))` shared-sibling form when no
shadow fires, and drops `define-fun` lines for bytemap symbols not
reachable from any Select query — content inlined into the chain
that reads them. Sound by the array Store/Select axiom.

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
    "prj": """ctac prj --agent

Manage a ctac project: a working directory with a `.ctac/` sidecar
that pins a HEAD ("the current TAC"), records every produced
artifact's provenance, and auto-names derived files mechanically.

WHY BEAT MANUAL: solving requires `rw -> ua -> smt` (and often
several iterations). Threading those through `-o` flags and
remembering which file is "current" is error-prone; a project tracks
HEAD for you, gives you `base.rw.ua.tac` as a friendly symlink, and
keeps a manifest you can replay later.

PROJECT-AWARE COMMANDS: pass a project directory in place of a .tac
path. HEAD is read for input; outputs are ingested automatically.
- `rw`, `ua` (merge strategy): no -o → ingest, advance HEAD.
- `pp` (-> .htac), `smt` (-> .smt2): no -o → ingest as HEAD-sibling
  (parent = HEAD; HEAD does not move).
- explicit `-o PATH` always bypasses project ingestion.

PRJ COMMANDS:
  ctac prj init f.tac -o mytac --plain          # create project
  ctac prj list mytac --plain                   # list objects
  ctac prj info mytac base --plain --recursive  # walk parents

TYPICAL PIPELINE:
  ctac prj init f.tac -o mytac --plain
  ctac rw mytac --plain         # HEAD -> in.rw.tac
  ctac ua mytac --plain         # HEAD -> in.rw.ua.tac
  ctac smt mytac --plain        # writes in.rw.ua.smt2 (sibling)
  ctac prj list mytac --plain

LAYOUT:
  mytac/.ctac/HEAD                    # text: <sha>
  mytac/.ctac/refs/<label>            # text: <sha>
  mytac/.ctac/objects/<pfx>/<rest>    # canonical content
  mytac/.ctac/manifest.json           # provenance graph
  mytac/.ctac/log.jsonl               # append-only command log
  mytac/in.tac                        # symlink -> objects/<sha>

REFS: any of these resolve an object — full sha, unique short sha
(>= 4 hex chars), label name (`base`), friendly symlink name
(`in.rw.tac`), or a path inside the project root.

NOT YET PROJECT-AWARE: `stats`, `cfg`, `search`, `slice`, `df`,
`types`, `run`, `cfg-match`, `bb-diff`, `op-diff`, `pin`,
`splitcrit`, `absint`, `rw-eq`. Pass an explicit object path
(`mytac/in.rw.tac`) for those today.
""",
}


def _agent_guide_text(ctx: typer.Context | None) -> str:
    if ctx is None:
        return _AGENT_GUIDE_MAIN
    path = (ctx.command_path or "").strip().split()
    # Walk from most-specific to least: ``ctac prj init --agent``
    # tries ``init`` then ``prj`` then falls through to the main
    # guide. Sub-app commands without their own entry inherit the
    # group's guide.
    for token in reversed(path):
        if token in _AGENT_GUIDE_BY_CMD:
            return _AGENT_GUIDE_BY_CMD[token]
    return _AGENT_GUIDE_MAIN


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
    # In plain mode, output is for agents / scripts — never re-flow
    # to fit a terminal column. Rich would otherwise wrap at the
    # detected width, fragmenting tokens like ``bytemap-rw`` across
    # lines and breaking grep / pattern matching. A very large width
    # disables wrapping while keeping Console's other plain-text
    # behaviors.
    width: int | None = 10**9 if plain else None
    return Console(
        force_terminal=force_terminal,
        no_color=plain or bool(os.environ.get("NO_COLOR")) or not sys.stdout.isatty(),
        highlight=False,
        theme=TAC_THEME,
        width=width,
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


def complete_search_tokens():
    """Tab-complete TAC operator / command names for ``ctac search`` patterns.

    An agent typing ``ctac search f.tac <TAB>`` sees every token that
    will match something real: expression ops (``BWAnd``, ``Mod``,
    ``Select``, ...), command kinds (``AssignExpCmd``, ``AssertCmd``,
    ...), builtin-function symbols (``safe_math_narrow_bv256:bif``),
    and humanized keywords. Source of truth: ``ctac.ast.ops``.
    """
    def _complete(incomplete: str):
        from ctac.ast.ops import all_search_tokens
        return [t for t in all_search_tokens() if t.startswith(incomplete)]

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
