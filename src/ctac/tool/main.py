from __future__ import annotations

import difflib
import os
import re
import sys
from collections import Counter
from pathlib import Path
from typing import Annotated, Any, Optional

import typer
from rich.console import Console
from rich.table import Table

from ctac.ast.models import TacFile
from ctac.diff.match_cfg import compare_matched_blocks, match_cfg_blocks
from ctac.eval import RunConfig, Value, parse_tac_model_path, run_program, value_to_text
from ctac.graph import Cfg, CfgFilter, CfgStyle
from ctac.parse import ParseError, parse_path
from ctac.tac_ast.nodes import (
    ApplyExpr,
    AssignExpCmd,
    AssignHavocCmd,
    AssumeExpCmd,
    ConstExpr,
    TacExpr,
)
from ctac.tac_ast.pretty import DEFAULT_PRINTERS, configured_printer, pretty_lines
from ctac.tool.highlight import TAC_THEME, highlight_tac_line
from ctac.tool.input_resolution import (
    resolve_model_input_path as _resolve_model_input_path,
    resolve_tac_input_path as _resolve_tac_input_path,
    resolve_user_path as _resolve_user_path,
)
from ctac.tool.run_format import (
    MODEL_HAVOC_FALLBACK_NUM,
    coerce_value_kind as _coerce_value_kind,
    format_value_plain_local as _format_value_plain,
    format_value_rich as _format_value_rich,
    model_fallback_value as _model_fallback_value,
    pp_terminator_line as _pp_terminator_line,
    source_prefix_for_cmd as _source_prefix_for_cmd,
    strip_meta_suffix as _strip_meta_suffix,
    values_equal as _values_equal,
)

app = typer.Typer(no_args_is_help=True, add_completion=False)

_AGENT_GUIDE_MAIN = """ctac agent guide (plain, terse)

Use ctac when you need TAC-aware structure, not raw text scraping.
Key use-cases:
- Fast sanity: `ctac stats <file> --plain`
- Slice/control-flow: `ctac cfg|pp <file> --from A --to B --plain`
- Cross-build drift: `ctac cfg-match` then `ctac bb-diff`
- Concrete replay/model checks: `ctac run --model ... --trace --plain`
- Pattern mining in commands: `ctac search <file> <pattern> --plain`

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

Use to find command patterns in parsed TAC blocks.
Defaults to regex; use `--literal` for substring.
Useful: `--blocks-only`, `--count`, `--max-matches`, and path filters.
Alias: `ctac grep`.
""",
    "grep": """ctac grep --agent

Alias of `ctac search`.
Use exactly like `search`; defaults to regex.
""",
    "cfg-match": """ctac cfg-match --agent

Use for coarse block mapping between two TACs.
Run before `bb-diff` to understand structural correspondence.
Tune with `--const-weight` and `--min-score`.
""",
    "bb-diff": """ctac bb-diff --agent

Use for semantic deltas in matched basic blocks.
Typical: `--drop-empty --normalize-vars --max-diff-lines N --plain`.
Run after `cfg-match`.
""",
    "run": """ctac run --agent

Use for concrete execution/replay.
Model replay: `--model ... --trace --plain`.
Validation mode: add `--validate`.
Use `--fallback` only with `--model`.
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
    # Intentionally plain text (no Rich formatting).
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


def _agent_option() -> Any:
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
    agent: bool = _agent_option(),
) -> None:
    # Guidance/exit is handled by callback above when --agent is present.
    _ = (ctx, agent)


def _console(plain: bool) -> Console:
    # Auto-detect TTY by default so redirected output stays plain (no ANSI styles).
    force_terminal = False if plain else None
    return Console(
        force_terminal=force_terminal,
        no_color=plain or bool(os.environ.get("NO_COLOR")) or not sys.stdout.isatty(),
        highlight=False,
        theme=TAC_THEME,
    )


def _plain_requested(plain: bool) -> bool:
    return plain or os.environ.get("CTAC_PLAIN", "").lower() in ("1", "true", "yes")


def _truncate_diff_lines(lines: list[str], max_lines: int) -> tuple[list[str], int]:
    """Return at most `max_lines` lines and how many were omitted."""
    if max_lines < 0:
        return lines, 0
    if len(lines) <= max_lines:
        return lines, 0
    keep = lines[:max_lines]
    omitted = len(lines) - max_lines
    return keep, omitted


def _print_tac_stats(
    tac: TacFile,
    *,
    plain: bool,
    by_cmd_kind: bool = False,
    top_blocks: int = 0,
) -> None:
    c = _console(plain)
    n_blocks = len(tac.program.blocks)
    n_cmds = sum(len(b.commands) for b in tac.program.blocks)
    n_meta_keys = len(tac.metas)
    sym_lines = tac.symbol_table_text.count("\n") + (1 if tac.symbol_table_text else 0)

    if plain:
        c.print(f"path: {tac.path}")
        c.print(f"symbol_table_lines: {sym_lines}")
        c.print(f"blocks: {n_blocks}")
        c.print(f"commands: {n_cmds}")
        c.print(f"metas_top_keys: {n_meta_keys}")
    else:
        c.print(f"[bold]path[/bold] {tac.path}")
        c.print(f"[bold]symbol table[/bold] ~{sym_lines} lines")
        c.print(f"[bold]blocks[/bold] {n_blocks}")
        c.print(f"[bold]commands[/bold] {n_cmds}")
        c.print(f"[bold]metas keys[/bold] {n_meta_keys}")

    if by_cmd_kind:
        cmd_kinds = Counter(type(cmd).__name__ for b in tac.program.blocks for cmd in b.commands)
        if plain:
            c.print("command_kinds:")
            for name, cnt in sorted(cmd_kinds.items(), key=lambda kv: (-kv[1], kv[0])):
                c.print(f"  {name}: {cnt}")
        else:
            c.print("[bold]command kinds[/bold]")
            t = Table(expand=False)
            t.add_column("kind", no_wrap=True)
            t.add_column("count", justify="right", no_wrap=True)
            for name, cnt in sorted(cmd_kinds.items(), key=lambda kv: (-kv[1], kv[0])):
                t.add_row(name, str(cnt))
            c.print(t)

    if top_blocks > 0:
        ranked = sorted(tac.program.blocks, key=lambda b: len(b.commands), reverse=True)[:top_blocks]
        if plain:
            c.print("top_blocks_by_command_count:")
            for b in ranked:
                c.print(f"  {b.id}: commands={len(b.commands)} succ={len(b.successors)}")
        else:
            c.print(f"[bold]top {len(ranked)} blocks by command count[/bold]")
            t = Table(expand=False)
            t.add_column("block", no_wrap=True)
            t.add_column("commands", justify="right", no_wrap=True)
            t.add_column("successors", justify="right", no_wrap=True)
            for b in ranked:
                t.add_row(b.id, str(len(b.commands)), str(len(b.successors)))
            c.print(t)

    expr_ops: Counter[str] = Counter()
    nonlinear_mul = 0
    nonlinear_div = 0

    def _visit_expr(expr: TacExpr) -> None:
        nonlocal nonlinear_mul, nonlinear_div
        if not isinstance(expr, ApplyExpr):
            return
        expr_ops[expr.op] += 1

        if len(expr.args) >= 2:
            lhs, rhs = expr.args[0], expr.args[1]
            if expr.op in ("Mul", "IntMul"):
                if not isinstance(lhs, ConstExpr) and not isinstance(rhs, ConstExpr):
                    nonlinear_mul += 1
            if expr.op in ("Div", "IntDiv", "Mod", "IntMod"):
                if not isinstance(rhs, ConstExpr):
                    nonlinear_div += 1

        for arg in expr.args:
            _visit_expr(arg)

    for b in tac.program.blocks:
        for cmd in b.commands:
            if isinstance(cmd, AssignExpCmd):
                _visit_expr(cmd.rhs)
            elif isinstance(cmd, AssumeExpCmd):
                _visit_expr(cmd.condition)

    if plain:
        c.print("expression_ops:")
        for op, cnt in sorted(expr_ops.items(), key=lambda kv: (-kv[1], kv[0])):
            c.print(f"  {op}: {cnt}")
        c.print("nonlinear_ops:")
        c.print(f"  multiplication: {nonlinear_mul}")
        c.print(f"  division_or_mod: {nonlinear_div}")
    else:
        c.print("[bold]expression ops[/bold]")
        t_ops = Table(expand=False)
        t_ops.add_column("op", no_wrap=True)
        t_ops.add_column("count", justify="right", no_wrap=True)
        for op, cnt in sorted(expr_ops.items(), key=lambda kv: (-kv[1], kv[0])):
            t_ops.add_row(op, str(cnt))
        c.print(t_ops)

        c.print("[bold]nonlinear arithmetic ops[/bold]")
        t_nl = Table(expand=False)
        t_nl.add_column("kind", no_wrap=True)
        t_nl.add_column("count", justify="right", no_wrap=True)
        t_nl.add_row("multiplication", str(nonlinear_mul))
        t_nl.add_row("division_or_mod", str(nonlinear_div))
        c.print(t_nl)


def _run_stats(
    path: Path | None,
    *,
    plain: bool,
    by_cmd_kind: bool = False,
    top_blocks: int = 0,
) -> None:
    plain = _plain_requested(plain)
    c = _console(plain)
    try:
        user_path, user_warnings = _resolve_user_path(path)
        tac_path, input_warnings = _resolve_tac_input_path(user_path)
        tac = parse_path(tac_path)
        for w in (user_warnings + input_warnings):
            c.print(f"input warning: {w}" if plain else f"[yellow]input warning:[/yellow] {w}")
    except ParseError as e:
        if plain:
            c.print(f"parse error: {e}")
        else:
            c.print(f"[red]parse error:[/red] {e}")
        raise typer.Exit(1) from e
    except ValueError as e:
        if plain:
            c.print(f"input error: {e}")
        else:
            c.print(f"[red]input error:[/red] {e}")
        raise typer.Exit(1) from e
    _print_tac_stats(
        tac,
        plain=plain,
        by_cmd_kind=by_cmd_kind,
        top_blocks=top_blocks,
    )


_PATH_KW = dict(exists=True, dir_okay=True, readable=True)
_PLAIN_HELP = "Plain text only (no Rich styling); also set CTAC_PLAIN=1 or NO_COLOR."


@app.command()
def stats(
    path: Optional[Path] = typer.Argument(None),
    plain: bool = typer.Option(False, "--plain", help=_PLAIN_HELP),
    agent: bool = _agent_option(),
    by_cmd_kind: bool = typer.Option(
        True,
        "--by-cmd-kind/--no-by-cmd-kind",
        help="Show counts by parsed TAC command class.",
    ),
    top_blocks: int = typer.Option(
        10,
        "--top-blocks",
        min=0,
        help="Show top N blocks by command count (0 disables). Default: 10.",
    ),
) -> None:
    """Print summary statistics for a .tac file (blocks, commands, metas, symbol table size)."""
    _ = agent
    _run_stats(path, plain=plain, by_cmd_kind=by_cmd_kind, top_blocks=top_blocks)


@app.command()
def parse(
    path: Optional[Path] = typer.Argument(None),
    plain: bool = typer.Option(False, "--plain", help=_PLAIN_HELP),
    agent: bool = _agent_option(),
    by_cmd_kind: bool = typer.Option(
        True,
        "--by-cmd-kind/--no-by-cmd-kind",
        help="Show counts by parsed TAC command class.",
    ),
    top_blocks: int = typer.Option(
        10,
        "--top-blocks",
        min=0,
        help="Show top N blocks by command count (0 disables). Default: 10.",
    ),
) -> None:
    """Parse a .tac file and print basic statistics (same output as ``ctac stats``)."""
    _ = agent
    _run_stats(path, plain=plain, by_cmd_kind=by_cmd_kind, top_blocks=top_blocks)


@app.command("cfg-match")
def match_cfg_cmd(
    left: Path = typer.Argument(..., exists=True, dir_okay=True, readable=True),
    right: Path = typer.Argument(..., exists=True, dir_okay=True, readable=True),
    plain: bool = typer.Option(False, "--plain", help=_PLAIN_HELP),
    agent: bool = _agent_option(),
    min_score: float = typer.Option(
        0.45,
        "--min-score",
        min=0.0,
        max=1.0,
        help="Minimum pair score to consider as a block match.",
    ),
    const_weight: float = typer.Option(
        0.20,
        "--const-weight",
        min=0.0,
        max=1.0,
        help="Weight of constant-signature overlap in block matching.",
    ),
    max_rows: int = typer.Option(
        120,
        "--max-rows",
        min=1,
        help="Maximum number of matched rows to print.",
    ),
) -> None:
    """Coarse CFG block matching with weighted structural/meta features."""
    _ = agent
    plain = _plain_requested(plain)
    c = _console(plain)
    try:
        left_tac_path, left_w = _resolve_tac_input_path(left)
        right_tac_path, right_w = _resolve_tac_input_path(right)
        a = parse_path(left_tac_path)
        b = parse_path(right_tac_path)
        for w in left_w:
            c.print(f"input warning: left: {w}" if plain else f"[yellow]input warning:[/yellow] left: {w}")
        for w in right_w:
            c.print(f"input warning: right: {w}" if plain else f"[yellow]input warning:[/yellow] right: {w}")
    except ParseError as e:
        c.print(f"parse error: {e}" if plain else f"[red]parse error:[/red] {e}")
        raise typer.Exit(1) from e
    except ValueError as e:
        c.print(f"input error: {e}" if plain else f"[red]input error:[/red] {e}")
        raise typer.Exit(1) from e

    mr = match_cfg_blocks(a, b, min_score=min_score, const_weight=const_weight)
    c.print(f"# left blocks: {len(a.program.blocks)}")
    c.print(f"# right blocks: {len(b.program.blocks)}")
    c.print(f"# matched: {len(mr.matches)}")
    c.print(f"# unmatched_left: {len(mr.unmatched_left)}")
    c.print(f"# unmatched_right: {len(mr.unmatched_right)}")
    c.print(f"# min_score: {min_score:.2f}")
    c.print(f"# const_weight: {const_weight:.2f}")
    c.print("")

    rows = mr.matches[:max_rows]
    if plain:
        for m in rows:
            parts = []
            for k in ("source", "function", "const", "print", "scope", "degree", "ops", "count", "addr"):
                if k in m.components:
                    parts.append(f"{k}={m.components[k]:.2f}")
            c.print(
                f"{m.left_id} -> {m.right_id}  score={m.score:.3f}  "
                + (" ".join(parts) if parts else "")
            )
    else:
        t = Table(title="CFG Block Matches", expand=True)
        t.add_column("left", no_wrap=True)
        t.add_column("right", no_wrap=True)
        t.add_column("score", justify="right", no_wrap=True)
        t.add_column("signals", overflow="ellipsis")
        for m in rows:
            sig = []
            for k in ("source", "function", "const", "print", "scope", "degree", "ops", "count", "addr"):
                if k in m.components:
                    sig.append(f"{k}:{m.components[k]:.2f}")
            t.add_row(
                m.left_id,
                m.right_id,
                f"{m.score:.3f}",
                "  ".join(sig),
            )
        c.print(t)

    if len(mr.matches) > max_rows:
        c.print(f"# ... truncated {len(mr.matches) - max_rows} more matched row(s)")
    if mr.unmatched_left:
        c.print("# unmatched left:")
        c.print(", ".join(mr.unmatched_left[:80]))
        if len(mr.unmatched_left) > 80:
            c.print(f"# ... {len(mr.unmatched_left) - 80} more left blocks")
    if mr.unmatched_right:
        c.print("# unmatched right:")
        c.print(", ".join(mr.unmatched_right[:80]))
        if len(mr.unmatched_right) > 80:
            c.print(f"# ... {len(mr.unmatched_right) - 80} more right blocks")


@app.command("bb-diff")
def bb_diff_cmd(
    left: Path = typer.Argument(..., exists=True, dir_okay=True, readable=True),
    right: Path = typer.Argument(..., exists=True, dir_okay=True, readable=True),
    plain: bool = typer.Option(False, "--plain", help=_PLAIN_HELP),
    agent: bool = _agent_option(),
    min_score: float = typer.Option(
        0.45,
        "--min-score",
        min=0.0,
        max=1.0,
        help="Minimum CFG match score to consider candidate block pairs.",
    ),
    const_weight: float = typer.Option(
        0.20,
        "--const-weight",
        min=0.0,
        max=1.0,
        help="Weight of constant-signature overlap in CFG block matching.",
    ),
    normalize_vars: bool = typer.Option(
        True,
        "--normalize-vars/--raw-vars",
        help="Normalize variable/register names in each matched block before comparison.",
    ),
    include_source: bool = typer.Option(
        False,
        "--with-source/--no-source",
        help="Include source-location lines in per-block compared lines.",
    ),
    drop_empty: bool = typer.Option(
        True,
        "--drop-empty/--keep-empty",
        help="Ignore pretty-printer-empty lines (e.g., skipped labels/annotations) in BB comparison.",
    ),
    max_blocks: int = typer.Option(
        20,
        "--max-blocks",
        min=1,
        help="Maximum number of changed matched blocks to print with diffs.",
    ),
    context_lines: int = typer.Option(
        2,
        "--context",
        min=0,
        max=8,
        help="Unified diff context lines per changed block.",
    ),
    max_diff_lines: int = typer.Option(
        120,
        "--max-diff-lines",
        min=1,
        help="Maximum diff lines printed per changed block.",
    ),
) -> None:
    """Compare matched basic blocks and print per-block semantic deltas."""
    _ = agent
    plain = _plain_requested(plain)
    c = _console(plain)
    try:
        left_tac_path, left_w = _resolve_tac_input_path(left)
        right_tac_path, right_w = _resolve_tac_input_path(right)
        a = parse_path(left_tac_path)
        b = parse_path(right_tac_path)
        for w in left_w:
            c.print(f"input warning: left: {w}" if plain else f"[yellow]input warning:[/yellow] left: {w}")
        for w in right_w:
            c.print(f"input warning: right: {w}" if plain else f"[yellow]input warning:[/yellow] right: {w}")
    except ParseError as e:
        c.print(f"parse error: {e}" if plain else f"[red]parse error:[/red] {e}")
        raise typer.Exit(1) from e
    except ValueError as e:
        c.print(f"input error: {e}" if plain else f"[red]input error:[/red] {e}")
        raise typer.Exit(1) from e

    mr = match_cfg_blocks(a, b, min_score=min_score, const_weight=const_weight)
    comps = compare_matched_blocks(
        a,
        b,
        match_result=mr,
        normalize_vars=normalize_vars,
        include_source=include_source,
        drop_empty_lines=drop_empty,
    )
    changed = [x for x in comps if x.changed]
    unchanged = [x for x in comps if not x.changed]

    c.print(f"# left blocks: {len(a.program.blocks)}")
    c.print(f"# right blocks: {len(b.program.blocks)}")
    c.print(f"# matched blocks: {len(comps)}")
    c.print(f"# changed matched blocks: {len(changed)}")
    c.print(f"# unchanged matched blocks: {len(unchanged)}")
    c.print(f"# unmatched left: {len(mr.unmatched_left)}")
    c.print(f"# unmatched right: {len(mr.unmatched_right)}")
    c.print(f"# const_weight: {const_weight:.2f}")
    c.print(f"# normalize_vars: {normalize_vars}")
    c.print(f"# with_source: {include_source}")
    c.print(f"# drop_empty: {drop_empty}")
    c.print(f"# max_diff_lines: {max_diff_lines}")
    c.print("")

    top = changed[:max_blocks]
    for bc in top:
        hdr = (
            f"## {bc.left_id} -> {bc.right_id}  "
            f"match={bc.match_score:.3f}  bb_similarity={bc.similarity:.3f}"
        )
        c.print(hdr if plain else f"[bold]{hdr}[/bold]")
        if not bc.diff_lines:
            c.print("  # no diff")
            continue
        # Recompute diff with requested context for compactness.
        dlines = list(
            difflib.unified_diff(
                bc.left_lines,
                bc.right_lines,
                fromfile=bc.left_id,
                tofile=bc.right_id,
                lineterm="",
                n=context_lines,
            )
        )
        shown, omitted = _truncate_diff_lines(dlines, max_diff_lines)
        for ln in shown:
            c.print(ln)
        if omitted:
            c.print(f"# ... truncated {omitted} diff line(s) for this block")
        c.print("")

    if len(changed) > max_blocks:
        c.print(f"# ... truncated {len(changed) - max_blocks} more changed matched block(s)")
    if mr.unmatched_left:
        c.print("# unmatched left block ids:")
        c.print(", ".join(mr.unmatched_left[:100]))
        if len(mr.unmatched_left) > 100:
            c.print(f"# ... {len(mr.unmatched_left) - 100} more")
    if mr.unmatched_right:
        c.print("# unmatched right block ids:")
        c.print(", ".join(mr.unmatched_right[:100]))
        if len(mr.unmatched_right) > 100:
            c.print(f"# ... {len(mr.unmatched_right) - 100} more")


def _normalize_cfg_style(raw: str) -> CfgStyle:
    s = raw.strip().lower()
    if s in ("goto", "edges", "dot"):
        return s  # type: ignore[return-value]
    raise typer.BadParameter("use 'goto', 'edges', or 'dot'", param_hint="--style")


def _normalize_printer_name(raw: str) -> str:
    name = raw.strip().lower()
    if name in DEFAULT_PRINTERS.names():
        return name
    raise typer.BadParameter(
        f"unknown printer {raw!r}; choose one of: {', '.join(DEFAULT_PRINTERS.names())}",
        param_hint="--printer",
    )


def _build_cfg_filter(
    *,
    to_block: str | None,
    from_block: str | None,
    only: str | None,
    id_contains: str | None,
    id_regex: str | None,
    cmd_contains: str | None,
    exclude: str | None,
) -> CfgFilter:
    return CfgFilter(
        to_id=to_block,
        from_id=from_block,
        only_ids=Cfg.parse_csv_ids(only),
        id_contains=id_contains,
        id_regex=id_regex,
        cmd_contains=cmd_contains,
        exclude_ids=Cfg.parse_csv_ids(exclude),
    )


def _parse_user_value(text: str, kind: str) -> Value:
    t = text.strip()
    if kind == "bool":
        if t.lower() in ("1", "true", "t", "yes", "y"):
            return Value("bool", True)
        if t.lower() in ("0", "false", "f", "no", "n"):
            return Value("bool", False)
        raise ValueError(f"expected bool for havoc ({t!r})")
    if t.startswith(("0x", "0X")):
        n = int(t, 16)
    else:
        n = int(t, 10)
    if kind == "bv":
        return Value("bv", n)
    return Value("int", n)


def _search_matcher(
    *,
    pattern: str,
    regex: bool,
    case_sensitive: bool,
):
    if regex:
        flags = 0 if case_sensitive else re.IGNORECASE
        try:
            rx = re.compile(pattern, flags=flags)
        except re.error as e:
            raise typer.BadParameter(f"invalid --pattern regex: {e}", param_hint="pattern") from e
        return lambda text: rx.search(text) is not None

    needle = pattern if case_sensitive else pattern.casefold()

    def _match_literal(text: str) -> bool:
        hay = text if case_sensitive else text.casefold()
        return needle in hay

    return _match_literal


def _run_search(
    *,
    path: Path | None,
    pattern: str,
    plain: bool,
    printer: str,
    strip_var_suffixes: bool,
    human: bool,
    regex: bool,
    case_sensitive: bool,
    max_matches: int,
    count_only: bool,
    blocks_only: bool,
    to_block: str | None,
    from_block: str | None,
    only: str | None,
    id_contains: str | None,
    id_regex: str | None,
    cmd_contains: str | None,
    exclude: str | None,
) -> None:
    plain = _plain_requested(plain)
    c = _console(plain)
    try:
        user_path, user_warnings = _resolve_user_path(path)
        tac_path, input_warnings = _resolve_tac_input_path(user_path)
        tac = parse_path(tac_path)
    except ParseError as e:
        if plain:
            c.print(f"parse error: {e}")
        else:
            c.print(f"[red]parse error:[/red] {e}")
        raise typer.Exit(1) from e
    except ValueError as e:
        if plain:
            c.print(f"input error: {e}")
        else:
            c.print(f"[red]input error:[/red] {e}")
        raise typer.Exit(1) from e

    flt = _build_cfg_filter(
        to_block=to_block,
        from_block=from_block,
        only=only,
        id_contains=id_contains,
        id_regex=id_regex,
        cmd_contains=cmd_contains,
        exclude=exclude,
    )
    try:
        filtered_cfg, warnings = Cfg(tac.program).filtered(flt)
    except ValueError as e:
        if plain:
            c.print(f"search filter error: {e}")
        else:
            c.print(f"[red]search filter error:[/red] {e}")
        raise typer.Exit(2) from e

    printer_name = _normalize_printer_name(printer)
    pp_backend = configured_printer(
        printer_name,
        strip_var_suffixes=strip_var_suffixes,
        human_patterns=human,
    )
    matches = _search_matcher(pattern=pattern, regex=regex, case_sensitive=case_sensitive)

    if tac.path:
        c.print(f"# path: {tac.path}")
    for w in (user_warnings + input_warnings):
        c.print(f"# input warning: {w}")
    c.print(f"# printer: {printer_name}")
    c.print(f"# mode: {'regex' if regex else 'literal'}")
    c.print(f"# case_sensitive: {case_sensitive}")
    c.print(f"# pattern: {pattern!r}")
    for w in warnings:
        c.print(f"# {w}")
    if flt.any_active():
        c.print(f"# filter: {len(filtered_cfg.blocks)} of {len(tac.program.blocks)} block(s)")

    total = 0
    blocks_hit: set[str] = set()
    for b in filtered_cfg.ordered_blocks():
        for idx, cmd in enumerate(b.commands):
            line = pp_backend.print_cmd(cmd)
            if line is None or line == "":
                continue
            if not matches(line):
                continue
            total += 1
            blocks_hit.add(b.id)

            if total > max_matches:
                break
            if count_only:
                continue
            if blocks_only:
                continue
            c.print(f"{b.id}:{idx}: [{type(cmd).__name__}] {line}")
        if total > max_matches:
            break

    shown_total = min(total, max_matches)
    if blocks_only and not count_only:
        for bid in sorted(blocks_hit):
            c.print(bid)

    c.print(f"matches: {shown_total}")
    c.print(f"blocks_with_matches: {len(blocks_hit)}")
    if total > max_matches:
        c.print(f"# truncated after {max_matches} matches; raise --max-matches to see more")


@app.command()
def cfg(
    path: Optional[Path] = typer.Argument(None),
    plain: bool = typer.Option(False, "--plain", help=_PLAIN_HELP),
    agent: bool = _agent_option(),
    style: Annotated[
        str,
        typer.Option(
            "--style",
            help=(
                "goto: block label + goto targets (default). edges: one 'src -> dst' line per edge. "
                "dot: Graphviz digraph (block id labels; asserts red, clog pastel, source tooltips)."
            ),
        ),
    ] = "goto",
    max_blocks: Annotated[
        Optional[int],
        typer.Option(
            "--max-blocks",
            help="List at most this many blocks in file order (default: all).",
        ),
    ] = None,
    check_refs: bool = typer.Option(
        True,
        "--check-refs/--no-check-refs",
        help="Append a warning when some successor id is not a defined block.",
    ),
    to_block: Annotated[
        Optional[str],
        typer.Option(
            "--to",
            metavar="NBID",
            help="Keep only blocks on some path ending here (NBId ∪ ancestors). Combine with --from for 'between'.",
        ),
    ] = None,
    from_block: Annotated[
        Optional[str],
        typer.Option(
            "--from",
            metavar="NBID",
            help="Keep only blocks reachable from here (NBId ∪ descendants). Combine with --to for 'between'.",
        ),
    ] = None,
    only: Annotated[
        Optional[str],
        typer.Option(
            "--only",
            help="Comma-separated NBIds; AND-ed with other structural filters if given.",
        ),
    ] = None,
    id_contains: Annotated[
        Optional[str],
        typer.Option("--id-contains", help="Keep blocks whose id contains this substring."),
    ] = None,
    id_regex: Annotated[
        Optional[str],
        typer.Option("--id-regex", help="Keep blocks whose id matches this Python regex (search)."),
    ] = None,
    cmd_contains: Annotated[
        Optional[str],
        typer.Option(
            "--cmd-contains",
            help="Keep blocks where at least one raw command line contains this substring.",
        ),
    ] = None,
    exclude: Annotated[
        Optional[str],
        typer.Option(
            "--exclude",
            help="Comma-separated NBIds to remove after other filters.",
        ),
    ] = None,
) -> None:
    """Print the control-flow graph structure as text (goto view by default).

    Filters use **intersection** (AND): e.g. ``--to X --id-contains foo`` keeps ancestors of ``X``
    whose ids contain ``foo``. ``--from A --to B`` keeps blocks on some path from ``A`` to ``B``.
    """
    _ = agent
    plain = _plain_requested(plain)
    c = _console(plain)
    try:
        user_path, user_warnings = _resolve_user_path(path)
        tac_path, input_warnings = _resolve_tac_input_path(user_path)
        tac = parse_path(tac_path)
    except ParseError as e:
        if plain:
            c.print(f"parse error: {e}")
        else:
            c.print(f"[red]parse error:[/red] {e}")
        raise typer.Exit(1) from e
    except ValueError as e:
        if plain:
            c.print(f"input error: {e}")
        else:
            c.print(f"[red]input error:[/red] {e}")
        raise typer.Exit(1) from e

    flt = _build_cfg_filter(
        to_block=to_block,
        from_block=from_block,
        only=only,
        id_contains=id_contains,
        id_regex=id_regex,
        cmd_contains=cmd_contains,
        exclude=exclude,
    )

    cfg_model = Cfg(tac.program)
    try:
        filtered_cfg, warnings = cfg_model.filtered(flt)
    except ValueError as e:
        if plain:
            c.print(f"cfg filter error: {e}")
        else:
            c.print(f"[red]cfg filter error:[/red] {e}")
        raise typer.Exit(2) from e

    st = _normalize_cfg_style(style)
    _pfx = "//" if st == "dot" else "#"
    if tac.path:
        if st == "dot":
            c.print(f"{_pfx} path: {tac.path}", markup=False)
        else:
            c.print(f"{_pfx} path: {tac.path}")
    for w in (user_warnings + input_warnings):
        if st == "dot":
            c.print(f"{_pfx} input warning: {w}", markup=False)
        else:
            c.print(f"{_pfx} input warning: {w}")
    for w in warnings:
        if st == "dot":
            c.print(f"{_pfx} {w}", markup=False)
        else:
            c.print(f"{_pfx} {w}")
    if flt.any_active():
        msg = f"{_pfx} filter: {len(filtered_cfg.blocks)} of {len(tac.program.blocks)} block(s)"
        if st == "dot":
            c.print(msg, markup=False)
        else:
            c.print(msg)

    if st == "dot":
        for line in filtered_cfg.iter_dot(tac.metas, max_blocks=max_blocks, check_refs=check_refs):
            c.print(line, markup=False)
    else:
        for line in filtered_cfg.iter_lines(style=st, max_blocks=max_blocks, check_refs=check_refs):
            c.print(line)


@app.command()
def pp(
    path: Optional[Path] = typer.Argument(None),
    plain: bool = typer.Option(False, "--plain", help=_PLAIN_HELP),
    agent: bool = _agent_option(),
    printer: Annotated[
        str,
        typer.Option(
            "--printer",
            help="Pretty-printer backend name. Built-ins: human (default), raw.",
        ),
    ] = "human",
    strip_var_suffixes: bool = typer.Option(
        True,
        "--strip-var-suffix/--keep-var-suffix",
        help="Strip TAC var meta suffixes like ':1' in printed symbols (default: strip).",
    ),
    human: bool = typer.Option(
        True,
        "--human/--no-human",
        help="Enable human-oriented pattern rewrites in pretty output (default: on).",
    ),
    max_blocks: Annotated[
        Optional[int],
        typer.Option("--max-blocks", help="List at most this many blocks in file order."),
    ] = None,
    to_block: Annotated[Optional[str], typer.Option("--to", metavar="NBID")] = None,
    from_block: Annotated[Optional[str], typer.Option("--from", metavar="NBID")] = None,
    only: Annotated[Optional[str], typer.Option("--only")] = None,
    id_contains: Annotated[Optional[str], typer.Option("--id-contains")] = None,
    id_regex: Annotated[Optional[str], typer.Option("--id-regex")] = None,
    cmd_contains: Annotated[Optional[str], typer.Option("--cmd-contains")] = None,
    exclude: Annotated[Optional[str], typer.Option("--exclude")] = None,
) -> None:
    """Pretty-print TAC as a goto program, using a selectable printer backend."""
    _ = agent
    plain = _plain_requested(plain)
    c = _console(plain)
    try:
        user_path, user_warnings = _resolve_user_path(path)
        tac_path, input_warnings = _resolve_tac_input_path(user_path)
        tac = parse_path(tac_path)
    except ParseError as e:
        if plain:
            c.print(f"parse error: {e}")
        else:
            c.print(f"[red]parse error:[/red] {e}")
        raise typer.Exit(1) from e
    except ValueError as e:
        if plain:
            c.print(f"input error: {e}")
        else:
            c.print(f"[red]input error:[/red] {e}")
        raise typer.Exit(1) from e

    flt = _build_cfg_filter(
        to_block=to_block,
        from_block=from_block,
        only=only,
        id_contains=id_contains,
        id_regex=id_regex,
        cmd_contains=cmd_contains,
        exclude=exclude,
    )
    try:
        filtered_cfg, warnings = Cfg(tac.program).filtered(flt)
    except ValueError as e:
        if plain:
            c.print(f"pp filter error: {e}")
        else:
            c.print(f"[red]pp filter error:[/red] {e}")
        raise typer.Exit(2) from e

    printer_name = _normalize_printer_name(printer)
    pp_backend = configured_printer(
        printer_name,
        strip_var_suffixes=strip_var_suffixes,
        human_patterns=human,
    )

    if tac.path:
        c.print(f"# path: {tac.path}")
    for w in (user_warnings + input_warnings):
        c.print(f"# input warning: {w}")
    c.print(f"# printer: {printer_name}")
    for w in warnings:
        c.print(f"# {w}")
    if flt.any_active():
        c.print(f"# filter: {len(filtered_cfg.blocks)} of {len(tac.program.blocks)} block(s)")

    shown = 0
    for b in filtered_cfg.ordered_blocks():
        if max_blocks is not None and shown >= max_blocks:
            rest = len(filtered_cfg.blocks) - shown
            c.print(f"# ... truncated: {rest} more block(s) not listed (--max-blocks {max_blocks})")
            break
        c.print(highlight_tac_line(f"{b.id}:"))
        for cmd_line in pretty_lines(b.commands, printer=pp_backend):
            c.print(highlight_tac_line(f"  {cmd_line}"))
        term_line = _pp_terminator_line(b, strip_var_suffixes=strip_var_suffixes)
        if term_line is not None:
            c.print(highlight_tac_line(f"  {term_line}"))
        elif b.successors:
            c.print(highlight_tac_line(f"  goto {', '.join(b.successors)}"))
        else:
            c.print(highlight_tac_line("  stop"))
        c.print("")
        shown += 1


@app.command("grep")
@app.command("search")
def search_cmd(
    path: Optional[Path] = typer.Argument(None),
    pattern: str = typer.Argument(..., help="Pattern to search in rendered command lines."),
    plain: bool = typer.Option(False, "--plain", help=_PLAIN_HELP),
    agent: bool = _agent_option(),
    printer: Annotated[
        str,
        typer.Option(
            "--printer",
            help="Pretty-printer backend name. Built-ins: human (default), raw.",
        ),
    ] = "human",
    strip_var_suffixes: bool = typer.Option(
        True,
        "--strip-var-suffix/--keep-var-suffix",
        help="Strip TAC var meta suffixes like ':1' in printed symbols (default: strip).",
    ),
    human: bool = typer.Option(
        True,
        "--human/--no-human",
        help="Enable human-oriented pattern rewrites in printed command lines (default: on).",
    ),
    regex: bool = typer.Option(
        True,
        "--regex/--literal",
        help="Interpret PATTERN as regex (default) or plain substring.",
    ),
    case_sensitive: bool = typer.Option(
        True,
        "--case-sensitive/--ignore-case",
        help="Case-sensitive matching (default) or case-insensitive.",
    ),
    max_matches: int = typer.Option(
        200,
        "--max-matches",
        min=1,
        help="Maximum number of matches to print/count before truncation.",
    ),
    count_only: bool = typer.Option(
        False,
        "--count",
        help="Print only total matches and blocks_with_matches.",
    ),
    blocks_only: bool = typer.Option(
        False,
        "--blocks-only",
        help="Print only block ids that contain at least one match.",
    ),
    to_block: Annotated[Optional[str], typer.Option("--to", metavar="NBID")] = None,
    from_block: Annotated[Optional[str], typer.Option("--from", metavar="NBID")] = None,
    only: Annotated[Optional[str], typer.Option("--only")] = None,
    id_contains: Annotated[Optional[str], typer.Option("--id-contains")] = None,
    id_regex: Annotated[Optional[str], typer.Option("--id-regex")] = None,
    cmd_contains: Annotated[Optional[str], typer.Option("--cmd-contains")] = None,
    exclude: Annotated[Optional[str], typer.Option("--exclude")] = None,
) -> None:
    """Search TAC command lines using regex or literal pattern matching."""
    _ = agent
    _run_search(
        path=path,
        pattern=pattern,
        plain=plain,
        printer=printer,
        strip_var_suffixes=strip_var_suffixes,
        human=human,
        regex=regex,
        case_sensitive=case_sensitive,
        max_matches=max_matches,
        count_only=count_only,
        blocks_only=blocks_only,
        to_block=to_block,
        from_block=from_block,
        only=only,
        id_contains=id_contains,
        id_regex=id_regex,
        cmd_contains=cmd_contains,
        exclude=exclude,
    )


@app.command()
def run(
    path: Optional[Path] = typer.Argument(None),
    plain: bool = typer.Option(False, "--plain", help=_PLAIN_HELP),
    agent: bool = _agent_option(),
    trace: bool = typer.Option(
        False,
        "--trace/--no-trace",
        help="Show execution trace with per-instruction values and taken branches.",
    ),
    entry: Annotated[
        Optional[str],
        typer.Option("--entry", metavar="NBID", help="Start execution at this block id (default: first block)."),
    ] = None,
    max_steps: Annotated[
        int,
        typer.Option("--max-steps", min=1, help="Safety cap on executed instructions."),
    ] = 50_000,
    havoc_mode: Annotated[
        str,
        typer.Option(
            "--havoc-mode",
            help="How AssignHavocCmd gets a value: zero (default), random, ask.",
        ),
    ] = "zero",
    printer: Annotated[
        str,
        typer.Option(
            "--printer",
            help="Pretty-printer for trace lines. Built-ins: human (default), raw.",
        ),
    ] = "human",
    strip_var_suffixes: bool = typer.Option(
        True,
        "--strip-var-suffix/--keep-var-suffix",
        help="Strip TAC var suffixes like ':1' in traced symbols (default: strip).",
    ),
    human: bool = typer.Option(
        True,
        "--human/--no-human",
        help="Enable human-oriented pattern rewrites in trace pretty-printer (default: on).",
    ),
    model: Annotated[
        Optional[Path],
        typer.Option(
            "--model",
            help="Path to a report/model file containing a 'TAC model begin/end' section.",
        ),
    ] = None,
    fallback: Annotated[
        Optional[Path],
        typer.Option(
            "--fallback",
            help="Fallback model path: used for havoc values only when --model has no value.",
        ),
    ] = None,
    validate: bool = typer.Option(
        False,
        "--validate/--no-validate",
        help="Compare computed assignments against model values and report mismatches.",
    ),
) -> None:
    """Execute TAC with a concrete interpreter (assume-fail stops, assert-fail continues)."""
    _ = agent
    plain = _plain_requested(plain)
    c = _console(plain)
    try:
        user_path, user_warnings = _resolve_user_path(path)
        tac_path, input_warnings = _resolve_tac_input_path(user_path)
        tac = parse_path(tac_path)
    except ParseError as e:
        if plain:
            c.print(f"parse error: {e}")
        else:
            c.print(f"[red]parse error:[/red] {e}")
        raise typer.Exit(1) from e
    except ValueError as e:
        if plain:
            c.print(f"input error: {e}")
        else:
            c.print(f"[red]input error:[/red] {e}")
        raise typer.Exit(1) from e

    hm = havoc_mode.strip().lower()
    if hm not in ("zero", "random", "ask"):
        raise typer.BadParameter("use one of: zero, random, ask", param_hint="--havoc-mode")

    input_warnings_run = list(user_warnings) + list(input_warnings)
    if model is None and user_path.is_dir():
        try:
            auto_model, auto_model_w = _resolve_model_input_path(
                user_path,
                tac_path=tac_path,
                kind="auto model",
            )
        except ValueError as e:
            raise typer.BadParameter(str(e), param_hint="path") from e
        input_warnings_run.extend(auto_model_w)
        model = auto_model

    if fallback is not None and model is None:
        raise typer.BadParameter("--fallback requires --model", param_hint="--fallback")

    if model is not None:
        try:
            resolved_model, model_input_w = _resolve_model_input_path(
                model,
                tac_path=tac_path,
                kind="model",
            )
        except ValueError as e:
            raise typer.BadParameter(str(e), param_hint="--model") from e
        input_warnings_run.extend(model_input_w)
        model = resolved_model
    if fallback is not None:
        try:
            resolved_fallback, fallback_input_w = _resolve_model_input_path(
                fallback,
                tac_path=tac_path,
                kind="fallback model",
            )
        except ValueError as e:
            raise typer.BadParameter(str(e), param_hint="--fallback") from e
        input_warnings_run.extend(fallback_input_w)
        fallback = resolved_fallback

    if model is None and fallback is not None:
        input_warnings_run.append("fallback model ignored because primary model was not resolved")
        fallback = None

    if validate and model is None:
        raise typer.BadParameter("--validate requires --model", param_hint="--validate")

    printer_name = _normalize_printer_name(printer)
    pp_backend = configured_printer(
        printer_name,
        strip_var_suffixes=strip_var_suffixes,
        human_patterns=human,
    )
    model_values: dict[str, Value] = {}
    model_warnings: list[str] = []
    fallback_model_values: dict[str, Value] = {}
    fallback_model_warnings: list[str] = []
    if model is not None:
        try:
            model_res = parse_tac_model_path(model)
        except OSError as e:
            c.print(f"[red]model read error:[/red] {e}" if not plain else f"model read error: {e}")
            raise typer.Exit(1) from e
        except ValueError as e:
            c.print(f"[red]model parse error:[/red] {e}" if not plain else f"model parse error: {e}")
            raise typer.Exit(1) from e
        model_values = model_res.values
        model_warnings = model_res.warnings
    if fallback is not None:
        try:
            fb_res = parse_tac_model_path(fallback)
        except OSError as e:
            c.print(f"[red]fallback model read error:[/red] {e}" if not plain else f"fallback model read error: {e}")
            raise typer.Exit(1) from e
        except ValueError as e:
            c.print(f"[red]fallback model parse error:[/red] {e}" if not plain else f"fallback model parse error: {e}")
            raise typer.Exit(1) from e
        fallback_model_values = fb_res.values
        fallback_model_warnings = fb_res.warnings

    def _ask(symbol: str, kind: str) -> Value:
        while True:
            prompt = f"havoc {symbol} ({kind})"
            raw = typer.prompt(prompt)
            try:
                return _parse_user_value(raw, kind)
            except ValueError as e:
                c.print(f"[red]{e}[/red]" if not plain else str(e))

    def _model_lookup(values: dict[str, Value], symbol: str) -> Value | None:
        if symbol in values:
            return values[symbol]
        stripped = _strip_meta_suffix(symbol)
        if stripped in values:
            return values[stripped]
        return None

    model_havoc_hits = 0
    model_havoc_fallback_hits = 0
    model_havoc_sentinel_fallback = 0

    def _ask_or_model(symbol: str, kind: str) -> Value:
        nonlocal model_havoc_hits, model_havoc_fallback_hits, model_havoc_sentinel_fallback
        mv = _model_lookup(model_values, symbol)
        if mv is not None:
            model_havoc_hits += 1
            return _coerce_value_kind(mv, kind)
        fb = _model_lookup(fallback_model_values, symbol)
        if fb is not None:
            model_havoc_fallback_hits += 1
            return _coerce_value_kind(fb, kind)
        model_havoc_sentinel_fallback += 1
        return _model_fallback_value(kind)

    ask_cb = _ask if hm == "ask" else None
    run_havoc_mode = hm
    if model is not None:
        # With a model, prefer model values for havoc and use sentinel values on misses.
        ask_cb = _ask_or_model
        run_havoc_mode = "ask"

    rcfg = RunConfig(
        entry_block=entry,
        max_steps=max_steps,
        havoc_mode=run_havoc_mode,  # type: ignore[arg-type]
        ask_value=ask_cb,
        strip_var_suffixes=strip_var_suffixes,
    )
    res = run_program(tac.program, config=rcfg, pretty_cmd=pp_backend.print_cmd)

    mismatch_count = 0
    missing_expected = 0
    mismatch_samples: list[str] = []
    if validate and model_values:
        for ev in res.events:
            if ev.value is None:
                continue
            if not isinstance(ev.cmd, (AssignExpCmd, AssignHavocCmd)):
                continue
            expected = _model_lookup(model_values, ev.cmd.lhs)
            if expected is None:
                missing_expected += 1
                continue
            expected_cast = _coerce_value_kind(expected, ev.value.kind)
            ev.expected = expected_cast
            if not _values_equal(ev.value, expected_cast):
                ev.mismatch = True
                mismatch_count += 1
                if len(mismatch_samples) < 15:
                    mismatch_samples.append(
                        f"{ev.block_id}: {ev.cmd.lhs} got {value_to_text(ev.value)} expected {value_to_text(expected_cast)}"
                    )
        if mismatch_count > 0 and not trace:
            c.print(
                f"[red]validation mismatch[/red]: {mismatch_count} assignment(s) differ from model"
                if not plain
                else f"validation mismatch: {mismatch_count} assignment(s) differ from model"
            )
            for line in mismatch_samples:
                c.print(f"  - {line}")
            if mismatch_count > len(mismatch_samples):
                c.print(f"  - ... {mismatch_count - len(mismatch_samples)} more")
    elif validate and not model_values:
        c.print(
            "[yellow]validate requested but model has no parsed scalar values[/yellow]"
            if not plain
            else "validate requested but model has no parsed scalar values"
        )

    if tac.path:
        c.print(f"# path: {tac.path}")
    for w in input_warnings_run:
        c.print(f"# input warning: {w}")
    c.print(f"# mode: run (havoc={run_havoc_mode}, max_steps={max_steps})")
    if model is not None:
        c.print(f"# model: {model}")
        c.print(f"# model values: {len(model_values)}")
        for w in model_warnings:
            c.print(f"# model warning: {w}")
        if fallback is not None:
            c.print(f"# fallback model: {fallback}")
            c.print(f"# fallback model values: {len(fallback_model_values)}")
            for w in fallback_model_warnings:
                c.print(f"# fallback model warning: {w}")
        c.print(
            f"# model havoc: hits={model_havoc_hits}, fallback_hits={model_havoc_fallback_hits}, "
            f"sentinel_fallback={model_havoc_sentinel_fallback}"
            f" (value={MODEL_HAVOC_FALLBACK_NUM})"
        )
    if validate:
        c.print(f"# validate: mismatches={mismatch_count}, missing_expected={missing_expected}")
    c.print(f"# status: {res.status} ({res.reason})")

    if trace:
        cur_block: str | None = None
        block_table: Table | None = None
        for ev in res.events:
            src_prefix = _source_prefix_for_cmd(ev.cmd, tac.metas)
            if ev.block_id != cur_block:
                if block_table is not None:
                    c.print(block_table)
                    c.print("")
                cur_block = ev.block_id
                c.print(f"[bold]{cur_block}:[/bold]" if not plain else f"{cur_block}:")
                if not plain:
                    block_table = Table.grid(expand=True)
                    block_table.add_column(ratio=3, overflow="ellipsis")
                    block_table.add_column(
                        ratio=1,
                        justify="left",
                        no_wrap=True,
                        overflow="ellipsis",
                    )
                else:
                    block_table = None

            if not ev.rendered and not ev.note:
                continue

            if plain:
                if src_prefix:
                    c.print(f"  {src_prefix}")
                # Keep plain mode grep-friendly and deterministic.
                if ev.value is not None:
                    suffix = ""
                    if ev.mismatch and ev.expected is not None:
                        suffix = f"    !! expected {_format_value_plain(ev.expected)}"
                    c.print(f"  {ev.rendered}    {_format_value_plain(ev.value)}{suffix}")
                elif ev.note:
                    c.print(f"  {ev.rendered}    {ev.note}")
                else:
                    c.print(f"  {ev.rendered}")
                continue

            assert block_table is not None
            if src_prefix:
                block_table.add_row(Text(src_prefix, style="grey50"), Text(""))

            left_style = ev.color if ev.color else None
            left = highlight_tac_line(ev.rendered or "", base_style=left_style)

            if ev.value is not None:
                right = _format_value_rich(ev.value)
                if ev.mismatch and ev.expected is not None:
                    right.append("  ")
                    right.append("!= expected ", style="bold red")
                    right.append(_format_value_plain(ev.expected), style="bold red")
            elif ev.note:
                note_style = f"bold {ev.color}" if ev.color else "bold cyan"
                right = Text(ev.note, style=note_style, justify="left")
            else:
                right = Text("")

            block_table.add_row(left, right)

        if block_table is not None and not plain:
            c.print(block_table)
        c.print("")

    c.print(f"steps: {res.steps}")
    c.print(f"executed_blocks: {len(res.executed_blocks)}")
    c.print(f"assert_ok: {res.assert_ok}")
    c.print(f"assert_fail: {res.assert_fail}")

    if res.status == "stopped":
        raise typer.Exit(2)
    if res.status in ("error", "max_steps"):
        raise typer.Exit(3)


def main() -> None:
    app()


if __name__ == "__main__":
    main()
