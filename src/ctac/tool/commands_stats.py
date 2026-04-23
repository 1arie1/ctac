from __future__ import annotations

from collections import Counter
from pathlib import Path
from typing import Optional

import typer

from ctac.analysis import (
    SymbolKind,
    classify_bytemap_usage,
    classify_sort,
)
from ctac.ast.nodes import (
    ApplyExpr,
    AssertCmd,
    AssignExpCmd,
    AssignHavocCmd,
    AssumeExpCmd,
    ConstExpr,
    SymbolRef,
    TacExpr,
)
from ctac.ir.models import TacFile
from ctac.parse import ParseError, parse_path
from ctac.tool.cli_runtime import (
    INSPECT_PANEL,
    PLAIN_HELP,
    agent_option,
    app,
    console,
    plain_requested,
)
from ctac.tool.input_resolution import resolve_tac_input_path, resolve_user_path
from ctac.tool.stats_model import StatsCollection
from ctac.tool.stats_render import render_plain_stats, render_rich_stats_tree


def collect_tac_stats(
    tac: TacFile,
    *,
    by_cmd_kind: bool = False,
    top_blocks: int = 0,
) -> StatsCollection:
    stats = StatsCollection()
    n_blocks = len(tac.program.blocks)
    n_cmds = sum(len(b.commands) for b in tac.program.blocks)
    n_meta_keys = len(tac.metas)
    sym_lines = tac.symbol_table_text.count("\n") + (1 if tac.symbol_table_text else 0)
    stats.add_str("overview.path", tac.path if tac.path is not None else "-")
    stats.add_num("overview.symbol_table_lines", sym_lines)
    stats.add_num("overview.blocks", n_blocks)
    stats.add_num("overview.commands", n_cmds)
    stats.add_num("overview.metas_top_keys", n_meta_keys)

    if by_cmd_kind:
        cmd_kinds = Counter(type(cmd).__name__ for b in tac.program.blocks for cmd in b.commands)
        for name, cnt in sorted(cmd_kinds.items(), key=lambda kv: (-kv[1], kv[0])):
            stats.add_num(f"command_kinds.{name}", cnt)

    if top_blocks > 0:
        ranked = sorted(tac.program.blocks, key=lambda b: len(b.commands), reverse=True)[:top_blocks]
        stats.add_num("top_blocks_by_command_count.count", len(ranked))
        for b in ranked:
            stats.add_num(f"top_blocks_by_command_count.{b.id}.commands", len(b.commands))
            stats.add_num(f"top_blocks_by_command_count.{b.id}.successors", len(b.successors))

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

    for op, cnt in sorted(expr_ops.items(), key=lambda kv: (-kv[1], kv[0])):
        stats.add_num(f"expression_ops.{op}", cnt)

    stats.add_num("nonlinear_ops.multiplication", nonlinear_mul)
    stats.add_num("nonlinear_ops.division_or_mod", nonlinear_div)

    _collect_memory_stats(stats, tac)
    return stats


def _collect_memory_stats(stats: StatsCollection, tac: TacFile) -> None:
    """Emit ``memory.*`` stats driven by the declared symbol sorts."""
    memory_symbols = {
        name
        for name, sort in tac.symbol_sorts.items()
        if classify_sort(sort) is SymbolKind.MEMORY
    }
    stats.add_num("memory.bytemap_symbols", len(memory_symbols))
    capability = classify_bytemap_usage(tac.program, tac.symbol_sorts)
    stats.add_str("memory.capability", capability.value)
    if not memory_symbols:
        return

    havocs = Counter()
    selects = Counter()
    stores = 0

    def _visit(expr: TacExpr) -> None:
        nonlocal stores
        if not isinstance(expr, ApplyExpr):
            return
        if expr.op == "Select" and expr.args and isinstance(expr.args[0], SymbolRef):
            base = expr.args[0].name
            # Strip DSA suffix: ``M16:3`` -> ``M16``.
            base = base.split(":", 1)[0]
            if base in memory_symbols:
                selects[base] += 1
        elif expr.op == "Store":
            stores += 1
        for a in expr.args:
            _visit(a)

    for b in tac.program.blocks:
        for cmd in b.commands:
            if isinstance(cmd, AssignHavocCmd):
                lhs = cmd.lhs.split(":", 1)[0]
                if lhs in memory_symbols:
                    havocs[lhs] += 1
            elif isinstance(cmd, AssignExpCmd):
                _visit(cmd.rhs)
            elif isinstance(cmd, AssumeExpCmd):
                _visit(cmd.condition)
            elif isinstance(cmd, AssertCmd):
                _visit(cmd.predicate)

    stats.add_num("memory.havocs", sum(havocs.values()))
    stats.add_num("memory.select_reads", sum(selects.values()))
    stats.add_num("memory.store_writes", stores)
    # Per-bytemap Select count for debugging hot spots — ranked by reads,
    # tie-break alphabetically for determinism.
    for name in sorted(memory_symbols, key=lambda n: (-selects[n], n)):
        if selects[name] == 0 and havocs[name] == 0:
            continue
        stats.add_num(f"memory.by_symbol.{name}.selects", selects[name])
        stats.add_num(f"memory.by_symbol.{name}.havocs", havocs[name])


def print_tac_stats(
    tac: TacFile,
    *,
    plain: bool,
    by_cmd_kind: bool = False,
    top_blocks: int = 0,
) -> None:
    c = console(plain)
    stats = collect_tac_stats(
        tac,
        by_cmd_kind=by_cmd_kind,
        top_blocks=top_blocks,
    )
    if plain:
        for line in render_plain_stats(stats):
            c.print(line, markup=False)
        return
    c.print(render_rich_stats_tree(stats))


def run_stats(
    path: Path | None,
    *,
    plain: bool,
    by_cmd_kind: bool = False,
    top_blocks: int = 0,
    weak_is_strong: bool = False,
) -> None:
    plain = plain_requested(plain)
    c = console(plain)
    try:
        user_path, user_warnings = resolve_user_path(path)
        tac_path, input_warnings = resolve_tac_input_path(user_path)
        tac = parse_path(tac_path, weak_is_strong=weak_is_strong)
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
    print_tac_stats(
        tac,
        plain=plain,
        by_cmd_kind=by_cmd_kind,
        top_blocks=top_blocks,
    )


_STATS_EPILOG = (
    "[bold green]What it does[/bold green]  Reports block/command/meta counts, "
    "symbol-table size, command-kind counts, top-N dense blocks, expression-op "
    "frequencies, non-linear mul/div counters, and the bytemap memory "
    "capability. Cheap sanity check to start with on any unknown TAC or SBF "
    "file.\n\n"
    "[bold green]Examples[/bold green]\n\n"
    "[cyan]ctac stats f.tac --plain[/cyan]\n\n"
    "[cyan]ctac stats dir/ --plain[/cyan]  [dim]# resolve dir/outputs/*.tac[/dim]\n\n"
    "[cyan]ctac stats f.tac --plain --top-blocks 0 --no-by-cmd-kind[/cyan]"
    "  [dim]# most compact[/dim]\n\n"
    "[cyan]ctac stats f.tac --plain --top-blocks 5[/cyan]  [dim]# top 5 dense blocks[/dim]"
)


@app.command(rich_help_panel=INSPECT_PANEL, epilog=_STATS_EPILOG)
def stats(
    path: Optional[Path] = typer.Argument(
        None, help="Path to .tac / .sbf.json file, or a Certora output directory."
    ),
    plain: bool = typer.Option(False, "--plain", help=PLAIN_HELP),
    agent: bool = agent_option(),
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
    weak_is_strong: bool = typer.Option(
        False,
        "--weak-is-strong",
        help="Parse snippet weak refs as strong refs (annotations use strong deref).",
    ),
) -> None:
    """Summary stats for a .tac / .sbf.json file (first look)."""
    _ = agent
    run_stats(
        path,
        plain=plain,
        by_cmd_kind=by_cmd_kind,
        top_blocks=top_blocks,
        weak_is_strong=weak_is_strong,
    )


_PARSE_EPILOG = (
    "Same output as [cyan]ctac stats[/cyan]; the name emphasizes that a "
    "successful run means the file round-trips through the TAC parser. "
    "Use it as a first-pass syntactic check before doing anything else.\n\n"
    "[bold green]Examples[/bold green]\n\n"
    "[cyan]ctac parse f.tac --plain[/cyan]\n\n"
    "[cyan]ctac parse dir/ --plain[/cyan]  [dim]# auto-resolves dir/outputs/*.tac[/dim]"
)


@app.command(rich_help_panel=INSPECT_PANEL, epilog=_PARSE_EPILOG)
def parse(
    path: Optional[Path] = typer.Argument(
        None, help="Path to .tac / .sbf.json file, or a Certora output directory."
    ),
    plain: bool = typer.Option(False, "--plain", help=PLAIN_HELP),
    agent: bool = agent_option(),
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
    weak_is_strong: bool = typer.Option(
        False,
        "--weak-is-strong",
        help="Parse snippet weak refs as strong refs (annotations use strong deref).",
    ),
) -> None:
    """Parse a .tac file and print stats (alias of `ctac stats`)."""
    _ = agent
    run_stats(
        path,
        plain=plain,
        by_cmd_kind=by_cmd_kind,
        top_blocks=top_blocks,
        weak_is_strong=weak_is_strong,
    )
