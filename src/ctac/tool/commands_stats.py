from __future__ import annotations

from collections import Counter
from pathlib import Path
from typing import Optional

import typer
from rich.table import Table

from ctac.ast.nodes import ApplyExpr, AssignExpCmd, AssumeExpCmd, ConstExpr, TacExpr
from ctac.ir.models import TacFile
from ctac.parse import ParseError, parse_path
from ctac.tool.cli_runtime import PLAIN_HELP, agent_option, app, console, plain_requested
from ctac.tool.input_resolution import resolve_tac_input_path, resolve_user_path


def print_tac_stats(
    tac: TacFile,
    *,
    plain: bool,
    by_cmd_kind: bool = False,
    top_blocks: int = 0,
) -> None:
    c = console(plain)
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


@app.command()
def stats(
    path: Optional[Path] = typer.Argument(None),
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
        help="Parse snippet weak refs as strong refs.",
    ),
) -> None:
    """Print summary statistics for a .tac file (blocks, commands, metas, symbol table size)."""
    _ = agent
    run_stats(
        path,
        plain=plain,
        by_cmd_kind=by_cmd_kind,
        top_blocks=top_blocks,
        weak_is_strong=weak_is_strong,
    )


@app.command()
def parse(
    path: Optional[Path] = typer.Argument(None),
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
        help="Parse snippet weak refs as strong refs.",
    ),
) -> None:
    """Parse a .tac file and print basic statistics (same output as ``ctac stats``)."""
    _ = agent
    run_stats(
        path,
        plain=plain,
        by_cmd_kind=by_cmd_kind,
        top_blocks=top_blocks,
        weak_is_strong=weak_is_strong,
    )
