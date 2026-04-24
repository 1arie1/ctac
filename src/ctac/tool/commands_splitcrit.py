"""`ctac split-crit` — break critical edges in a TAC CFG.

Thin CLI wrapper around :func:`ctac.splitcrit.split_critical_edges`.
"""

from __future__ import annotations

from pathlib import Path
from typing import Annotated, Optional

import typer

from ctac.parse import ParseError, parse_path, render_tac_file
from ctac.splitcrit import split_critical_edges
from ctac.tool.cli_runtime import (
    PLAIN_HELP,
    TRANSFORM_PANEL,
    agent_option,
    app,
    console,
    plain_requested,
)
from ctac.tool.input_resolution import resolve_tac_input_path, resolve_user_path


_SPLIT_CRIT_EPILOG = (
    "[bold green]What it does[/bold green]  Insert a single-command shim "
    "block on every critical edge [cyan](u -> v)[/cyan] where [cyan]u[/cyan] "
    "has multiple successors and [cyan]v[/cyan] has multiple predecessors. "
    "Each shim contains one [cyan]JumpCmd v[/cyan] and sits between "
    "[cyan]u[/cyan] and [cyan]v[/cyan], so no edge incident to it is "
    "critical. Idempotent: a program with no critical edges is returned "
    "unchanged ([cyan]was_noop: true[/cyan]).\n\n"
    "[bold green]Why[/bold green]  [cyan]ctac smt[/cyan] (sea_vc) requires "
    "a critical-edge-free CFG for its predecessor-exclusivity encoding to "
    "be sound. [cyan]ctac smt[/cyan] runs this transform automatically as "
    "a pre-pass, so most users don't need this command directly; use it "
    "when you want to inspect or hand off the split program.\n\n"
    "[bold green]Examples[/bold green]\n\n"
    "[cyan]ctac split-crit f.tac -o f.sc.tac --plain[/cyan]"
    "  [dim]# split and write[/dim]\n\n"
    "[cyan]ctac split-crit f.tac --plain --report[/cyan]"
    "  [dim]# counts only[/dim]"
)


@app.command("split-crit", rich_help_panel=TRANSFORM_PANEL, epilog=_SPLIT_CRIT_EPILOG)
def split_crit_cmd(
    path: Annotated[
        Optional[Path],
        typer.Argument(
            help="Path to .tac / .sbf.json file, or a Certora output directory.",
        ),
    ] = None,
    output_path: Annotated[
        Optional[Path],
        typer.Option(
            "-o",
            "--output",
            help="Write the split TAC here (.tac).",
        ),
    ] = None,
    plain: bool = typer.Option(False, "--plain", help=PLAIN_HELP),
    agent: bool = agent_option(),
    report: bool = typer.Option(
        False, "--report", help="Print counts and the split edge list."
    ),
) -> None:
    """Break critical edges by inserting single-command shim blocks."""
    _ = agent
    plain = plain_requested(plain)
    c = console(plain)

    try:
        user_path, user_warnings = resolve_user_path(path)
        tac_path, input_warnings = resolve_tac_input_path(user_path)
        tac = parse_path(tac_path)
    except ParseError as e:
        c.print(f"parse error: {e}" if plain else f"[red]parse error:[/red] {e}")
        raise typer.Exit(1) from e
    except ValueError as e:
        c.print(f"input error: {e}" if plain else f"[red]input error:[/red] {e}")
        raise typer.Exit(1) from e

    for w in user_warnings + input_warnings:
        c.print(f"# input warning: {w}", markup=False)

    result = split_critical_edges(tac.program)

    if report:
        _print_report(c, plain=plain, result=result)

    if output_path is None:
        if not report:
            c.print(
                "# no --output given; pass -o FILE.tac to write the result",
                markup=False,
            )
        return

    text = render_tac_file(tac, program=result.program)
    output_path.write_text(text, encoding="utf-8")
    if not report:
        c.print(f"# wrote {output_path}", markup=False)


def _print_report(c, *, plain: bool, result) -> None:
    def line(s: str) -> None:
        c.print(s, markup=not plain)

    if plain:
        line("split-crit:")
        line(f"  shims_added: {result.shims_added}")
        line(f"  was_noop: {str(result.was_noop).lower()}")
        for u, v in result.edges_split:
            line(f"  edge: {u} -> {v}")
        return
    line("[bold]Split-Crit Summary[/bold]")
    line(f"  shims_added: [bold]{result.shims_added}[/bold]")
    line(f"  was_noop: [bold]{str(result.was_noop).lower()}[/bold]")
    for u, v in result.edges_split:
        line(f"  edge: [cyan]{u}[/cyan] -> [cyan]{v}[/cyan]")
