"""`ctac cfg-simplify` — CFG simplification command.

Drops annotation-only fall-through basic blocks (no executable cmds,
single declared successor) and rewires their predecessors to point
directly at the successor. Pure CFG-shape transform; not a rewrite
rule.

The transform is also wired as the optional final phase of `ctac rw`
via the `--simplify-cfg` flag; this command exposes the same pass
standalone so the user can run it in isolation, e.g. to apply
CFG-only cleanup to a hand-edited TAC and then verify soundness via
`ctac rw-eq <orig> <simplified>`.
"""

from __future__ import annotations

import sys
from pathlib import Path
from typing import Annotated, Optional

import typer

from ctac.parse import ParseError, parse_path, render_tac_file
from ctac.tool.cli_runtime import (
    PLAIN_HELP,
    TRANSFORM_PANEL,
    agent_option,
    app,
    console,
    plain_requested,
)
from ctac.tool.input_resolution import resolve_tac_input_path, resolve_user_path
from ctac.tool.tac_output import write_program_to_path
from ctac.transform.cfg_simplify import simplify_cfg


_CFG_SIMPLIFY_EPILOG = (
    "[bold green]What it does[/bold green]  Drops basic blocks "
    "whose body is exclusively [cyan]AnnotationCmd[/cyan] / "
    "[cyan]LabelCmd[/cyan] (no executable command) with a single "
    "declared successor, and rewires the predecessor's "
    "[cyan]JumpCmd[/cyan] / [cyan]JumpiCmd[/cyan] target(s) to the "
    "dropped block's successor.\n\n"
    "[bold green]Scope[/bold green]  Only fall-throughs with a "
    "unique predecessor are removed (the safe subset for the rw-eq "
    "stuttering-simulation walker). Multi-pred fall-throughs are "
    "skipped and surfaced under [cyan]--report[/cyan].\n\n"
    "[bold green]Soundness[/bold green]  Verifiable end-to-end via "
    "[cyan]ctac rw-eq <orig.tac> <simplified.tac>[/cyan] — the "
    "stuttering walker treats each dropped block as a stutter and "
    "discharges per-sync CHKs against the simplified CFG.\n\n"
    "[bold green]Examples[/bold green]\n\n"
    "[cyan]ctac cfg-simplify in.tac -o out.tac --plain[/cyan]\n\n"
    "[cyan]ctac cfg-simplify in.tac --plain --report[/cyan]  "
    "[dim]# stdout; print drop/rewire summary[/dim]\n\n"
    "[cyan]ctac cfg-simplify in.tac -o out.htac[/cyan]  "
    "[dim]# pretty-printed output (not round-trippable)[/dim]\n\n"
    "Pipeline: [cyan]ctac rw f.tac -o f.rw.tac[/cyan] then "
    "[cyan]ctac cfg-simplify f.rw.tac -o f.rw.cfg.tac[/cyan] then "
    "[cyan]ctac rw-eq f.rw.tac f.rw.cfg.tac[/cyan]."
)


@app.command(
    "cfg-simplify",
    rich_help_panel=TRANSFORM_PANEL,
    epilog=_CFG_SIMPLIFY_EPILOG,
)
def cfg_simplify_cmd(
    path: Annotated[
        Path,
        typer.Argument(
            help="Path to .tac file (or a Certora output directory).",
        ),
    ],
    output_path: Annotated[
        Optional[Path],
        typer.Option(
            "-o",
            "--output",
            help=(
                "Write the simplified TAC here. "
                ".tac = round-trippable; .htac = pretty-printed."
            ),
        ),
    ] = None,
    plain: bool = typer.Option(False, "--plain", help=PLAIN_HELP),
    agent: bool = agent_option(),
    report: bool = typer.Option(
        False,
        "--report",
        help="Print drop / rewire / skip counts to stderr (alongside the TAC output).",
    ),
) -> None:
    """Drop annotation-only fall-through blocks."""
    _ = agent
    plain = plain_requested(plain)
    c = console(plain)

    try:
        user_path, ow = resolve_user_path(path)
        resolved, iw = resolve_tac_input_path(user_path)
        tac = parse_path(resolved)
    except ParseError as e:
        c.print(f"parse error: {e}" if plain else f"[red]parse error:[/red] {e}")
        raise typer.Exit(1) from e
    except ValueError as e:
        c.print(f"input error: {e}" if plain else f"[red]input error:[/red] {e}")
        raise typer.Exit(1) from e

    for w in ow + iw:
        c.print(f"# input warning: {w}", markup=False)

    new_program, simplify_report = simplify_cfg(tac.program)

    if output_path is None:
        text = render_tac_file(tac, program=new_program)
        if plain:
            sys.stdout.write(text)
        else:
            c.print(text)
    else:
        write_program_to_path(
            output_path=output_path,
            tac=tac,
            program=new_program,
        )

    if report:
        _print_report(c, plain=plain, simplify_report=simplify_report, output_path=output_path)
    elif output_path is not None:
        c.print(f"# wrote {output_path}", markup=False)


def _print_report(c, *, plain: bool, simplify_report, output_path: Optional[Path]) -> None:
    """Print a per-invocation summary. Format mirrors `ctac rw --report`
    — terse, plain ASCII under --plain."""
    n_dropped = simplify_report.n_dropped
    n_rewires = len(simplify_report.rewires)
    n_skipped = len(simplify_report.skipped_multipred)
    if plain:
        c.print(
            f"# cfg-simplify: dropped {n_dropped}, "
            f"rewires {n_rewires}, "
            f"skipped (multi-pred) {n_skipped}",
            markup=False,
        )
        for bid in simplify_report.dropped_blocks:
            c.print(f"#   dropped {bid}", markup=False)
        for pred, dropped, new in simplify_report.rewires:
            c.print(f"#   rewire {pred}: {dropped} -> {new}", markup=False)
        for bid in simplify_report.skipped_multipred:
            c.print(f"#   skipped {bid} (multi-pred)", markup=False)
    else:
        c.print(
            f"[bold]cfg-simplify[/bold]: dropped [green]{n_dropped}[/green], "
            f"rewires [cyan]{n_rewires}[/cyan], "
            f"skipped (multi-pred) [yellow]{n_skipped}[/yellow]"
        )
    if output_path is not None:
        c.print(f"# wrote {output_path}", markup=False)
