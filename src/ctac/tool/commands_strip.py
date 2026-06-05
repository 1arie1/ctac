"""`ctac strip` — strip client-specific metadata from a TAC file.

Thin CLI façade over :mod:`ctac.transform.strip`.
"""

from __future__ import annotations

import dataclasses
from pathlib import Path
from typing import Annotated, Optional

import typer

from ctac.parse import ParseError, parse_path
from ctac.tool.cli_runtime import (
    PLAIN_HELP,
    TRANSFORM_PANEL,
    agent_option,
    app,
    console,
    plain_requested,
)
from ctac.tool.project_io import ingest_or_write_program, resolve_project_or_tac
from ctac.transform.strip import StripReport, strip_tac

_STRIP_EPILOG = (
    "[bold green]What it does[/bold green]  Removes client-identifying "
    "metadata so a TAC dump can be published as an open benchmark: spec "
    "file paths and embedded source ([cyan]cvl.range[/cyan], "
    "[cyan]sbf.source.segment[/cyan], [cyan]sbf.rule.location[/cyan]), "
    "function/crate names ([cyan]sbf.inline.*[/cyan], struct-form "
    "[cyan]debug.sbf.function_*[/cyan]), call-trace snippets "
    "([cyan]snippet.cmd[/cyan]), assert ids. Assert message strings are "
    "replaced with sequential generic ones ([cyan]\"assert 1\"[/cyan], ...).\n\n"
    "[bold green]What it keeps[/bold green]  Generic, solver-useful "
    "metadata: [cyan]sbf.bytecode.address[/cyan], [cyan]tac.*[/cyan] "
    "structural markers, [cyan]overflow.rewrite[/cyan], "
    "[cyan]debug.sbf.external_call[/cyan] intrinsics "
    "([cyan]__rust_alloc[/cyan], [cyan]CVT_*[/cyan]), string-form "
    "memcpy/memset debug annotations, [cyan]LabelCmd[/cyan] lines. "
    "Unknown metadata keys are dropped (default-deny) and listed in "
    "[cyan]--report[/cyan].\n\n"
    "[bold green]Examples[/bold green]\n\n"
    "[cyan]ctac strip f.tac -o f_open.tac --plain[/cyan]"
    "  [dim]# default allowlist-keep policy[/dim]\n\n"
    "[cyan]ctac strip f.tac -o f_open.tac --plain --report[/cyan]"
    "  [dim]# + per-key kept/dropped table[/dim]\n\n"
    "[cyan]ctac strip f.tac -o f_open.tac --plain --all[/cyan]"
    "  [dim]# maximal anonymity: empty Metas, no annotations[/dim]\n\n"
    "Before publishing, audit the result: "
    "[cyan]grep -iE 'specFile|filepath|mangledName|displayMessage' f_open.tac[/cyan] "
    "should be empty."
)


@app.command("strip", rich_help_panel=TRANSFORM_PANEL, epilog=_STRIP_EPILOG)
def strip_cmd(
    path: Annotated[
        Optional[Path],
        typer.Argument(
            help="Path to .tac file, a Certora output directory, or a ctac project.",
        ),
    ] = None,
    output_path: Annotated[
        Optional[Path],
        typer.Option(
            "-o",
            "--output",
            help="Output .tac (round-trippable) or .htac (pretty-printed) path.",
        ),
    ] = None,
    strip_all: bool = typer.Option(
        False,
        "--all",
        help=(
            "Strip everything: empty Metas, drop every AnnotationCmd, "
            "remove all :N meta suffixes. Maximal-anonymity mode."
        ),
    ),
    plain: bool = typer.Option(False, "--plain", help=PLAIN_HELP),
    agent: bool = agent_option(),
    report: bool = typer.Option(
        False, "--report", help="Print per-key kept/dropped counts."
    ),
) -> None:
    """Strip client-specific metadata (paths, source text, names) from a TAC."""
    _ = agent
    plain = plain_requested(plain)
    c = console(plain)

    try:
        resolved = resolve_project_or_tac(path)
        tac = parse_path(resolved.tac_path)
    except ParseError as e:
        c.print(f"parse error: {e}" if plain else f"[red]parse error:[/red] {e}")
        raise typer.Exit(1) from e
    except ValueError as e:
        c.print(f"input error: {e}" if plain else f"[red]input error:[/red] {e}")
        raise typer.Exit(1) from e

    for w in resolved.warnings:
        c.print(f"# input warning: {w}", markup=False)

    result = strip_tac(tac, strip_all=strip_all)

    if report:
        _print_report(c, plain=plain, report=result.report, strip_all=strip_all)

    stripped_tac = dataclasses.replace(tac, metas=result.metas)
    written_path, _info = ingest_or_write_program(
        explicit_output=output_path,
        project=resolved.project,
        tac=stripped_tac,
        program=result.program,
        command="strip",
        kind="tac",
        advance_head=True,
    )
    if written_path is not None:
        if not report:
            c.print(f"# wrote {written_path}", markup=False)
    else:
        if not report:
            c.print(
                "# no --output given; pass -o FILE.tac (or .htac) to write the result",
                markup=False,
            )


def _counter_line(counter) -> str:
    return ", ".join(f"{k}={v}" for k, v in sorted(counter.items())) or "-"


def _print_report(c, *, plain: bool, report: StripReport, strip_all: bool) -> None:
    def line(s: str) -> None:
        c.print(s, markup=not plain)

    kept_meta = sum(report.kept_meta.values())
    dropped_meta = sum(report.dropped_meta.values())
    kept_ann = sum(report.kept_annotations.values())
    dropped_ann = sum(report.dropped_annotations.values())
    if plain:
        line("strip:")
        line(f"  mode: {'all' if strip_all else 'allowlist'}")
        line(f"  metas_kept: {kept_meta}")
        line(f"  metas_dropped: {dropped_meta}")
        line(f"  annotations_kept: {kept_ann}")
        line(f"  annotations_dropped: {dropped_ann}")
        line(f"  assert_messages_replaced: {report.assert_messages_replaced}")
        line(f"  meta_suffixes_removed: {report.meta_suffixes_removed}")
        line(f"  kept_keys: {_counter_line(report.kept_meta + report.kept_annotations)}")
        line(
            "  dropped_keys: "
            f"{_counter_line(report.dropped_meta + report.dropped_annotations)}"
        )
        if report.unknown_keys:
            line(f"  unknown_keys: {', '.join(sorted(report.unknown_keys))}")
        return
    line("[bold]Strip Summary[/bold]")
    line(f"  mode: [cyan]{'all' if strip_all else 'allowlist'}[/cyan]")
    line(f"  metas kept/dropped: [bold]{kept_meta}[/bold]/[bold]{dropped_meta}[/bold]")
    line(
        f"  annotations kept/dropped: [bold]{kept_ann}[/bold]/[bold]{dropped_ann}[/bold]"
    )
    line(f"  assert messages replaced: [bold]{report.assert_messages_replaced}[/bold]")
    line(f"  meta suffixes removed: [bold]{report.meta_suffixes_removed}[/bold]")
    line(f"  kept keys: {_counter_line(report.kept_meta + report.kept_annotations)}")
    line(
        "  dropped keys: "
        f"{_counter_line(report.dropped_meta + report.dropped_annotations)}"
    )
    if report.unknown_keys:
        line(
            f"  [yellow]unknown keys (dropped):[/yellow] "
            f"{', '.join(sorted(report.unknown_keys))}"
        )
