"""`ctac ua` — uniquify asserts.

Converts a multi-assertion TAC program into one whose assertions have all
been redirected to a single ``__UA_ERROR`` block. See
:mod:`ctac.ua` for the underlying transforms.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Annotated, Optional

import typer

from ctac.analysis import remove_true_asserts
from ctac.ast.nodes import AssertCmd
from ctac.ir.models import TacProgram
from ctac.parse import ParseError, parse_path, render_tac_file
from ctac.tool.tac_output import filter_live_extra_symbols
from ctac.rewrite import rewrite_program
from ctac.rewrite.rules import PURIFY_ASSERT
from ctac.tool.cli_runtime import (
    PLAIN_HELP,
    TRANSFORM_PANEL,
    agent_option,
    app,
    complete_choices,
    console,
    plain_requested,
)
from ctac.tool.project_io import ingest_or_write_program, resolve_project_or_tac
from ctac.ua import merge_asserts, split_asserts


def _count_asserts(program: TacProgram) -> int:
    return sum(
        1 for b in program.blocks for c in b.commands if isinstance(c, AssertCmd)
    )


_UA_EPILOG = (
    "[bold green]What it does[/bold green]  Use as preprocessing for "
    "[cyan]ctac smt[/cyan], which requires a single assertion. Each "
    "assertion's predicate is used verbatim — never inverted — so the "
    "rewrite preserves the original semantics. Single-assert input is a "
    "no-op ([cyan]was_noop: true[/cyan]); zero-assert input emits a warning.\n\n"
    "[bold green]Pipeline[/bold green]\n\n"
    "[bold]1.[/bold] [cyan]remove_true_asserts[/cyan] — strip every "
    "[cyan]assert true[/cyan].\n\n"
    "[bold]2.[/bold] [cyan]PURIFY_ASSERT[/cyan] rewrite — name each "
    "non-trivial predicate as a fresh [cyan]TA<N>:bool[/cyan].\n\n"
    "[bold]3.[/bold] Apply [cyan]--strategy[/cyan]:\n\n"
    "    [cyan]merge[/cyan] — redirect every remaining assert to "
    "[cyan]__UA_ERROR[/cyan] via [cyan]if (P) goto GOOD else goto __UA_ERROR[/cyan], "
    "with [cyan]assume P[/cyan] starting each continuation so later asserts "
    "can assume earlier ones held. Output is a single .tac file.\n\n"
    "    [cyan]split[/cyan] — emit one .tac per assertion. File i keeps the "
    "i-th assert live; all other AssertCmds become AssumeExpCmds with the "
    "same predicate. Each output is pruned to the cone of influence of the "
    "live assert. Output is a directory with [cyan]assert_<NN>.tac[/cyan] "
    "files and [cyan]manifest.json[/cyan].\n\n"
    "[bold green]Examples[/bold green]\n\n"
    "[cyan]ctac ua f.tac -o f_ua.tac --plain[/cyan]"
    "  [dim]# merge asserts[/dim]\n\n"
    "[cyan]ctac ua f.tac -o f_ua.tac --plain --report[/cyan]"
    "  [dim]# + counts[/dim]\n\n"
    "[cyan]ctac ua f.tac -o split_dir --plain --strategy split[/cyan]"
    "  [dim]# k files, one per assert[/dim]\n\n"
    "[cyan]ctac ua f.tac -o f_ua.tac --plain --no-purify-assert[/cyan]"
    "  [dim]# skip purification[/dim]\n\n"
    "[cyan]ctac ua f.tac -o f_ua.tac --plain --keep-true-asserts[/cyan]"
    "  [dim]# keep assert true[/dim]\n\n"
    "Followup: [cyan]ctac smt f_ua.tac --plain --run[/cyan] to solve the VC."
)


@app.command("ua", rich_help_panel=TRANSFORM_PANEL, epilog=_UA_EPILOG)
def ua_cmd(
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
            help=(
                "For --strategy merge: .tac file to write the merged program. "
                "For --strategy split: directory to populate with "
                "assert_<NN>.tac files + manifest.json (created if missing)."
            ),
        ),
    ] = None,
    strategy: str = typer.Option(
        "merge",
        "--strategy",
        help=(
            "Uniquify-asserts strategy. 'merge' folds every assert into a "
            "single __UA_ERROR block; 'split' emits one .tac per assert "
            "(others become AssumeExpCmd) into the directory named by -o."
        ),
        autocompletion=complete_choices(["merge", "split"]),
    ),
    plain: bool = typer.Option(False, "--plain", help=PLAIN_HELP),
    agent: bool = agent_option(),
    report: bool = typer.Option(
        False, "--report", help="Print counts for each pipeline step."
    ),
    purify_assert: bool = typer.Option(
        True,
        "--purify-assert/--no-purify-assert",
        help=(
            "Run PURIFY_ASSERT before the strategy so every surviving "
            "assertion predicate becomes a named bool. Default on — "
            "turning this off requires predicates to already be SymbolRef "
            "or ConstExpr, otherwise the strategy raises."
        ),
    ),
    drop_true_asserts: bool = typer.Option(
        True,
        "--drop-true-asserts/--keep-true-asserts",
        help=(
            "Run `remove_true_asserts` before the strategy to strip every "
            "trivially-true assertion. Default on."
        ),
    ),
) -> None:
    """Uniquify assertions (merge into one __UA_ERROR block, or split per assert)."""
    _ = agent
    if strategy not in {"merge", "split"}:
        raise typer.BadParameter(
            f"unknown strategy: {strategy!r} (supported: merge, split)",
            param_hint="--strategy",
        )
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

    if strategy == "split" and resolved.project is not None and output_path is None:
        # Split produces a directory of TACs (a fileset). Project
        # ingestion of filesets is phase 3; for now, require an
        # explicit -o so the user opts in to the legacy behavior.
        c.print(
            "# error: --strategy split inside a project requires explicit "
            "-o DIR (fileset ingestion lands in phase 3)",
            markup=False,
        )
        raise typer.Exit(1)

    for w in resolved.warnings:
        c.print(f"# input warning: {w}", markup=False)

    asserts_before = _count_asserts(tac.program)
    if asserts_before == 0:
        c.print(
            "# warning: input has zero asserts; ua is a no-op" if plain
            else "[yellow]warning:[/yellow] input has zero asserts; ua is a no-op",
            markup=not plain,
        )

    program = tac.program

    removed_true = 0
    if drop_true_asserts:
        program, removed = remove_true_asserts(program)
        removed_true = len(removed)

    extra_symbols: tuple[tuple[str, str], ...] = ()
    if purify_assert:
        rewrite = rewrite_program(program, (PURIFY_ASSERT,))
        program = rewrite.program
        extra_symbols = rewrite.extra_symbols

    if strategy == "merge":
        _run_merge(
            c,
            plain=plain,
            tac=tac,
            program=program,
            output_path=output_path,
            project=resolved.project,
            report=report,
            asserts_before=asserts_before,
            removed_true=removed_true,
            extra_symbols=extra_symbols,
            source_path=str(resolved.tac_path),
        )
    else:  # strategy == "split"
        _run_split(
            c,
            plain=plain,
            tac=tac,
            program=program,
            output_path=output_path,
            report=report,
            asserts_before=asserts_before,
            removed_true=removed_true,
            extra_symbols=extra_symbols,
            source_path=str(resolved.tac_path),
        )


def _run_merge(
    c,
    *,
    plain: bool,
    tac,
    program: TacProgram,
    output_path: Optional[Path],
    project,
    report: bool,
    asserts_before: int,
    removed_true: int,
    extra_symbols: tuple[tuple[str, str], ...],
    source_path: str,
) -> None:
    _ = source_path  # merge report doesn't reference it today
    try:
        result = merge_asserts(program)
    except ValueError as e:
        c.print(f"ua error: {e}" if plain else f"[red]ua error:[/red] {e}")
        raise typer.Exit(1) from e

    if report:
        _print_merge_report(
            c,
            plain=plain,
            asserts_before=asserts_before,
            removed_true=removed_true,
            result=result,
        )

    live_extra = filter_live_extra_symbols(extra_symbols, result.program)
    written_path, _info = ingest_or_write_program(
        explicit_output=output_path,
        project=project,
        tac=tac,
        program=result.program,
        extra_symbols=live_extra,
        command="ua",
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


def _run_split(
    c,
    *,
    plain: bool,
    tac,
    program: TacProgram,
    output_path: Optional[Path],
    report: bool,
    asserts_before: int,
    removed_true: int,
    extra_symbols: tuple[tuple[str, str], ...],
    source_path: str,
) -> None:
    if output_path is None:
        c.print(
            "# error: --strategy split requires -o DIR for the output directory",
            markup=False,
        )
        raise typer.Exit(1)
    if output_path.exists() and not output_path.is_dir():
        c.print(
            f"# error: --strategy split expects -o to be a directory; "
            f"{output_path} exists and is not a directory",
            markup=False,
        )
        raise typer.Exit(1)

    result = split_asserts(program)

    output_path.mkdir(parents=True, exist_ok=True)
    outputs_written = 0
    k = len(result.outputs)
    pad = max(2, len(str(max(k - 1, 0))))
    manifest_outputs: list[dict] = []
    for out in result.outputs:
        filename = f"assert_{out.index:0{pad}d}.tac"
        live_extra = filter_live_extra_symbols(extra_symbols, out.program)
        text = render_tac_file(tac, program=out.program, extra_symbols=live_extra)
        (output_path / filename).write_text(text, encoding="utf-8")
        outputs_written += 1
        manifest_outputs.append(
            {
                "file": filename,
                "index": out.index,
                "block_id": out.block_id,
                "cmd_index": out.cmd_index,
                "message": out.message,
            }
        )
    manifest = {
        "strategy": "split",
        "source_path": source_path,
        "asserts_before": result.asserts_before,
        "removed_true_asserts": removed_true,
        "outputs": manifest_outputs,
    }
    (output_path / "manifest.json").write_text(
        json.dumps(manifest, indent=2) + "\n", encoding="utf-8"
    )

    if report:
        _print_split_report(
            c,
            plain=plain,
            asserts_before=asserts_before,
            removed_true=removed_true,
            result=result,
            output_dir=output_path,
            outputs_written=outputs_written,
        )
    elif outputs_written:
        c.print(f"# wrote {outputs_written} files + manifest to {output_path}", markup=False)


def _print_merge_report(
    c,
    *,
    plain: bool,
    asserts_before: int,
    removed_true: int,
    result,
) -> None:
    def line(s: str) -> None:
        c.print(s, markup=not plain)

    if plain:
        line("ua:")
        line("  strategy: merge")
        line(f"  asserts_before: {asserts_before}")
        line(f"  removed_true_asserts: {removed_true}")
        line(f"  asserts_merged: {result.asserts_merged}")
        line(f"  error_block_id: {result.error_block_id or '-'}")
        line(f"  was_noop: {str(result.was_noop).lower()}")
        return
    line("[bold]UA Summary[/bold]")
    line("  strategy: [cyan]merge[/cyan]")
    line(f"  asserts_before: [bold]{asserts_before}[/bold]")
    line(f"  removed_true_asserts: [bold]{removed_true}[/bold]")
    line(f"  asserts_merged:       [bold]{result.asserts_merged}[/bold]")
    line(f"  error_block_id: [cyan]{result.error_block_id or '-'}[/cyan]")
    line(f"  was_noop: [bold]{str(result.was_noop).lower()}[/bold]")


def _print_split_report(
    c,
    *,
    plain: bool,
    asserts_before: int,
    removed_true: int,
    result,
    output_dir: Path,
    outputs_written: int,
) -> None:
    def line(s: str) -> None:
        c.print(s, markup=not plain)

    if plain:
        line("ua:")
        line("  strategy: split")
        line(f"  asserts_before: {asserts_before}")
        line(f"  removed_true_asserts: {removed_true}")
        line(f"  outputs_written: {outputs_written}")
        line(f"  output_dir: {output_dir}")
        line(f"  was_noop: {str(result.was_noop).lower()}")
        return
    line("[bold]UA Summary[/bold]")
    line("  strategy: [cyan]split[/cyan]")
    line(f"  asserts_before: [bold]{asserts_before}[/bold]")
    line(f"  removed_true_asserts: [bold]{removed_true}[/bold]")
    line(f"  outputs_written:      [bold]{outputs_written}[/bold]")
    line(f"  output_dir: [cyan]{output_dir}[/cyan]")
    line(f"  was_noop: [bold]{str(result.was_noop).lower()}[/bold]")
