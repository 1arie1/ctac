"""``ctac pin`` — drop blocks, bind variables, enumerate splits.

Library at :mod:`ctac.transform.pin`; this is a thin façade. When the
input is a directory containing ``manifest.json`` (or ``--show`` is
set), the command renders a summary instead of running.
"""

from __future__ import annotations

import sys
from pathlib import Path
from typing import Annotated, Optional

import typer

from ctac.ast.nodes import ConstExpr
from ctac.parse import ParseError, parse_path
from ctac.tool.cli_runtime import (
    PLAIN_HELP,
    TRANSFORM_PANEL,
    agent_option,
    app,
    console,
    plain_requested,
)
from ctac.tool.project_io import (
    ingest_or_write_dir,
    ingest_or_write_program,
    resolve_project_or_tac,
)
from ctac.tracing import JsonlTrace, NullTrace
from ctac.transform.pin import (
    PinPlan,
    apply,
)
from ctac.transform.pin import enumerate as pin_enumerate
from ctac.transform.pin_manifest import (
    MANIFEST_FILENAME,
    read_manifest,
    summarize_manifest,
    write_manifest,
)


_PIN_EPILOG = (
    "[bold green]What it does[/bold green]  Specialize a TAC by [cyan]"
    "--drop[/cyan] (remove blocks from the CFG with cleanup), "
    "[cyan]--bind[/cyan] (substitute a variable to a constant), and "
    "[cyan]--split[/cyan] (enumerate cases where each split block "
    "keeps exactly one predecessor).\n\n"
    "[bold green]Output[/bold green]  Without [cyan]--split[/cyan], "
    "writes a single [cyan].tac[/cyan]. With [cyan]--split[/cyan], "
    "writes one [cyan].tac[/cyan] per case plus a [cyan]manifest.json"
    "[/cyan] in the output directory.\n\n"
    "[bold green]Show mode[/bold green]  Pass a directory containing "
    "[cyan]manifest.json[/cyan] to render the manifest summary "
    "(implicit when the positional is a directory; force with "
    "[cyan]--show[/cyan]).\n\n"
    "[bold green]Examples[/bold green]\n\n"
    "[cyan]ctac pin f.tac --drop BLK_a -o out.tac --plain[/cyan]\n\n"
    "[cyan]ctac pin f.tac --bind B987=false -o out.tac --plain[/cyan]\n\n"
    "[cyan]ctac pin f.tac --split BLK_J -o out/ --plain[/cyan]\n\n"
    "[cyan]ctac pin out/ --plain[/cyan]"
    "  [dim]# show manifest summary[/dim]\n\n"
    "[bold green]Notes[/bold green]\n\n"
    "[cyan]--drop[/cyan] / [cyan]--bind[/cyan] / [cyan]--split[/cyan] "
    "are repeatable; [cyan]--drop[/cyan] and [cyan]--split[/cyan] each "
    "accept a comma-separated list. [cyan]--bind RC_*[/cyan] is rejected "
    "(use [cyan]--drop[/cyan] on the corresponding block instead).\n\n"
    "[cyan]--trace[/cyan] writes per-decision JSONL events for "
    "debugging."
)


def _parse_const(s: str) -> ConstExpr:
    """Parse a CLI bind value. Accepts ``true``/``false``/numeric
    literals; passes through unchanged."""
    return ConstExpr(s)


def _parse_bind(s: str) -> tuple[str, ConstExpr]:
    if "=" not in s:
        raise typer.BadParameter(
            f"--bind expects VAR=VALUE form (got {s!r})"
        )
    var, _, value = s.partition("=")
    var = var.strip()
    value = value.strip()
    if not var:
        raise typer.BadParameter(f"--bind: empty variable name in {s!r}")
    return (var, _parse_const(value))


def _split_csv(values: list[str]) -> tuple[str, ...]:
    """``--drop a,b --drop c`` becomes ``("a", "b", "c")``."""
    out: list[str] = []
    seen: set[str] = set()
    for raw in values:
        for tok in raw.split(","):
            tok = tok.strip()
            if tok and tok not in seen:
                seen.add(tok)
                out.append(tok)
    return tuple(out)


def _show_summary(
    c, *, plain: bool, dir_path: Path
) -> None:
    try:
        m = read_manifest(dir_path)
    except FileNotFoundError as e:
        c.print(
            f"error: {e}" if plain else f"[red]error:[/red] {e}",
            markup=not plain,
        )
        raise typer.Exit(1) from e
    except ValueError as e:
        c.print(
            f"error: {e}" if plain else f"[red]error:[/red] {e}",
            markup=not plain,
        )
        raise typer.Exit(1) from e
    text = summarize_manifest(m, plain=plain, manifest_dir=dir_path)
    c.print(text, markup=False, end="")


@app.command("pin", rich_help_panel=TRANSFORM_PANEL, epilog=_PIN_EPILOG)
def pin_cmd(
    path: Annotated[
        Optional[Path],
        typer.Argument(
            help=(
                "TAC file or output directory. Directory + manifest.json "
                "triggers show mode."
            ),
        ),
    ] = None,
    drop: Annotated[
        list[str],
        typer.Option(
            "--drop",
            help="Block(s) to drop. Comma-separated; repeatable.",
        ),
    ] = None,
    bind: Annotated[
        list[str],
        typer.Option(
            "--bind",
            help="VAR=VALUE binding. Repeatable. RC vars rejected.",
        ),
    ] = None,
    split: Annotated[
        list[str],
        typer.Option(
            "--split",
            help=(
                "Block(s) to split (enumerate one case per predecessor). "
                "Comma-separated; repeatable."
            ),
        ),
    ] = None,
    output_path: Annotated[
        Optional[Path],
        typer.Option(
            "-o",
            "--output",
            help=(
                "Output file (single-case) or directory (multi-case "
                "with --split)."
            ),
        ),
    ] = None,
    name_style: Annotated[
        str,
        typer.Option(
            "--name-style",
            help="Case filename style: 'descriptive' (default) or 'index'.",
        ),
    ] = "descriptive",
    no_cleanup: Annotated[
        bool,
        typer.Option("--no-cleanup", help="Skip the cleanup rewriter pass."),
    ] = False,
    show: Annotated[
        bool,
        typer.Option(
            "--show",
            help="Force show mode (positional must be a manifest directory).",
        ),
    ] = False,
    trace: Annotated[
        Optional[Path],
        typer.Option(
            "--trace",
            help=(
                "Write JSONL trace of pin decisions and edits to PATH "
                "(use '-' for stdout). Debug-only; verbose."
            ),
        ),
    ] = None,
    plain: bool = typer.Option(False, "--plain", help=PLAIN_HELP),
    agent: bool = agent_option(),
) -> None:
    """Drop blocks, bind variables, enumerate splits on a TAC program."""
    _ = agent
    plain = plain_requested(plain)
    c = console(plain)

    if path is None:
        c.print(
            "error: no input given" if plain
            else "[red]error:[/red] no input given",
            markup=not plain,
        )
        raise typer.Exit(2)

    drop = drop or []
    bind = bind or []
    split = split or []

    drops = _split_csv(drop)
    splits = _split_csv(split)
    try:
        binds = tuple(_parse_bind(s) for s in bind)
    except typer.BadParameter as e:
        c.print(
            f"error: {e}" if plain else f"[red]error:[/red] {e}",
            markup=not plain,
        )
        raise typer.Exit(2) from e

    # Show mode dispatch.
    is_dir_with_manifest = path.is_dir() and (path / MANIFEST_FILENAME).is_file()
    if show:
        if not path.is_dir():
            c.print(
                "error: --show expects a directory with manifest.json"
                if plain
                else "[red]error:[/red] --show expects a directory with "
                "manifest.json",
                markup=not plain,
            )
            raise typer.Exit(2)
        _show_summary(c, plain=plain, dir_path=path)
        return
    if is_dir_with_manifest:
        _show_summary(c, plain=plain, dir_path=path)
        return

    # Run mode.
    try:
        resolved = resolve_project_or_tac(path)
        tac = parse_path(resolved.tac_path)
    except ParseError as e:
        c.print(
            f"parse error: {e}" if plain
            else f"[red]parse error:[/red] {e}",
            markup=not plain,
        )
        raise typer.Exit(1) from e
    except ValueError as e:
        c.print(
            f"input error: {e}" if plain
            else f"[red]input error:[/red] {e}",
            markup=not plain,
        )
        raise typer.Exit(1) from e

    for w in resolved.warnings:
        c.print(f"# input warning: {w}", markup=False)

    plan = PinPlan(
        drops=drops,
        binds=binds,
        splits=splits,
        cleanup=not no_cleanup,
    )

    # Set up trace.
    trace_obj = NullTrace()
    trace_fh = None
    if trace is not None:
        if str(trace) == "-":
            trace_fh = sys.stdout
        else:
            trace_fh = open(trace, "w", encoding="utf-8")
        trace_obj = JsonlTrace(trace_fh)

    try:
        if splits:
            cs = pin_enumerate(tac.program, plan, trace=trace_obj)
            if name_style not in ("descriptive", "index"):
                c.print(
                    f"error: --name-style must be descriptive|index "
                    f"(got {name_style!r})"
                    if plain
                    else "[red]error:[/red] --name-style must be "
                    f"[cyan]descriptive[/cyan]|[cyan]index[/cyan] "
                    f"(got {name_style!r})",
                    markup=not plain,
                )
                raise typer.Exit(2)
            command_str = _reconstruct_command(
                str(path), drops, binds, splits, output_path, no_cleanup
            )

            def _populate_split_dir(dst: Path) -> None:
                write_manifest(
                    cs,
                    dst,
                    source_tac=tac,
                    source_path=str(resolved.tac_path),
                    command=command_str,
                    name_style=name_style,  # type: ignore[arg-type]
                )

            written, _info = ingest_or_write_dir(
                explicit_output=output_path,
                project=resolved.project,
                populate=_populate_split_dir,
                command="pin",
                kind="tac-set",
                advance_head=True,
            )
            if written is None:
                c.print(
                    "# no --output given; pass -o DIR/ to write cases + manifest",
                    markup=False,
                )
                c.print(
                    f"# would write {len(cs.cases)} case(s)",
                    markup=False,
                )
                return
            c.print(
                f"# wrote {len(cs.cases)} case(s) + manifest.json to "
                f"{written}",
                markup=False,
            )
        else:
            res = apply(tac.program, plan, trace=trace_obj)
            written_path, _info = ingest_or_write_program(
                explicit_output=output_path,
                project=resolved.project,
                tac=tac,
                program=res.program,
                command="pin",
                kind="tac",
                advance_head=True,
            )
            if written_path is None:
                c.print(
                    "# no --output given; pass -o FILE.tac to write the result",
                    markup=False,
                )
                c.print(
                    f"# would drop {len(res.dead_blocks)} block(s)",
                    markup=False,
                )
                return
            c.print(f"# wrote {written_path}", markup=False)
    except ValueError as e:
        c.print(
            f"error: {e}" if plain else f"[red]error:[/red] {e}",
            markup=not plain,
        )
        raise typer.Exit(1) from e
    finally:
        if trace_obj is not None:
            trace_obj.close()
        if trace_fh is not None and trace_fh is not sys.stdout:
            trace_fh.close()


def _reconstruct_command(
    input_path: str,
    drops: tuple[str, ...],
    binds: tuple[tuple[str, ConstExpr], ...],
    splits: tuple[str, ...],
    output: Optional[Path],
    no_cleanup: bool,
) -> str:
    parts = ["ctac pin", input_path]
    for d in drops:
        parts.extend(["--drop", d])
    for var, val in binds:
        parts.extend(["--bind", f"{var}={val.value}"])
    for s in splits:
        parts.extend(["--split", s])
    if output is not None:
        parts.extend(["-o", str(output)])
    if no_cleanup:
        parts.append("--no-cleanup")
    return " ".join(parts)
