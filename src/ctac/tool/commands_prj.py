"""CLI for ``ctac prj`` — manage a ctac project.

Phase 1 commands:

- ``prj init <TAC_FILE> -o <DIR>`` — create a new project at DIR
  with TAC_FILE as the base.
- ``prj list <DIR> [<OBJ_ID>]`` — list project entries.
- ``prj info <DIR> <OBJ_ID> [--recursive]`` — full record for one
  object, optionally walking parents.

The CLI is a thin façade over :mod:`ctac.project` (library-first).
"""

from __future__ import annotations

from pathlib import Path
from typing import Annotated, Optional

import typer

from ctac.project import Project, ProjectError
from ctac.project.types import ObjectInfo
from ctac.tool.cli_runtime import (
    PLAIN_HELP,
    PROJECT_PANEL,
    agent_option,
    app,
    console,
    plain_requested,
)


_PRJ_EPILOG = (
    "[bold green]What is a project?[/bold green]  A working directory "
    "with a [cyan].ctac/[/cyan] sidecar. HEAD is "
    "\"the current TAC\"; intermediate artifacts (TAC, htac, smt2) "
    "are content-addressed in [cyan].ctac/objects/[/cyan] and "
    "exposed as friendly symlinks in the project root "
    "([cyan]in.tac[/cyan], [cyan]in.rw.tac[/cyan], "
    "[cyan]in.rw.ua.tac[/cyan], ...).\n\n"
    "[bold green]Project-aware commands[/bold green]  "
    "Pass [cyan]mytac[/cyan] in place of a [cyan].tac[/cyan] path: "
    "[cyan]rw[/cyan] and [cyan]ua[/cyan] (merge) advance HEAD; "
    "[cyan]pp[/cyan] and [cyan]smt[/cyan] register a sibling object. "
    "Explicit [cyan]-o PATH[/cyan] always bypasses the project.\n\n"
    "[bold green]Examples[/bold green]\n\n"
    "[cyan]ctac prj init f.tac -o mytac --plain[/cyan]"
    "  [dim]# create project[/dim]\n\n"
    "[cyan]ctac rw mytac --plain[/cyan]"
    "  [dim]# HEAD -> in.rw.tac[/dim]\n\n"
    "[cyan]ctac ua mytac --plain[/cyan]"
    "  [dim]# HEAD -> in.rw.ua.tac[/dim]\n\n"
    "[cyan]ctac smt mytac --plain[/cyan]"
    "  [dim]# writes in.rw.ua.smt2 (sibling)[/dim]\n\n"
    "[cyan]ctac prj list mytac --plain[/cyan]"
    "  [dim]# list objects[/dim]\n\n"
    "[cyan]ctac prj info mytac base --plain[/cyan]"
    "  [dim]# show base object provenance[/dim]"
)


prj_app = typer.Typer(
    no_args_is_help=True,
    rich_markup_mode="rich",
    help="Manage a ctac project (HEAD-tracked TAC pipeline workspace).",
    epilog=_PRJ_EPILOG,
)
app.add_typer(prj_app, name="prj", rich_help_panel=PROJECT_PANEL)


# ----------------------------------------------------------- prj init


@prj_app.command("init")
def prj_init(
    tac_file: Annotated[
        Path,
        typer.Argument(
            exists=True,
            file_okay=True,
            dir_okay=False,
            readable=True,
            help="Initial TAC (or htac / smt2) file to use as the project's base.",
        ),
    ],
    output_dir: Annotated[
        Path,
        typer.Option(
            "-o",
            "--output",
            help="Project directory to create. Will be created if missing.",
        ),
    ],
    label: Annotated[
        str,
        typer.Option(
            "-l", "--label",
            help="Label to apply to the base object (default: 'base').",
        ),
    ] = "base",
    force: Annotated[
        bool,
        typer.Option(
            "--force",
            help="Overwrite an existing .ctac/ in the output directory.",
        ),
    ] = False,
    plain: bool = typer.Option(False, "--plain", help=PLAIN_HELP),
    agent: bool = agent_option(),
) -> None:
    """Create a new project at <DIR> with <TAC_FILE> as its base."""
    _ = agent
    plain = plain_requested(plain)
    c = console(plain)
    try:
        prj = Project.init(output_dir, tac_file, label=label, force=force)
    except ProjectError as e:
        c.print(f"project error: {e}" if plain else f"[red]project error:[/red] {e}")
        raise typer.Exit(1) from e

    head = prj.head
    head_link = prj.root / head.names[0] if head.names else None
    if plain:
        c.print(f"project: {prj.root}", markup=False)
        c.print(f"head: {head.sha}", markup=False)
        c.print(f"label: {label}", markup=False)
        if head_link is not None:
            c.print(f"head_path: {head_link}", markup=False)
    else:
        c.print(f"[bold]Created project[/bold] [cyan]{prj.root}[/cyan]")
        c.print(f"  HEAD:    [yellow]{head.sha[:12]}[/yellow]")
        c.print(f"  label:   [magenta]{label}[/magenta]")
        if head_link is not None:
            c.print(f"  HEAD →   [cyan]{head_link}[/cyan]")


# ----------------------------------------------------------- prj list


@prj_app.command("list")
def prj_list(
    project_dir: Annotated[
        Path,
        typer.Argument(
            exists=True,
            file_okay=False,
            dir_okay=True,
            readable=True,
            help="Project directory (the one containing .ctac/).",
        ),
    ],
    obj_id: Annotated[
        Optional[str],
        typer.Argument(help="Optional object id (sha, label, or friendly name)."),
    ] = None,
    plain: bool = typer.Option(False, "--plain", help=PLAIN_HELP),
    agent: bool = agent_option(),
) -> None:
    """List objects in a project (or details on one object)."""
    _ = agent
    plain = plain_requested(plain)
    c = console(plain)
    try:
        prj = Project.open(project_dir)
    except ProjectError as e:
        c.print(f"project error: {e}" if plain else f"[red]project error:[/red] {e}")
        raise typer.Exit(1) from e

    if obj_id is not None:
        try:
            info = prj.info(obj_id)
        except ProjectError as e:
            c.print(f"resolve error: {e}" if plain else f"[red]resolve error:[/red] {e}")
            raise typer.Exit(1) from e
        _print_one(c, prj, info, plain=plain, recursive=False)
        return

    head_sha = prj.head_sha
    objects = prj.list_objects()
    if plain:
        # Tabular: <head?>  <short-sha>  <kind>  <command>  <names>
        c.print("HEAD  sha       kind      command   names", markup=False)
        for o in objects:
            head_marker = "*" if o.sha == head_sha else " "
            names = ",".join(o.names) if o.names else "-"
            c.print(
                f"{head_marker}     {o.sha[:8]}  {o.kind:<8}  "
                f"{o.command:<8}  {names}",
                markup=False,
            )
        # Labels footer.
        if prj.manifest.labels:
            c.print("labels:", markup=False)
            for lbl, sha in sorted(prj.manifest.labels.items()):
                c.print(f"  {lbl} -> {sha[:8]}", markup=False)
    else:
        c.print(f"[bold]Project[/bold] [cyan]{prj.root}[/cyan]")
        c.print(f"  HEAD: [yellow]{head_sha[:12]}[/yellow]")
        c.print("")
        c.print(f"[bold]{len(objects)} object(s)[/bold]")
        for o in objects:
            marker = "[bold green]*[/bold green]" if o.sha == head_sha else " "
            names = ", ".join(o.names) if o.names else "-"
            c.print(
                f"  {marker} [yellow]{o.sha[:8]}[/yellow]  "
                f"[magenta]{o.kind:<8}[/magenta] "
                f"[cyan]{o.command}[/cyan]  {names}"
            )
        if prj.manifest.labels:
            c.print("")
            c.print("[bold]Labels[/bold]")
            for lbl, sha in sorted(prj.manifest.labels.items()):
                c.print(f"  [magenta]{lbl}[/magenta] -> [yellow]{sha[:8]}[/yellow]")


# ----------------------------------------------------------- prj info


@prj_app.command("info")
def prj_info(
    project_dir: Annotated[
        Path,
        typer.Argument(
            exists=True,
            file_okay=False,
            dir_okay=True,
            readable=True,
            help="Project directory (the one containing .ctac/).",
        ),
    ],
    obj_id: Annotated[
        str,
        typer.Argument(help="Object id (sha, short sha, label, or friendly name)."),
    ],
    recursive: Annotated[
        bool,
        typer.Option(
            "-r", "--recursive",
            help="Walk parents back to base, printing each ancestor's record.",
        ),
    ] = False,
    plain: bool = typer.Option(False, "--plain", help=PLAIN_HELP),
    agent: bool = agent_option(),
) -> None:
    """Show full provenance for an object (sha, kind, parents, names, ...)."""
    _ = agent
    plain = plain_requested(plain)
    c = console(plain)
    try:
        prj = Project.open(project_dir)
    except ProjectError as e:
        c.print(f"project error: {e}" if plain else f"[red]project error:[/red] {e}")
        raise typer.Exit(1) from e

    try:
        info = prj.info(obj_id)
    except ProjectError as e:
        c.print(f"resolve error: {e}" if plain else f"[red]resolve error:[/red] {e}")
        raise typer.Exit(1) from e

    _print_one(c, prj, info, plain=plain, recursive=recursive)


# ------------------------------------------------------------ helpers


def _print_one(
    c, prj: Project, info: ObjectInfo, *, plain: bool, recursive: bool
) -> None:
    seen: set[str] = set()
    chain: list[ObjectInfo] = []
    cur: Optional[ObjectInfo] = info
    while cur is not None and cur.sha not in seen:
        chain.append(cur)
        seen.add(cur.sha)
        if not recursive:
            break
        if not cur.parents:
            break
        # Pick the first parent (linear pipeline; multi-parent printing is
        # phase 3 territory once filesets land).
        parent_sha = cur.parents[0]
        cur = prj.manifest.objects.get(parent_sha)

    head_sha = prj.head_sha
    for idx, o in enumerate(chain):
        prefix = "" if not recursive else ("HEAD" if o.sha == head_sha else f"#{idx}")
        if plain:
            if recursive and prefix:
                c.print(f"# {prefix}", markup=False)
            c.print(f"sha: {o.sha}", markup=False)
            c.print(f"kind: {o.kind}", markup=False)
            c.print(f"command: {o.command}", markup=False)
            c.print(f"args: {' '.join(o.args) if o.args else '-'}", markup=False)
            c.print(
                f"parents: {','.join(p[:8] for p in o.parents) if o.parents else '-'}",
                markup=False,
            )
            c.print(
                f"names: {','.join(o.names) if o.names else '-'}",
                markup=False,
            )
            c.print(f"created: {o.created}", markup=False)
            c.print(f"size: {o.size}", markup=False)
            if recursive and idx + 1 < len(chain):
                c.print("", markup=False)
        else:
            if recursive and prefix:
                c.print(f"[bold]{prefix}[/bold]")
            c.print(f"  sha:     [yellow]{o.sha}[/yellow]")
            c.print(f"  kind:    [magenta]{o.kind}[/magenta]")
            c.print(f"  command: [cyan]{o.command}[/cyan]")
            args_disp = " ".join(o.args) if o.args else "-"
            c.print(f"  args:    {args_disp}")
            parents_disp = (
                ", ".join(f"[yellow]{p[:8]}[/yellow]" for p in o.parents)
                if o.parents else "-"
            )
            c.print(f"  parents: {parents_disp}")
            c.print(f"  names:   {', '.join(o.names) if o.names else '-'}")
            c.print(f"  created: {o.created}")
            c.print(f"  size:    {o.size}")
            if recursive and idx + 1 < len(chain):
                c.print("")
