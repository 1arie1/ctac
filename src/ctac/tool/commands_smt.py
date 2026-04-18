from __future__ import annotations

from pathlib import Path
from typing import Annotated, Optional

import typer

from ctac.parse import ParseError, parse_path
from ctac.smt import available_encodings, build_vc, render_smt_script
from ctac.tool.cli_runtime import PLAIN_HELP, agent_option, app, console, plain_requested
from ctac.tool.input_resolution import resolve_tac_input_path, resolve_user_path


@app.command("smt")
def smt_cmd(
    path: Optional[Path] = typer.Argument(None),
    plain: bool = typer.Option(False, "--plain", help=PLAIN_HELP),
    agent: bool = agent_option(),
    encoding: Annotated[
        str,
        typer.Option(
            "--encoding",
            help="SMT VC encoding strategy (default: sea_vc).",
        ),
    ] = "sea_vc",
    output_path: Annotated[
        Optional[Path],
        typer.Option("-o", "--output", help="Write SMT-LIB output to this file."),
    ] = None,
) -> None:
    """Emit an SMT-LIB VC for a TAC program.

    Preconditions: loop-free TAC, exactly one AssertCmd, and the AssertCmd is
    the last command in its block.

    Query semantics: SAT iff the assertion-failure state is reachable.
    """
    _ = agent
    plain = plain_requested(plain)
    c = console(plain)
    known_encodings = ", ".join(available_encodings())
    try:
        user_path, user_warnings = resolve_user_path(path)
        tac_path, input_warnings = resolve_tac_input_path(user_path)
        tac = parse_path(tac_path)
        script = build_vc(tac, encoding=encoding)
        smt_text = render_smt_script(script)
    except ParseError as e:
        c.print(f"parse error: {e}" if plain else f"[red]parse error:[/red] {e}")
        raise typer.Exit(1) from e
    except ValueError as e:
        msg = f"{e} (available encodings: {known_encodings})"
        c.print(f"input error: {msg}" if plain else f"[red]input error:[/red] {msg}")
        raise typer.Exit(1) from e

    if plain:
        if tac.path:
            c.print(f"# path: {tac.path}", markup=False)
        c.print(f"# encoding: {encoding}", markup=False)
        for w in user_warnings + input_warnings:
            c.print(f"# input warning: {w}", markup=False)

    if output_path is not None:
        output_path.write_text(smt_text, encoding="utf-8")
        if plain:
            c.print(f"# wrote smt: {output_path}", markup=False)
        else:
            c.print(f"[cyan]wrote smt[/cyan]: [bold]{output_path}[/bold]")
        return

    c.print(smt_text, markup=False, end="")
