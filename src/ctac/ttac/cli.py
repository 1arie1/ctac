"""The ``ttac`` command-line tool.

A small, self-contained Typer app mirroring ``ctac`` conventions
(``--plain`` for deterministic ASCII output, ``-`` for stdin) but with a
much narrower surface: parse a Tiny TAC program and pretty-print it.
"""

from __future__ import annotations

import sys
from collections import Counter
from pathlib import Path

import typer

from . import ast, parse_program, pretty
from .errors import TtacParseError

app = typer.Typer(
    no_args_is_help=True,
    add_completion=False,
    help="ttac - parse and pretty-print Tiny TAC, the VCGen source language.",
)


def _read(file: str) -> str:
    if file == "-":
        return sys.stdin.read()
    path = Path(file)
    if not path.is_file():
        typer.echo(f"error: no such file: {file}", err=True)
        raise typer.Exit(2)
    return path.read_text(encoding="utf-8")


def _parse_or_exit(file: str) -> ast.Program:
    source = _read(file)
    try:
        return parse_program(source)
    except TtacParseError as exc:
        typer.echo(exc.with_caret(source), err=True)
        raise typer.Exit(1) from exc


@app.command()
def parse(
    file: str = typer.Argument(..., help="Tiny TAC file, or '-' for stdin."),
    plain: bool = typer.Option(False, "--plain", help="Deterministic ASCII output."),
) -> None:
    """Parse FILE and report a structural summary (exit 1 on parse error)."""
    program = _parse_or_exit(file)
    n_cmds = sum(len(b.commands) for b in program.blocks)
    kinds = Counter(type(c).__name__ for b in program.blocks for c in b.commands)
    typer.echo(f"ok: {len(program.blocks)} block(s), {n_cmds} command(s)")
    typer.echo(f"entry: {program.entry}")
    typer.echo(f"exit: {program.exit}")
    for kind in sorted(kinds):
        typer.echo(f"  {kind}: {kinds[kind]}")
    _ = plain  # output is ASCII regardless; flag kept for ctac parity


@app.command()
def pp(
    file: str = typer.Argument(..., help="Tiny TAC file, or '-' for stdin."),
    plain: bool = typer.Option(False, "--plain", help="Deterministic ASCII output."),
) -> None:
    """Pretty-print FILE (round-trips through the parser)."""
    program = _parse_or_exit(file)
    typer.echo(pretty(program), nl=False)
    _ = plain


def main() -> None:
    app()


if __name__ == "__main__":
    main()
