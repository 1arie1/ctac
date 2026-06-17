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
from .analysis import analyze_types, check_dsa, extract_def_use
from .ast import Ty
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


@app.command()
def df(
    file: str = typer.Argument(..., help="Tiny TAC file, or '-' for stdin."),
    plain: bool = typer.Option(False, "--plain", help="Deterministic ASCII output."),
) -> None:
    """Def-use summary and DSA/SSA validity (exit 1 when invalid)."""
    program = _parse_or_exit(file)
    du = extract_def_use(program)
    dsa = check_dsa(program, def_use=du)
    typer.echo(f"def-use: {len(du.symbols)} symbol(s)")
    for sym in sorted(du.symbols):
        n_def = len(du.defs_by_symbol.get(sym, ()))
        n_use = len(du.uses_by_symbol.get(sym, ()))
        typer.echo(f"  {sym}: defs={n_def} uses={n_use}")
    typer.echo(f"dsa: {'valid' if dsa.is_valid else 'invalid'}")
    typer.echo(
        f"  static={len(dsa.static)} phi={len(dsa.phi)} dynamic={len(dsa.dynamic)}"
    )
    for issue in dsa.issues:
        loc = f"{issue.block}:{issue.cmd_index}"
        sym = f" [{issue.symbol}]" if issue.symbol else ""
        typer.echo(f"  {issue.kind} at {loc}{sym}: {issue.detail}")
    _ = plain
    if not dsa.is_valid:
        raise typer.Exit(1)


_SHOW_CHOICES = ("bool", "int", "bytemap", "ref", "unknown", "conflict", "all")


@app.command()
def types(
    file: str = typer.Argument(..., help="Tiny TAC file, or '-' for stdin."),
    show: str = typer.Option("all", "--show", help=f"One of {', '.join(_SHOW_CHOICES)}."),
    plain: bool = typer.Option(False, "--plain", help="Deterministic ASCII output."),
) -> None:
    """Infer every variable's type (exit 1 if the typing is not total)."""
    program = _parse_or_exit(file)
    res = analyze_types(program)

    def kind_of(sym: str) -> str:
        if sym in res.conflicts:
            return "conflict"
        t = res.types[sym]
        return t.value if isinstance(t, Ty) else "unknown"

    for sym in sorted(res.types):
        k = kind_of(sym)
        if show in ("all", k):
            typer.echo(f"  {k} | {sym}")
    for msg in res.errors:
        typer.echo(f"  error: {msg}")

    if not res.is_total:
        unknown = sorted(s for s, t in res.types.items() if t is None and s not in res.conflicts)
        if unknown:
            typer.echo(f"untyped: {', '.join(unknown)}", err=True)
        if res.conflicts:
            typer.echo(f"conflict: {', '.join(sorted(res.conflicts))}", err=True)
        _ = plain
        raise typer.Exit(1)
    _ = plain


def main() -> None:
    app()


if __name__ == "__main__":
    main()
