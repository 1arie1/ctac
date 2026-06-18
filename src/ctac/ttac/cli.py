"""The ``ttac`` command-line tool.

A small, self-contained Typer app mirroring ``ctac`` conventions
(``--plain`` for deterministic ASCII output, ``-`` for stdin) but with a
much narrower surface: parse a Tiny TAC program and pretty-print it.
"""

from __future__ import annotations

import json
import sys
from collections import Counter
from pathlib import Path

import typer

from . import ast, parse_program, pretty
from .analysis import analyze_types, check_dsa, extract_def_use
from .ast import Ty
from .errors import TtacParseError, TtacTypeError, VcGenError
from .transform import desugar_refs, merge_asserts, split_asserts
from .vcgen import generate_vc

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


@app.command()
def ua(
    file: str = typer.Argument(..., help="Tiny TAC file, or '-' for stdin."),
    strategy: str = typer.Option("merge", "--strategy", help="'merge' or 'split'."),
    output: Path = typer.Option(
        None, "-o", "--output", help="Output file (merge) or directory (split)."
    ),
    report: bool = typer.Option(False, "--report", help="Print counts."),
    plain: bool = typer.Option(False, "--plain", help="Deterministic ASCII output."),
) -> None:
    """Uniquify assertions: merge into one __UA_ERROR sink, or split per assert."""
    program = _parse_or_exit(file)
    if strategy == "merge":
        _run_merge(program, output, report)
    elif strategy == "split":
        _run_split(program, file, output, report)
    else:
        typer.echo(f"error: unknown strategy {strategy!r} (merge|split)", err=True)
        raise typer.Exit(2)
    _ = plain


def _run_merge(program: ast.Program, output: Path | None, report: bool) -> None:
    res = merge_asserts(program)
    text = pretty(res.program)
    if output is not None:
        output.write_text(text, encoding="utf-8")
    else:
        typer.echo(text, nl=False)
    if report:
        typer.echo("ua:", err=True)
        typer.echo("  strategy: merge", err=True)
        typer.echo(f"  asserts_merged: {res.asserts_merged}", err=True)
        typer.echo(f"  error_block: {res.error_block}", err=True)
        typer.echo(f"  was_noop: {str(res.was_noop).lower()}", err=True)


def _run_split(program: ast.Program, file: str, output: Path | None, report: bool) -> None:
    if output is None:
        typer.echo("error: split requires -o DIR", err=True)
        raise typer.Exit(2)
    if output.exists() and not output.is_dir():
        typer.echo(f"error: -o must be a directory: {output}", err=True)
        raise typer.Exit(2)

    res = split_asserts(program)
    output.mkdir(parents=True, exist_ok=True)
    manifest_outputs = []
    for out in res.outputs:
        name = f"assert_{out.index:02d}.ttac"
        (output / name).write_text(pretty(out.program), encoding="utf-8")
        manifest_outputs.append(
            {"file": name, "index": out.index, "block": out.block, "cond": out.cond_name}
        )
    manifest = {
        "strategy": "split",
        "source": file,
        "asserts_before": res.asserts_before,
        "outputs": manifest_outputs,
    }
    (output / "manifest.json").write_text(json.dumps(manifest, indent=2), encoding="utf-8")

    if report:
        typer.echo("ua:", err=True)
        typer.echo("  strategy: split", err=True)
        typer.echo(f"  asserts_before: {res.asserts_before}", err=True)
        typer.echo(f"  outputs_written: {len(res.outputs)}", err=True)
        typer.echo(f"  output_dir: {output}", err=True)
        typer.echo(f"  was_noop: {str(res.was_noop).lower()}", err=True)


@app.command()
def desugar(
    file: str = typer.Argument(..., help="Tiny TAC file, or '-' for stdin."),
    output: Path = typer.Option(None, "-o", "--output", help="Write the result here."),
    plain: bool = typer.Option(False, "--plain", help="Deterministic ASCII output."),
) -> None:
    """Desugar references/borrows into a reference-free Tiny TAC program."""
    program = _parse_or_exit(file)
    try:
        res = desugar_refs(program)
    except ValueError as exc:
        typer.echo(f"error: {exc}", err=True)
        raise typer.Exit(1) from exc
    text = pretty(res.program)
    if output is not None:
        output.write_text(text, encoding="utf-8")
    else:
        typer.echo(text, nl=False)
    _ = plain


@app.command()
def vcgen(
    file: str = typer.Argument(..., help="Tiny TAC file, or '-' for stdin."),
    cfg_encoding: str = typer.Option("bwd0", "--cfg-encoding", help="CFG-constraint encoding."),
    output: Path = typer.Option(None, "-o", "--output", help="Write the SMT-LIB VC here."),
    solve: bool = typer.Option(False, "--solve", help="Run z3 on the VC immediately."),
    model: Path = typer.Option(None, "--model", help="On sat, write the z3 model here."),
    timeout: int = typer.Option(None, "--timeout", help="z3 timeout in seconds."),
    plain: bool = typer.Option(False, "--plain", help="Deterministic ASCII output."),
) -> None:
    """Generate a seahorn-style SMT VC (merges multiple asserts first)."""
    program = _parse_or_exit(file)
    try:
        res = generate_vc(program, cfg_encoding=cfg_encoding)
    except (VcGenError, TtacTypeError) as exc:
        typer.echo(f"error: {exc}", err=True)
        raise typer.Exit(1) from exc

    if res.merged:
        typer.echo(
            f"note: merged {res.asserts_before} assertions into a single __UA_ERROR sink",
            err=True,
        )

    if output is not None:
        output.write_text(res.smt_text, encoding="utf-8")
    elif not solve:
        typer.echo(res.smt_text, nl=False)

    _ = plain
    if solve:
        _run_solver(res, model, timeout)


def _run_solver(res, model: Path | None, timeout: int | None) -> None:
    from ctac.smt.runner import run_z3_solver
    from ctac.smt.z3_model import parse_z3_sat_output
    from ctac.solver.z3 import resolve_z3_bin

    try:
        z3_path = str(resolve_z3_bin(None))
    except FileNotFoundError as exc:
        typer.echo(f"error: {exc}", err=True)
        raise typer.Exit(1) from exc

    result = run_z3_solver(
        smt_text=res.smt_text,
        z3_path=z3_path,
        timeout_seconds=timeout,
        seed=0,
        tactic="default",
        extra_args=[],
        want_model=model is not None,
    )
    if result.timed_out:
        typer.echo("timeout")
        raise typer.Exit(2)
    out = parse_z3_sat_output(result.stdout)
    typer.echo(out.status)
    if out.status == "sat" and model is not None:
        model.write_text(out.model_text, encoding="utf-8")


def main() -> None:
    app()


if __name__ == "__main__":
    main()
