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
from .run import RunConfig, run_program
from .stats import collect_stats, stats_to_dict
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
    text = pretty(program)
    # Syntax-highlight only on a real terminal; piped / --plain output stays
    # plain so it round-trips through the parser unchanged.
    if plain or not sys.stdout.isatty():
        typer.echo(text, nl=False)
        return
    from rich.console import Console

    from .highlight import TTAC_THEME, highlight_line

    console = Console(theme=TTAC_THEME)
    for line in text.splitlines():
        console.print(highlight_line(line), soft_wrap=True)


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


def _fmt_value(v) -> str:
    if v is None:
        return "?"
    return "true" if (v.kind == "bool" and v.data) else "false" if v.kind == "bool" else str(int(v.data))


@app.command()
def run(
    file: str = typer.Argument(..., help="Tiny TAC file, or '-' for stdin."),
    trace: bool = typer.Option(False, "--trace", help="Show a per-command execution trace."),
    entry: str = typer.Option(None, "--entry", help="Entry block label (default: program entry)."),
    max_steps: int = typer.Option(50_000, "--max-steps", min=1, help="Execution step cap."),
    havoc_mode: str = typer.Option("zero", "--havoc-mode", help="zero | random | ask."),
    model: Path = typer.Option(None, "--model", help="Model file (z3/SMT-LIB or TAC) for replay."),
    validate: bool = typer.Option(False, "--validate", help="Compare computed values to the model."),
    plain: bool = typer.Option(False, "--plain", help="Deterministic ASCII output."),
) -> None:
    """Concrete interpreter (desugars references first; replays --model)."""
    program = _parse_or_exit(file)
    tac_model = None
    if model is not None:
        from ctac.eval.model import parse_model_path

        tac_model = parse_model_path(model)
    cfg = RunConfig(
        havoc_mode=havoc_mode, max_steps=max_steps, entry=entry,
        model=tac_model, validate=validate,
    )
    try:
        res = run_program(program, config=cfg)
    except ValueError as exc:
        typer.echo(f"error: {exc}", err=True)
        raise typer.Exit(3) from exc

    typer.echo(f"status: {res.status} ({res.reason})")
    typer.echo(f"steps: {res.steps}")
    typer.echo(f"executed_blocks: {len(res.executed_blocks)}")
    typer.echo(f"assert_ok: {res.assert_ok}")
    typer.echo(f"assert_fail: {res.assert_fail}")
    if validate and tac_model is not None:
        typer.echo(f"mismatches: {res.mismatches}")
    for w in res.warnings:
        typer.echo(f"warning: {w}", err=True)
    if trace:
        _print_trace(res.events, plain=plain)
    raise typer.Exit({"done": 0, "stopped": 2}.get(res.status, 3))


def _print_trace(events, *, plain: bool) -> None:
    use_color = (not plain) and sys.stdout.isatty()
    if not use_color:
        for ev in events:
            val = f"  = {_fmt_value(ev.value)}" if ev.value is not None else ""
            extras = [x for x in (ev.note, ev.mem) if x]
            comment = f"  # {' | '.join(extras)}" if extras else ""
            typer.echo(f"  {ev.block}: {ev.rendered}{val}{comment}")
        return
    from rich.console import Console
    from rich.text import Text

    from .highlight import TTAC_THEME, highlight_line

    console = Console(theme=TTAC_THEME)
    for ev in events:
        t = Text("  ")
        t.append(f"{ev.block}: ", style="ttac.label")
        t.append_text(highlight_line(ev.rendered))
        if ev.value is not None:
            t.append(f"  = {_fmt_value(ev.value)}", style="yellow")
        extras = [x for x in (ev.note, ev.mem) if x]
        if extras:
            t.append(f"  # {' | '.join(extras)}", style="dim")
        console.print(t, soft_wrap=True)


@app.command()
def stats(
    file: str = typer.Argument(..., help="Tiny TAC file, or '-' for stdin."),
    json_out: bool = typer.Option(False, "--json", help="Machine-readable output."),
    plain: bool = typer.Option(False, "--plain", help="Deterministic ASCII output."),
) -> None:
    """Summary statistics: command kinds, bytemap capability, borrows, types."""
    program = _parse_or_exit(file)
    collection = collect_stats(program)
    if json_out:
        typer.echo(json.dumps(stats_to_dict(collection), indent=2))
        return
    from ctac.tool.stats_render import render_plain_stats

    for line in render_plain_stats(collection):
        typer.echo(line)
    _ = plain


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
    z3: str = typer.Option(None, "--z3", help="Path to the z3 binary (else CTAC_Z3 / PATH)."),
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
        _run_solver(res, model, timeout, z3)


def _run_solver(res, model: Path | None, timeout: int | None, z3: str | None) -> None:
    from ctac.smt.runner import run_z3_solver
    from ctac.smt.z3_model import parse_z3_sat_output
    from ctac.solver.z3 import resolve_z3_bin

    try:
        z3_path = str(resolve_z3_bin(z3))
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
