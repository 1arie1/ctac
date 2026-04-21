from __future__ import annotations

from pathlib import Path
from typing import Annotated, Optional

import typer
from rich.markup import escape

from ctac.analysis import eliminate_dead_assignments
from ctac.ast.pretty import configured_printer
from ctac.ast.run_format import pp_terminator_line
from ctac.graph import Cfg
from ctac.ir.models import TacProgram
from ctac.parse import ParseError, parse_path, render_tac_file
from ctac.rewrite import default_pipeline, rewrite_program
from ctac.rewrite.framework import RewriteResult
from ctac.tool.cli_runtime import PLAIN_HELP, agent_option, app, console, plain_requested
from ctac.tool.input_resolution import resolve_tac_input_path, resolve_user_path


def _render_pp_lines(program: TacProgram) -> list[str]:
    pp = configured_printer("human", strip_var_suffixes=True, human_patterns=True)
    out: list[str] = []
    for b in Cfg(program).ordered_blocks():
        out.append(f"{b.id}:")
        for cmd in b.commands:
            line = pp.print_cmd(cmd)
            if line is not None and line != "":
                out.append(f"  {line}")
        term = pp_terminator_line(b, strip_var_suffixes=True)
        if term is not None:
            out.append(f"  {term}")
        elif b.successors:
            out.append(f"  goto {', '.join(b.successors)}")
        else:
            out.append("  stop")
        out.append("")
    return out


def _output_kind(out: Path | None) -> str:
    if out is None:
        return "pp-stdout"
    suffix = out.suffix.lower()
    if suffix == ".htac":
        return "pp"
    return "tac"


def _print_report(
    c, *, plain: bool, rewrite: RewriteResult, dce_removed: int, total_cmds_before: int, total_cmds_after: int,
) -> None:
    def line(s: str) -> None:
        c.print(s, markup=not plain)

    if plain:
        line("rw:")
        line(f"  iterations: {rewrite.iterations}")
        line(f"  rule_hits: {rewrite.total_hits}")
        for name in sorted(rewrite.hits_by_rule):
            line(f"    {name}: {rewrite.hits_by_rule[name]}")
        line(f"  dce_removed: {dce_removed}")
        line(f"  commands_before: {total_cmds_before}")
        line(f"  commands_after: {total_cmds_after}")
        return
    line("[bold]Rewrite Summary[/bold]")
    line(f"  iterations: [bold]{rewrite.iterations}[/bold]")
    line(f"  rule_hits:  [bold]{rewrite.total_hits}[/bold]")
    for name in sorted(rewrite.hits_by_rule):
        line(f"    [cyan]{escape(name)}[/cyan]: {rewrite.hits_by_rule[name]}")
    line(f"  dce_removed: [bold]{dce_removed}[/bold]")
    line(f"  commands_before: {total_cmds_before}")
    line(f"  commands_after:  {total_cmds_after}")


def _command_count(program: TacProgram) -> int:
    return sum(len(b.commands) for b in program.blocks)


@app.command("rw")
def rewrite_cmd(
    path: Annotated[Optional[Path], typer.Argument()] = None,
    output_path: Annotated[
        Optional[Path],
        typer.Option("-o", "--output", help="Write output here. .tac = TAC; .htac = pretty-printed."),
    ] = None,
    plain: bool = typer.Option(False, "--plain", help=PLAIN_HELP),
    agent: bool = agent_option(),
    report: bool = typer.Option(
        False, "--report", help="Print per-rule hit counts and DCE stats."
    ),
    max_iterations: int = typer.Option(
        16, "--max-iter", min=1, help="Fixed-point iteration cap."
    ),
    ite_max_depth: int = typer.Option(
        4,
        "--max-ite-depth",
        min=0,
        help="Max nested Ite levels the range inferrer will union (deeper -> unknown).",
    ),
) -> None:
    """Run the TAC → TAC rewrite pipeline (div/bit-field simplifications + DCE).

    Default output: pretty-printed TAC to stdout. With ``-o FILE.tac`` emits a
    round-trippable ``.tac`` file; with ``-o FILE.htac`` emits pretty-printed
    text to a file.
    """
    _ = agent
    plain = plain_requested(plain)
    c = console(plain)
    try:
        user_path, user_warnings = resolve_user_path(path)
        tac_path, input_warnings = resolve_tac_input_path(user_path)
        tac = parse_path(tac_path)
    except ParseError as e:
        c.print(f"parse error: {e}" if plain else f"[red]parse error:[/red] {e}")
        raise typer.Exit(1) from e
    except ValueError as e:
        c.print(f"input error: {e}" if plain else f"[red]input error:[/red] {e}")
        raise typer.Exit(1) from e

    for w in user_warnings + input_warnings:
        c.print(f"# input warning: {w}", markup=False)

    before_count = _command_count(tac.program)
    rw = rewrite_program(
        tac.program,
        default_pipeline,
        max_iterations=max_iterations,
        ite_max_depth=ite_max_depth,
    )
    dce = eliminate_dead_assignments(rw.program)
    after_count = _command_count(dce.program)

    kind = _output_kind(output_path)

    if report:
        _print_report(
            c,
            plain=plain,
            rewrite=rw,
            dce_removed=len(dce.removed),
            total_cmds_before=before_count,
            total_cmds_after=after_count,
        )

    if kind == "tac":
        assert output_path is not None
        text = render_tac_file(tac, program=dce.program)
        output_path.write_text(text, encoding="utf-8")
        if not report:
            c.print(f"# wrote {output_path}", markup=False)
        return

    lines = _render_pp_lines(dce.program)
    if kind == "pp":
        assert output_path is not None
        output_path.write_text("\n".join(lines) + ("\n" if lines else ""), encoding="utf-8")
        if not report:
            c.print(f"# wrote {output_path}", markup=False)
        return

    for ln in lines:
        c.print(ln, markup=False)
