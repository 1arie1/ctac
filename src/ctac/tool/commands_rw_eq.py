"""`ctac rw-eq` — equivalence checker for the rewriter.

Walks two TAC programs in lockstep and emits one merged TAC program
with ``assert`` commands at every site where the two sides disagree.
The merged program then composes with ``ctac ua --strategy split`` +
``ctac smt`` to verify each site individually.
"""

from __future__ import annotations

import sys
from pathlib import Path
from typing import Annotated, Optional

import typer

from ctac.parse import ParseError, parse_path, render_tac_file
from ctac.rw_eq import EquivContractError, emit_equivalence_program
from ctac.tool.tac_output import write_program_to_path
from ctac.tool.cli_runtime import (
    PLAIN_HELP,
    VALIDATE_PANEL,
    agent_option,
    app,
    console,
    plain_requested,
)
from ctac.tool.input_resolution import resolve_tac_input_path, resolve_user_path


_RW_EQ_EPILOG = (
    "[bold green]What it does[/bold green]  Walks the original and "
    "rewritten TAC programs in lockstep, emitting one merged TAC where "
    "every site at which the two sides differ becomes an "
    "[cyan]assert[/cyan]. The merged file is consumed by the rest of "
    "the verification pipeline ([cyan]ctac ua --strategy split[/cyan] + "
    "[cyan]ctac smt[/cyan]) — no new SMT-layer code, equivalence "
    "queries reuse the existing VC machinery.\n\n"
    "[bold green]Inputs contract[/bold green]  Both inputs must have "
    "the same set of block ids and the same successor list per block. "
    "Variable names are preserved by the rewriter, so the walker uses "
    "a single namespace; the only exception is rule 6 (rehavoc, R4A "
    "pattern) which mints a fresh [cyan]X__rw_eq<n>[/cyan] for the "
    "rehavoc'd LHS variable.\n\n"
    "[bold green]Soundness note[/bold green]  Rule 6 admits the "
    "rewriter's post-havoc assume conditions without checking they're "
    "jointly satisfiable. Pass [cyan]--check-feasibility[/cyan] to "
    "insert per-rehavoc-window [cyan]assert false[/cyan] probes that "
    "catch contradictory assumes. Pass [cyan]--strict[/cyan] to abort "
    "instead of admitting; if you do that, re-run [cyan]ctac rw[/cyan] "
    "with [cyan]--no-purify-div[/cyan] and friends to get a "
    "rehavoc-free [cyan]rw.tac[/cyan], and lean on [cyan]ctac rw-valid"
    "[/cyan] for those rules' soundness.\n\n"
    "[bold green]Examples[/bold green]\n\n"
    "[cyan]ctac rw-eq orig.tac rw.tac -o eq.tac --plain[/cyan]\n\n"
    "[cyan]ctac rw-eq orig.tac rw.tac -o eq.tac --plain --report[/cyan]"
    "  [dim]# rule-hit counts + rehavoc sites[/dim]\n\n"
    "[cyan]ctac rw-eq orig.tac rw.tac -o eq.tac --strict[/cyan]"
    "  [dim]# abort on rule 6[/dim]\n\n"
    "[cyan]ctac rw-eq orig.tac rw.tac -o eq.tac --check-feasibility[/cyan]"
    "  [dim]# add feasibility probes[/dim]\n\n"
    "Followup: [cyan]ctac ua eq.tac --strategy split -o split[/cyan] "
    "then [cyan]for f in split/*.tac; do ctac smt \"$f\" --run; done[/cyan]."
)


@app.command("rw-eq", rich_help_panel=VALIDATE_PANEL, epilog=_RW_EQ_EPILOG)
def rw_eq_cmd(
    orig_path: Annotated[
        Path,
        typer.Argument(
            help="Original TAC file (the input to ctac rw).",
        ),
    ],
    rw_path: Annotated[
        Path,
        typer.Argument(
            help="Rewritten TAC file (the output of ctac rw).",
        ),
    ],
    output_path: Annotated[
        Optional[Path],
        typer.Option(
            "-o",
            "--output",
            help=(
                "Write the merged equivalence-check TAC here. "
                ".tac = round-trippable TAC; .htac = pretty-printed."
            ),
        ),
    ] = None,
    plain: bool = typer.Option(False, "--plain", help=PLAIN_HELP),
    agent: bool = agent_option(),
    strict: bool = typer.Option(
        False,
        "--strict",
        help=(
            "Abort with exit code 2 on any rule-6 (rehavoc) trigger "
            "instead of admitting it. Use to enforce that no "
            "soundness-quirky shortcuts are taken."
        ),
    ),
    check_feasibility: bool = typer.Option(
        False,
        "--check-feasibility",
        help=(
            "Insert an `assert false` immediately before each rule-6 "
            "close site so a downstream solver can detect whether the "
            "rehavoc window's assumes are jointly satisfiable."
        ),
    ),
    report: bool = typer.Option(
        False, "--report", help="Print rule-hit counts and rehavoc sites."
    ),
) -> None:
    """Emit a merged equivalence-check TAC for (orig, rw)."""
    _ = agent
    plain = plain_requested(plain)
    c = console(plain)

    orig_path_str, rw_path_str = str(orig_path), str(rw_path)
    try:
        user_orig, ow = resolve_user_path(orig_path)
        orig_resolved, oiw = resolve_tac_input_path(user_orig)
        user_rw, rw_w = resolve_user_path(rw_path)
        rw_resolved, riw = resolve_tac_input_path(user_rw)
        orig_tac = parse_path(orig_resolved)
        rw_tac = parse_path(rw_resolved)
    except ParseError as e:
        c.print(f"parse error: {e}" if plain else f"[red]parse error:[/red] {e}")
        raise typer.Exit(1) from e
    except ValueError as e:
        c.print(f"input error: {e}" if plain else f"[red]input error:[/red] {e}")
        raise typer.Exit(1) from e

    for w in ow + oiw + rw_w + riw:
        c.print(f"# input warning: {w}", markup=False)

    try:
        result = emit_equivalence_program(
            orig_tac.program,
            rw_tac.program,
            strict=strict,
            check_feasibility=check_feasibility,
        )
    except EquivContractError as e:
        msg = f"rw-eq error: {e}"
        c.print(msg if plain else f"[red]{msg}[/red]")
        # Strict-mode rule-6 hit uses a distinct exit code so CI can
        # distinguish "soundness shortcut taken" from "broken inputs".
        exit_code = 2 if "rule-6 rehavoc" in str(e) else 1
        raise typer.Exit(exit_code) from e

    extra_symbols = result.extra_symbols

    if output_path is None:
        # No -o: stream raw TAC to stdout. Useful for piping into a
        # follow-up command. Pretty-printed output is opt-in via -o
        # FILE.htac (matches the convention of `ctac rw`).
        text = render_tac_file(
            orig_tac, program=result.program, extra_symbols=extra_symbols
        )
        if plain:
            sys.stdout.write(text)
        else:
            c.print(text)
    else:
        write_program_to_path(
            output_path=output_path,
            tac=orig_tac,
            program=result.program,
            extra_symbols=extra_symbols,
        )

    if report:
        _print_report(c, plain=plain, result=result, output_path=output_path)
    elif output_path is not None:
        c.print(f"# wrote {output_path}", markup=False)

    # Loud rehavoc warning to stderr regardless of --report.
    if result.rehavoc_sites:
        warn = (
            f"WARNING: {len(result.rehavoc_sites)} rehavoc admission(s) used "
            f"(rule 6). The verifier did not check that the rewriter's post-"
            f"havoc assumes are satisfiable. Pass --check-feasibility for "
            f"per-window probes, or --strict to abort instead."
        )
        print(warn, file=sys.stderr)
        for site in result.rehavoc_sites:
            print(
                f"  - {site.block_id}:{site.cmd_index} {site.var_name} -> {site.shadow_name}",
                file=sys.stderr,
            )

    _ = orig_path_str, rw_path_str  # reserved for future report fields


def _print_report(c, *, plain: bool, result, output_path) -> None:
    def line(s: str) -> None:
        c.print(s, markup=not plain)

    if plain:
        line("rw-eq:")
        for rule in sorted(result.rule_hits):
            line(f"  rule_{rule}: {result.rule_hits[rule]}")
        line(f"  asserts_emitted: {result.asserts_emitted}")
        line(f"  feasibility_asserts: {result.feasibility_asserts_emitted}")
        line(f"  rehavoc_admissions: {len(result.rehavoc_sites)}")
        if output_path is not None:
            line(f"  output: {output_path}")
        return
    line("[bold]RW-EQ Summary[/bold]")
    for rule in sorted(result.rule_hits):
        line(f"  rule_{rule}: [bold]{result.rule_hits[rule]}[/bold]")
    line(f"  asserts_emitted: [bold]{result.asserts_emitted}[/bold]")
    line(f"  feasibility_asserts: [bold]{result.feasibility_asserts_emitted}[/bold]")
    color = "red" if result.rehavoc_sites else "green"
    line(f"  rehavoc_admissions: [{color}]{len(result.rehavoc_sites)}[/{color}]")
    if output_path is not None:
        line(f"  output: [cyan]{output_path}[/cyan]")
