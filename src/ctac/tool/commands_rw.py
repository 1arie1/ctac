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
from collections import Counter

from ctac.rewrite import rewrite_program
from ctac.rewrite.framework import RewriteResult, RuleHit
from ctac.rewrite.rules import (
    CP_ALIAS,
    CSE,
    ITE_PURIFY,
    PURIFY_ASSERT,
    PURIFY_ASSUME,
    R4A_DIV_PURIFY,
    simplify_pipeline,
)
from ctac.tool.cli_runtime import (
    PLAIN_HELP,
    TRANSFORM_PANEL,
    agent_option,
    app,
    console,
    plain_requested,
)
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


def _merge_phases(*phases: RewriteResult) -> RewriteResult:
    """Combine the outputs of sequential :func:`rewrite_program` invocations.

    Hits, per-rule counts, and extra symbols accumulate; the final program is
    the output of the last phase. Iterations sum across phases.
    """
    if not phases:
        raise ValueError("need at least one phase")
    all_hits: list[RuleHit] = []
    all_counts: Counter[str] = Counter()
    all_extras: list[tuple[str, str]] = []
    iterations = 0
    for p in phases:
        all_hits.extend(p.hits)
        for name, n in p.hits_by_rule.items():
            all_counts[name] += n
        all_extras.extend(p.extra_symbols)
        iterations += p.iterations
    return RewriteResult(
        program=phases[-1].program,
        hits=tuple(all_hits),
        hits_by_rule=dict(all_counts),
        iterations=iterations,
        extra_symbols=tuple(all_extras),
    )


_RW_EPILOG = (
    "[bold]Examples:[/bold]\n\n"
    "[cyan]ctac rw f.tac --plain[/cyan]"
    "  [dim]# pp to stdout[/dim]\n\n"
    "[cyan]ctac rw f.tac --plain --report[/cyan]"
    "  [dim]# + per-rule hit counts[/dim]\n\n"
    "[cyan]ctac rw f.tac -o small.tac --plain[/cyan]"
    "  [dim]# write round-trippable .tac[/dim]\n\n"
    "[cyan]ctac rw f.tac -o small.htac --plain[/cyan]"
    "  [dim]# write pretty-printed .htac[/dim]\n\n"
    "[cyan]ctac rw f.tac --no-purify-div --plain[/cyan]"
    "  [dim]# disable R4a[/dim]\n\n"
    "[cyan]ctac rw f.tac --purify-assume --plain[/cyan]"
    "  [dim]# also purify assumes[/dim]\n\n"
    "Soundness is documented by [cyan]ctac rw-valid[/cyan] (per-rule SMT specs)."
)


@app.command("rw", rich_help_panel=TRANSFORM_PANEL, epilog=_RW_EPILOG)
def rewrite_cmd(
    path: Annotated[
        Optional[Path],
        typer.Argument(
            help="Path to .tac / .sbf.json file, or a Certora output directory.",
        ),
    ] = None,
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
    purify_div: bool = typer.Option(
        True,
        "--purify-div/--no-purify-div",
        help=(
            "Enable R4a (replace `X = Div(A, B)` with `havoc X; B*X <= A < B*(X+1)` "
            "for non-constant positive-range B). Default on."
        ),
    ),
    purify_ite: bool = typer.Option(
        True,
        "--purify-ite/--no-purify-ite",
        help=(
            "Name non-trivial Ite conditions as fresh bool vars (TB<N>) so the "
            "solver can split cases cleanly. Runs as a final phase after DCE. "
            "Default on."
        ),
    ),
    purify_assert: bool = typer.Option(
        True,
        "--purify-assert/--no-purify-assert",
        help=(
            "Name every non-trivial AssertCmd predicate as a fresh bool var "
            "(TA<N>). Runs in the post-DCE phase. Default on."
        ),
    ),
    purify_assume: bool = typer.Option(
        False,
        "--purify-assume/--no-purify-assume",
        help=(
            "Name every non-trivial AssumeExpCmd condition as a fresh bool var "
            "(TA<N>). Runs in the post-DCE phase. Default off."
        ),
    ),
) -> None:
    """Run the TAC → TAC rewrite pipeline (div/bit-field simplifications + DCE).

    Pipeline phases:
    1. ``simplify_pipeline`` — bit-op canonicalization (N1-N4), div/ceildiv
       simplifications (R1-R4, R6), boolean/Ite cleanup, CSE, copy-prop —
       all iterated to a fixed point.
    2. (optional) R4a div purification — replaces ``X = Div(A, B)`` with
       ``havoc X + euclidean bounds`` when ``B`` has a non-constant positive
       range. Controlled by ``--purify-div`` (default on).
    3. Iterated DCE to remove the residual dead defs.
    4. (optional) Post-DCE naming phase: ``--purify-ite`` (default on),
       ``--purify-assert`` (default on), ``--purify-assume`` (default off),
       plus CSE + CP + another DCE sweep.

    Default output: pretty-printed TAC to stdout. With ``-o FILE.tac`` emits
    a round-trippable ``.tac`` file; with ``-o FILE.htac`` emits
    pretty-printed text to a file. Use ``--report`` to see per-rule hit
    counts and DCE stats.
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
    # Phase 1: simplification (bit-ops, const-divisor div rules, R6, boolean/Ite).
    # Phase 2 (optional): add R4a (div purification for non-constant divisors).
    # Splitting ensures R6 and peephole rules get first crack at the ceiling
    # chain before R4a replaces any `Div` with a fresh symbol.
    phase1 = rewrite_program(
        tac.program,
        simplify_pipeline,
        max_iterations=max_iterations,
        ite_max_depth=ite_max_depth,
    )
    if purify_div:
        phase2 = rewrite_program(
            phase1.program,
            simplify_pipeline + (R4A_DIV_PURIFY,),
            max_iterations=max_iterations,
            ite_max_depth=ite_max_depth,
        )
        rw = _merge_phases(phase1, phase2)
    else:
        rw = phase1
    # Iterate DCE to fixed point: a chain of dead defs needs multiple sweeps
    # because liveness is computed once per pass and each pass only removes
    # the directly-dead leaves.
    program = rw.program
    total_removed = 0
    while True:
        dce = eliminate_dead_assignments(program)
        total_removed += len(dce.removed)
        if not dce.removed:
            break
        program = dce.program
    # Phase 3 (optional): after all simplification + DCE, name every remaining
    # non-trivial Ite condition as a fresh bool var, then do the same for
    # assert predicates and (optionally) assume conditions. Pair with CSE +
    # CP so that two expressions with identical structure collapse to one
    # T<N> instead of producing structurally-equal defs.
    phase_rules: list = []
    if purify_ite:
        phase_rules.append(ITE_PURIFY)
    if purify_assert:
        phase_rules.append(PURIFY_ASSERT)
    if purify_assume:
        phase_rules.append(PURIFY_ASSUME)
    if phase_rules:
        phase_rules.extend((CSE, CP_ALIAS))
        phase_ite = rewrite_program(
            program,
            tuple(phase_rules),
            max_iterations=max_iterations,
            ite_max_depth=ite_max_depth,
        )
        rw = _merge_phases(rw, phase_ite)
        program = phase_ite.program
        # One more DCE sweep — CSE turns duplicates into aliases; CP+DCE
        # makes those aliases disappear.
        while True:
            dce = eliminate_dead_assignments(program)
            total_removed += len(dce.removed)
            if not dce.removed:
                break
            program = dce.program
    final_program = program
    after_count = _command_count(final_program)

    kind = _output_kind(output_path)

    if report:
        _print_report(
            c,
            plain=plain,
            rewrite=rw,
            dce_removed=total_removed,
            total_cmds_before=before_count,
            total_cmds_after=after_count,
        )

    if kind == "tac":
        assert output_path is not None
        text = render_tac_file(tac, program=final_program, extra_symbols=rw.extra_symbols)
        output_path.write_text(text, encoding="utf-8")
        if not report:
            c.print(f"# wrote {output_path}", markup=False)
        return

    lines = _render_pp_lines(final_program)
    if kind == "pp":
        assert output_path is not None
        output_path.write_text("\n".join(lines) + ("\n" if lines else ""), encoding="utf-8")
        if not report:
            c.print(f"# wrote {output_path}", markup=False)
        return

    for ln in lines:
        c.print(ln, markup=False)
