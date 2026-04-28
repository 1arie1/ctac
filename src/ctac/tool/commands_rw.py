from __future__ import annotations

from pathlib import Path
from typing import Annotated, Optional

import typer
from rich.markup import escape

from ctac.analysis import eliminate_dead_assignments
from ctac.ir.models import TacProgram
from ctac.parse import ParseError, parse_path
from ctac.tool.tac_output import (
    filter_live_extra_symbols,
    render_pp_lines,
    write_program_to_path,
)
from collections import Counter

from ctac.rewrite import rewrite_program
from ctac.rewrite.framework import RewriteResult, RuleHit
from ctac.rewrite.materialize_assumes import materialize_assumes
from ctac.rewrite.rules import (
    CP_ALIAS,
    CSE,
    ITE_PURIFY,
    PURIFY_ASSERT,
    PURIFY_ASSUME,
    R4A_DIV_PURIFY,
    chain_recognition_pipeline,
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


def _print_report(
    c,
    *,
    plain: bool,
    rewrite: RewriteResult,
    dce_removed: int,
    total_cmds_before: int,
    total_cmds_after: int,
    materialize_hits: dict[str, int] | None = None,
) -> None:
    def line(s: str) -> None:
        c.print(s, markup=not plain)

    materialize_hits = materialize_hits or {}
    materialize_total = sum(materialize_hits.values())

    if plain:
        line("rw:")
        line(f"  iterations: {rewrite.iterations}")
        line(f"  rule_hits: {rewrite.total_hits}")
        for name in sorted(rewrite.hits_by_rule):
            line(f"    {name}: {rewrite.hits_by_rule[name]}")
        line(f"  dce_removed: {dce_removed}")
        line(f"  commands_before: {total_cmds_before}")
        line(f"  commands_after: {total_cmds_after}")
        if materialize_hits:
            line(f"  materialized_assumes: {materialize_total}")
            for name in sorted(materialize_hits):
                line(f"    {name}: {materialize_hits[name]}")
        return
    line("[bold]Rewrite Summary[/bold]")
    line(f"  iterations: [bold]{rewrite.iterations}[/bold]")
    line(f"  rule_hits:  [bold]{rewrite.total_hits}[/bold]")
    for name in sorted(rewrite.hits_by_rule):
        line(f"    [cyan]{escape(name)}[/cyan]: {rewrite.hits_by_rule[name]}")
    line(f"  dce_removed: [bold]{dce_removed}[/bold]")
    line(f"  commands_before: {total_cmds_before}")
    line(f"  commands_after:  {total_cmds_after}")
    if materialize_hits:
        line(f"  materialized_assumes: [bold]{materialize_total}[/bold]")
        for name in sorted(materialize_hits):
            line(
                f"    [cyan]{escape(name)}[/cyan]: {materialize_hits[name]}"
            )


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
    all_warnings: list[str] = []
    iterations = 0
    for p in phases:
        all_hits.extend(p.hits)
        for name, n in p.hits_by_rule.items():
            all_counts[name] += n
        all_extras.extend(p.extra_symbols)
        all_warnings.extend(p.warnings)
        iterations += p.iterations
    return RewriteResult(
        program=phases[-1].program,
        hits=tuple(all_hits),
        hits_by_rule=dict(all_counts),
        iterations=iterations,
        extra_symbols=tuple(all_extras),
        warnings=tuple(all_warnings),
    )


_RW_EPILOG = (
    "[bold green]Pipeline[/bold green]\n\n"
    "[bold]1.[/bold] [bold]simplify_pipeline[/bold] — bit-op canonicalization "
    "(N1-N4), div/ceildiv simplifications (R1-R4, R6), boolean/Ite cleanup, "
    "CSE, copy-prop — all iterated to a fixed point.\n\n"
    "[bold]2.[/bold] (optional) [bold]R4a div purification[/bold] — replaces "
    "[cyan]X = Div(A, B)[/cyan] with [cyan]havoc X + euclidean bounds[/cyan] "
    "when [cyan]B[/cyan] has a non-constant positive range. Controlled by "
    "[cyan]--purify-div[/cyan] (default on).\n\n"
    "[bold]3.[/bold] Iterated [bold]DCE[/bold] to remove the residual dead defs.\n\n"
    "[bold]4.[/bold] (optional) [bold]Post-DCE naming phase[/bold]: "
    "[cyan]--purify-ite[/cyan] (default on), "
    "[cyan]--purify-assert[/cyan] (default on), "
    "[cyan]--purify-assume[/cyan] (default off), plus CSE + CP + another DCE sweep.\n\n"
    "Default output: pretty-printed TAC to stdout. With [cyan]-o FILE.tac[/cyan] "
    "emits a round-trippable [cyan].tac[/cyan] file; with "
    "[cyan]-o FILE.htac[/cyan] emits pretty-printed text to a file. Use "
    "[cyan]--report[/cyan] to see per-rule hit counts and DCE stats.\n\n"
    "Soundness is documented by [cyan]ctac rw-valid[/cyan] (per-rule SMT specs).\n\n"
    "[bold green]Examples[/bold green]\n\n"
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
    "  [dim]# also purify assumes[/dim]"
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
    ceildiv_op: bool = typer.Option(
        True,
        "--ceildiv-op/--no-ceildiv-op",
        help=(
            "When R6 collapses the 256-bit ceiling-division chain, emit "
            "`Apply(safe_math_narrow_bv256:bif IntCeilDiv(num, den))` (an "
            "int-typed UF in SMT, axiomatized) instead of fresh havoc + "
            "polynomial-bound assumes. Default on; --no-ceildiv-op uses "
            "the legacy emission as the performance benchmark."
        ),
    ),
    materialize_assumes_flag: bool = typer.Option(
        True,
        "--materialize-assumes/--no-materialize-assumes",
        help=(
            "Run a final pass that materializes range-derived assumes "
            "around uses of axiomatized operators (today: IntCeilDiv). "
            "Strictly gated by interval analysis — every emitted assume "
            "comes from a successful infer_expr_range query, not from "
            "thin air. Targets verification-time solver speed; rw-eq "
            "validates each materialized assume holds under the orig "
            "program's existing constraints. Default on."
        ),
    ),
) -> None:
    """Simplify TAC via the rewrite pipeline (div/bit-field rewrites + DCE)."""
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
    # Phase 0: chain recognition (R6's ceildiv idiom + bit-op
    # canonicalization). Runs in isolation so distribution rules can't
    # rewrite chain-interior expressions before R6 sees them. Without
    # this, SUB_ITE_DIST_RIGHT etc. (in simplify_pipeline) fire on the
    # chain's `Sub(R_high, Ite(...))` before R6 can match the outer
    # IntAdd, silently disabling R6.
    phase0 = rewrite_program(
        tac.program,
        chain_recognition_pipeline,
        max_iterations=max_iterations,
        ite_max_depth=ite_max_depth,
        symbol_sorts=tac.symbol_sorts,
        use_int_ceil_div=ceildiv_op,
    )
    # Phase 1: simplification (bit-ops, const-divisor div rules, boolean/Ite,
    # distribution, range narrowing). Operates on phase 0's output.
    # Phase 2 (optional): add R4a (div purification for non-constant divisors).
    phase1 = rewrite_program(
        phase0.program,
        simplify_pipeline,
        max_iterations=max_iterations,
        ite_max_depth=ite_max_depth,
        symbol_sorts=tac.symbol_sorts,
        use_int_ceil_div=ceildiv_op,
    )
    if purify_div:
        phase2 = rewrite_program(
            phase1.program,
            simplify_pipeline + (R4A_DIV_PURIFY,),
            max_iterations=max_iterations,
            ite_max_depth=ite_max_depth,
            symbol_sorts=tac.symbol_sorts,
            use_int_ceil_div=ceildiv_op,
        )
        rw = _merge_phases(phase0, phase1, phase2)
    else:
        rw = _merge_phases(phase0, phase1)
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
            symbol_sorts=tac.symbol_sorts,
            use_int_ceil_div=ceildiv_op,
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
    # Final phase (gated): selectively materialize range-derived
    # assumes around uses of axiomatized operators (today: IntCeilDiv).
    # Runs LAST so range analysis sees the post-rewrite program; the
    # output flows directly into ctac rw-eq, which validates each
    # materialized assume against the orig program's constraints.
    materialize_hits: dict[str, int] = {}
    if materialize_assumes_flag:
        mres = materialize_assumes(program, symbol_sorts=tac.symbol_sorts)
        program = mres.program
        materialize_hits = mres.hits
    final_program = program
    after_count = _command_count(final_program)

    for w in dict.fromkeys(rw.warnings):
        c.print(f"# rewrite warning: {w}", markup=False)

    if report:
        _print_report(
            c,
            plain=plain,
            rewrite=rw,
            dce_removed=total_removed,
            total_cmds_before=before_count,
            total_cmds_after=after_count,
            materialize_hits=materialize_hits,
        )

    if output_path is not None:
        # Prune symbol-table declarations whose AssignExpCmd was DCE'd
        # so the output's TACSymbolTable doesn't carry orphan
        # ``TCSE<n>:bv256`` lines without a matching def. Annotation-
        # only weak refs are preserved (extract_def_use treats them as
        # uses), so debug metadata stays valid.
        live_extra = filter_live_extra_symbols(rw.extra_symbols, final_program)
        write_program_to_path(
            output_path=output_path,
            tac=tac,
            program=final_program,
            extra_symbols=live_extra,
        )
        if not report:
            c.print(f"# wrote {output_path}", markup=False)
        return

    for ln in render_pp_lines(final_program):
        c.print(ln, markup=False)
