"""`ctac ua` — uniquify asserts.

Converts a multi-assertion TAC program into one whose assertions have all
been redirected to a single ``__UA_ERROR`` block. See
:mod:`ctac.ua` for the underlying transforms.
"""

from __future__ import annotations

from pathlib import Path
from typing import Annotated, Optional

import typer

from ctac.analysis import remove_true_asserts
from ctac.ast.nodes import AssertCmd
from ctac.ir.models import TacProgram
from ctac.parse import ParseError, parse_path, render_tac_file
from ctac.rewrite import rewrite_program
from ctac.rewrite.rules import PURIFY_ASSERT
from ctac.tool.cli_runtime import PLAIN_HELP, agent_option, app, console, plain_requested
from ctac.tool.input_resolution import resolve_tac_input_path, resolve_user_path
from ctac.ua import merge_asserts


def _count_asserts(program: TacProgram) -> int:
    return sum(
        1 for b in program.blocks for c in b.commands if isinstance(c, AssertCmd)
    )


@app.command("ua")
def ua_cmd(
    path: Annotated[Optional[Path], typer.Argument()] = None,
    output_path: Annotated[
        Optional[Path],
        typer.Option(
            "-o",
            "--output",
            help="Write the uniquified TAC here (.tac). Required.",
        ),
    ] = None,
    strategy: str = typer.Option(
        "merge",
        "--strategy",
        help="Uniquify-asserts strategy. Currently only 'merge' is supported.",
    ),
    plain: bool = typer.Option(False, "--plain", help=PLAIN_HELP),
    agent: bool = agent_option(),
    report: bool = typer.Option(
        False, "--report", help="Print counts for each pipeline step."
    ),
    purify_assert: bool = typer.Option(
        True,
        "--purify-assert/--no-purify-assert",
        help=(
            "Run PURIFY_ASSERT before the strategy so every surviving "
            "assertion predicate becomes a named bool. Default on — "
            "turning this off requires predicates to already be SymbolRef "
            "or ConstExpr, otherwise the strategy raises."
        ),
    ),
    drop_true_asserts: bool = typer.Option(
        True,
        "--drop-true-asserts/--keep-true-asserts",
        help=(
            "Run `remove_true_asserts` before the strategy to strip every "
            "trivially-true assertion. Default on."
        ),
    ),
) -> None:
    """Uniquify assertions: fold every AssertCmd into a single __UA_ERROR block.

    Use this as preprocessing for ``ctac smt``, which requires a single
    assertion. The predicate of each assertion is used verbatim — never
    inverted — so the rewrite preserves the original semantics.

    Pipeline (all steps are optional flags; defaults mirror the typical use case):

    1. ``remove_true_asserts`` — strip every ``assert true``.
    2. ``PURIFY_ASSERT`` rewrite — name each non-trivial predicate as a
       fresh ``TA<N>:bool``.
    3. Apply ``--strategy`` (``merge`` redirects every remaining assert to
       ``__UA_ERROR`` via ``if (P) goto GOOD else goto __UA_ERROR``, with
       ``assume P`` starting each continuation so later asserts can assume
       earlier ones held).

    Examples:
      ctac ua f.tac -o f_ua.tac --plain                  # merge asserts
      ctac ua f.tac -o f_ua.tac --plain --report         # + counts
      ctac ua f.tac -o f_ua.tac --plain --no-purify-assert    # skip purification
      ctac ua f.tac -o f_ua.tac --plain --keep-true-asserts   # keep assert true

    Followup: ``ctac smt f_ua.tac --plain --run`` to solve the VC.
    Single-assert input is a no-op (``was_noop: true``); zero-assert
    input emits a warning.
    """
    _ = agent
    if strategy != "merge":
        raise typer.BadParameter(
            f"unknown strategy: {strategy!r} (supported: merge)", param_hint="--strategy",
        )
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

    asserts_before = _count_asserts(tac.program)
    if asserts_before == 0:
        c.print(
            "# warning: input has zero asserts; ua is a no-op" if plain
            else "[yellow]warning:[/yellow] input has zero asserts; ua is a no-op",
            markup=not plain,
        )

    program = tac.program

    removed_true = 0
    if drop_true_asserts:
        program, removed = remove_true_asserts(program)
        removed_true = len(removed)

    extra_symbols: tuple[tuple[str, str], ...] = ()
    if purify_assert:
        rewrite = rewrite_program(program, (PURIFY_ASSERT,))
        program = rewrite.program
        extra_symbols = rewrite.extra_symbols

    try:
        result = merge_asserts(program)
    except ValueError as e:
        c.print(f"ua error: {e}" if plain else f"[red]ua error:[/red] {e}")
        raise typer.Exit(1) from e

    if report:
        _print_report(
            c,
            plain=plain,
            asserts_before=asserts_before,
            removed_true=removed_true,
            result=result,
            strategy=strategy,
        )

    if output_path is None:
        if not report:
            c.print(
                "# no --output given; pass -o FILE.tac to write the result",
                markup=False,
            )
        return

    text = render_tac_file(tac, program=result.program, extra_symbols=extra_symbols)
    output_path.write_text(text, encoding="utf-8")
    if not report:
        c.print(f"# wrote {output_path}", markup=False)


def _print_report(
    c,
    *,
    plain: bool,
    asserts_before: int,
    removed_true: int,
    result,
    strategy: str,
) -> None:
    def line(s: str) -> None:
        c.print(s, markup=not plain)

    if plain:
        line("ua:")
        line(f"  strategy: {strategy}")
        line(f"  asserts_before: {asserts_before}")
        line(f"  removed_true_asserts: {removed_true}")
        line(f"  asserts_merged: {result.asserts_merged}")
        line(f"  error_block_id: {result.error_block_id or '-'}")
        line(f"  was_noop: {str(result.was_noop).lower()}")
        return
    line("[bold]UA Summary[/bold]")
    line(f"  strategy: [cyan]{strategy}[/cyan]")
    line(f"  asserts_before: [bold]{asserts_before}[/bold]")
    line(f"  removed_true_asserts: [bold]{removed_true}[/bold]")
    line(f"  asserts_merged:       [bold]{result.asserts_merged}[/bold]")
    line(f"  error_block_id: [cyan]{result.error_block_id or '-'}[/cyan]")
    line(f"  was_noop: [bold]{str(result.was_noop).lower()}[/bold]")
