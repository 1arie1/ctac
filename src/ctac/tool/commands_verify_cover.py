"""`ctac verify-cover` — independent re-verifier for cover certificates.

Reads a cover manifest (Certificate JSON), re-runs every recorded
z3 invocation, and confirms the verdicts match. Exits 0 on full
match; non-zero if any check deviates. Soundness is a property of
this re-verification: passing here ⇒ the cover verdict is sound,
regardless of any bugs in the cover loop that produced it.
"""
from __future__ import annotations

from pathlib import Path
from typing import Optional

import typer

from ctac.cover.verify import verify
from ctac.tool.cli_runtime import (
    PLAIN_HELP,
    VERIFY_PANEL,
    agent_option,
    app,
    console,
    plain_requested,
)


_VERIFY_COVER_EPILOG = (
    "[bold green]Verify a manifest[/bold green]  "
    "[cyan]ctac verify-cover cover.json --plain[/cyan]\n\n"
    "[bold green]With a specific z3[/bold green]  "
    "[cyan]ctac verify-cover cover.json --z3 ~/ag/z3/wt-master/build/z3[/cyan]\n\n"
    "[bold green]CI-style[/bold green]  "
    "[cyan]ctac verify-cover cover.json --plain && echo OK || echo BAD[/cyan]"
)


@app.command('verify-cover', rich_help_panel=VERIFY_PANEL,
              epilog=_VERIFY_COVER_EPILOG,
              help='Re-verify a cover certificate by re-running every '
                   'recorded z3 invocation.')
def verify_cover_cmd(
    manifest: Path = typer.Argument(
        ..., exists=True, dir_okay=False,
        help='Cover certificate JSON (SAT or UNSAT).'),
    z3_bin: Optional[Path] = typer.Option(
        None, '--z3', help='Override the z3 binary (else uses recorded path '
                            'or $CTAC_Z3 / $PATH).'),
    timeout: int = typer.Option(
        300, '-T', '--timeout',
        help='Per-check timeout in seconds. Each recorded sub-solve gets '
              'this budget independently.'),
    ctac_bin: str = typer.Option(
        'ctac', '--ctac',
        help='ctac binary for the SAT program-replay step.'),
    plain: bool = typer.Option(False, '--plain', help=PLAIN_HELP),
    agent: bool = agent_option(),
) -> None:
    _ = agent
    cons = console(plain_requested(plain))
    report = verify(manifest, z3_bin=z3_bin, timeout_s=timeout,
                     ctac_bin=ctac_bin)

    if plain_requested(plain):
        cons.print(f'cert: {manifest}')
        cons.print(f'kind: {report.cert_kind}')
        for c in report.checks:
            mark = 'ok' if c.passed else 'FAIL'
            cons.print(f'[{mark}] {c.label}  expected={c.expected}  '
                        f'got={c.got}  wall={c.wall_s:.2f}s')
            if not c.passed and c.detail:
                cons.print(f'    {c.detail}')
        cons.print(f'summary: {report.summary()}')
        cons.print(f'result: {"OK" if report.passed else "FAILED"}')
    else:
        from rich.table import Table
        tbl = Table(title=f'ctac verify-cover ({report.cert_kind})',
                     show_lines=False)
        tbl.add_column('check')
        tbl.add_column('expected')
        tbl.add_column('got')
        tbl.add_column('wall', justify='right')
        tbl.add_column('status')
        for c in report.checks:
            status = ('[green]ok[/green]' if c.passed
                       else '[red]FAIL[/red]')
            got_cell = (c.got if c.passed
                         else f'[red]{c.got}[/red]')
            tbl.add_row(c.label, c.expected, got_cell,
                         f'{c.wall_s:.2f}s', status)
        cons.print(tbl)
        if report.passed:
            cons.print(f'[bold green]VERIFY OK[/bold green]  '
                        f'({report.summary()})')
        else:
            cons.print(f'[bold red]VERIFY FAILED[/bold red]  '
                        f'({report.summary()})')

    raise typer.Exit(0 if report.passed else 1)
