"""`ctac cover-cfg` — sound CFG cover for single-assert TAC VCs.

Bottom-up cover via probe-based path sampling + K-medoid clustering +
PB linear-path completeness probe. Per the first-SAT-wins rule,
returns immediately on the first SAT slice; otherwise runs the
completeness CEGAR loop to a sound UNSAT verdict (or reports
residual subgoals on timeout).

See `durable/auto-cover-strategy.md` for the technique and
`durable/solver-infrastructure-design.md` for the architecture.
"""
from __future__ import annotations

from pathlib import Path
from typing import Optional

import typer

from ctac.cover.cfg.run import CoverConfig, run_cover_cfg
from ctac.tool.cli_runtime import (
    PLAIN_HELP,
    VERIFY_PANEL,
    agent_option,
    app,
    console,
    plain_requested,
)


_COVER_CFG_EPILOG = (
    "[bold green]Default run[/bold green]  "
    "[cyan]ctac cover-cfg f.tac -o cover/[/cyan]  "
    "samples=32, k=auto, 30s/cluster.\n\n"
    "[bold green]Tight budget[/bold green]  "
    "[cyan]ctac cover-cfg f.tac -o cover/ --samples 16 --budget 15[/cyan]\n\n"
    "[bold green]Pass z3 args[/bold green]  "
    "[cyan]ctac cover-cfg f.tac -o cover/ -- smt.random_seed=42 "
    "tactic.default_tactic=smt[/cyan]  "
    "(cluster solves only; completeness probe stays bare)\n\n"
    "[bold green]Re-verify after[/bold green]  "
    "[cyan]ctac verify-cover cover/manifest.json --plain[/cyan]  "
    "independent re-solve from the manifest.\n\n"
    "Output:\n"
    "  cover/manifest.json   SAT / UNSAT / unknown certificate\n"
    "  cover/rerun.sh        bash audit script\n"
    "  cover/report.md       human-readable summary\n"
    "  cover/cluster_<i>/    per-cluster TAC + smt2 + verdict\n"
    "  cover/completeness/   probe smt2 per iteration\n"
    "  cover/subgoals/       residual subgoals (on unknown)"
)


@app.command('cover-cfg', rich_help_panel=VERIFY_PANEL,
              epilog=_COVER_CFG_EPILOG,
              help='Sound CFG cover (path decomposition + completeness '
                   'probe). First-SAT wins; otherwise proves UNSAT or '
                   'reports residual subgoals.')
def cover_cfg_cmd(
    tac: Path = typer.Argument(
        ..., exists=True, dir_okay=False,
        help='Single-assert TAC file. Run `ctac ua` first if you have '
              'multiple AssertCmds.'),
    output: Path = typer.Option(
        ..., '-o', '--output',
        help='Output directory (created if missing).'),
    samples: int = typer.Option(
        32, '--samples',
        help='Initial random-path samples (before saturation).'),
    k: Optional[int] = typer.Option(
        None, '--k',
        help='K-medoid cluster count. Defaults to one cluster per '
              'sampled path (singleton-per-path).'),
    budget: int = typer.Option(
        30, '--budget',
        help='Per-cluster z3 timeout (seconds).'),
    absorb_budget: int = typer.Option(
        8, '--absorb-budget',
        help='Absorption-probe z3 timeout (seconds). Short on purpose.'),
    absorb_threshold: int = typer.Option(
        5, '--absorb-threshold',
        help='Max Hamming distance for absorbing an escape into a '
              'nearby cluster.'),
    completeness_iter: int = typer.Option(
        30, '--completeness-iter',
        help='Max completeness-loop iterations.'),
    completeness_budget: int = typer.Option(
        30, '--completeness-budget',
        help='Per-iteration completeness-probe z3 timeout.'),
    workers: int = typer.Option(
        4, '--workers',
        help='Parallel cluster-solver count.'),
    seed: int = typer.Option(
        0, '--seed',
        help='RNG seed for path sampling + cluster init.'),
    abort_on_timeout: bool = typer.Option(
        False, '--abort-on-timeout',
        help='If any cluster times out (or returns unknown), abort the '
              'parallel race immediately instead of waiting for the other '
              'clusters. Default off: continue past timeouts so a SAT '
              'cluster in another worker can still win.'),
    core_forbids: bool = typer.Option(
        False, '--core-forbids/--no-core-forbids',
        help='Use unsat-core block projections as `((_ at-most n-1) '
              '...)` forbid clauses in the completeness probe '
              '(experimental, currently UNSOUND). The mechanism '
              'assumes core blocks have path-stable content; with '
              'pin --drop\'s assume injection and shared block '
              'naming across slices, a core from one slice may '
              'reference assumes that don\'t exist (or have different '
              'content) on another path. **Default OFF** until '
              'soundness is addressed; pass `--core-forbids` to '
              're-enable for experiments.'),
    z3_bin: Optional[Path] = typer.Option(
        None, '--z3', help='z3 binary (else CTAC_Z3 / $PATH).'),
    ctac_bin: str = typer.Option(
        'ctac', '--ctac',
        help='ctac binary for the pin/rw/smt sub-steps.'),
    plain: bool = typer.Option(False, '--plain', help=PLAIN_HELP),
    agent: bool = agent_option(),
    z3_extra: Optional[list[str]] = typer.Argument(
        None,
        help='Args after `--` are passed to z3 for cluster solves '
              '(parallel race + singleton-from-escape + absorption '
              'probe). The completeness probe is a different theory '
              'and is always solved with default z3. Example: '
              '`ctac cover-cfg f.tac -o cover/ -- smt.random_seed=42 '
              'tactic.default_tactic=smt`.'),
) -> None:
    _ = agent
    cons = console(plain_requested(plain))
    output.mkdir(parents=True, exist_ok=True)

    config = CoverConfig(
        samples=samples,
        k=k,
        cluster_budget_s=budget,
        absorb_budget_s=absorb_budget,
        absorb_threshold=absorb_threshold,
        completeness_iter=completeness_iter,
        completeness_budget_s=completeness_budget,
        workers=workers,
        seed=seed,
    )

    def emit(line: str) -> None:
        if plain_requested(plain):
            cons.print(f'# {line}')
        else:
            cons.print(f'[dim]{line}[/dim]')

    cluster_args = tuple(z3_extra or [])
    if cluster_args and plain_requested(plain):
        cons.print(f'# z3 cluster args: {" ".join(cluster_args)}')

    result = run_cover_cfg(
        input_tac=tac,
        output_dir=output,
        config=config,
        z3_bin=z3_bin,
        ctac_bin=ctac_bin,
        cluster_z3_args=cluster_args,
        abort_on_timeout=abort_on_timeout,
        disable_forbids=not core_forbids,
        on_event=emit,
    )

    # Summary
    if plain_requested(plain):
        cons.print(f'verdict: {result.verdict}')
        cons.print(f'wall: {result.wall_s:.2f}s')
        cons.print(f'manifest: {result.manifest_path}')
        cons.print(f'report: {result.report_path}')
        cons.print(f'clusters: {result.n_clusters}')
        cons.print(f'completeness_iters: {result.n_completeness_iters}')
        cons.print(f'subgoals: {len(result.subgoals)}')
    else:
        color = {'sat': 'green', 'unsat': 'green',
                  'timeout': 'yellow',
                  'unknown': 'yellow'}.get(result.verdict, 'red')
        cons.print(f'[bold {color}]{result.verdict.upper()}[/bold {color}]  '
                    f'in {result.wall_s:.2f}s')
        cons.print(f'manifest:  {result.manifest_path}')
        cons.print(f'report:    {result.report_path}')
        cons.print(f'rerun:     {result.rerun_sh_path}')
        if result.subgoals:
            cons.print(f'subgoals:  {len(result.subgoals)} residual')

    # Exit code: 0 for SAT/UNSAT verdict, 2 for unknown.
    # Exit codes: 0 for sat/unsat verdict, 2 for partial (timeout/unknown).
    if result.verdict in ('timeout', 'unknown'):
        raise typer.Exit(2)
