"""`ctac z3` — run z3 with classification + parallel orchestration.

Modes:
  ctac z3 <FILE.smt2>                       # single config, live display
  ctac z3 <FILE.smt2> --seeds 0-7           # seed range, dashboard
  ctac z3 <FILE.smt2> --configs default,alt # multiple configs
  ctac z3 <FILE.smt2> --configs ... --seeds 0-3  # cross-product, parallel

Race semantics: first sat/unsat verdict wins; remaining tasks cancelled.
"""
from __future__ import annotations

import os
import shlex
import time
from pathlib import Path
from typing import Optional

import typer
from rich.live import Live
from rich.panel import Panel
from rich.table import Table

from ctac.solver import (
    DiagnosticSignature,
    ProgressEvent,
    RaceTask,
    Z3Config,
    Z3Runner,
    Z3RunResult,
    race,
    resolve_configs,
    save_winning_config,
)
from ctac.solver.z3 import resolve_z3_bin
from ctac.tool.cli_runtime import (
    PLAIN_HELP,
    VERIFY_PANEL,
    agent_option,
    app,
    console,
    plain_requested,
)


_Z3_EPILOG = (
    "[bold green]One config, one seed[/bold green]  "
    "[cyan]ctac z3 f.smt2 -T 60 --seed 0[/cyan]  with live -v:2 + signature.\n\n"
    "[bold green]Seed sweep[/bold green]  "
    "[cyan]ctac z3 f.smt2 --seeds 0-7 -j 4[/cyan]  race seeds; first verdict wins.\n\n"
    "[bold green]Config × seeds[/bold green]  "
    "[cyan]ctac z3 f.smt2 --configs default,alt-then,bp-off --seeds 0-3 -j auto[/cyan]\n\n"
    "[bold green]Pass through to z3[/bold green]  "
    "[cyan]ctac z3 f.smt2 -- smt.arith.solver=2[/cyan]  args after [bold]--[/bold] go to z3.\n\n"
    "[bold green]Save the winning rerun[/bold green]  "
    "[cyan]ctac z3 ... --save-rerun winner.sh[/cyan] or "
    "[cyan]--save-config winner.json[/cyan]\n\n"
    "[bold green]Discoverable configs[/bold green]  "
    "drops a [bold].ctac-z3-configs.json[/bold] in the input file's directory "
    "(or any ancestor) to add custom named configs alongside the defaults."
)


_Z3_AGENT_GUIDE = """ctac z3 agent guide (plain, terse)

WHAT: Run z3 on an SMT2 file with adaptive observation + classification.
Spawns z3 with `-v:2 -st`, parses stderr into a progress timeline,
classifies the run (fast-close, lp-bp-blowup, nlsat-stuck, ...),
optionally races seeds and configs in parallel.

WHY beat manual `z3 -T:N -smt2 f.smt2`:
- Single source for z3 invocation with consistent stats parsing.
- Bottleneck signature surfaces "is this stuck, or just running?".
- Seed/config racing built-in (first-verdict-wins, kills the rest).
- Always emits a copy-paste rerun command for the winning combo.

CANONICAL INVOCATIONS:
- one-shot:        ctac z3 f.smt2 -T 60 --plain
- seed sweep:      ctac z3 f.smt2 --seeds 0-7 -j 4 --plain
- config × seeds:  ctac z3 f.smt2 --configs default,alt-then,bp-off --seeds 0-3 --plain
- pass-through:    ctac z3 f.smt2 -- smt.arith.solver=2

LIST CONFIGS: ctac z3 --list-configs

PLAIN MODE: deterministic line-per-result output for piping. The Rich
dashboard fires only on an interactive TTY without `--plain`.
"""


def _parse_seeds(spec: str) -> list[int]:
    """Parse `0-7` or `0,2,7-9` into a sorted list of unique seeds."""
    seeds: set[int] = set()
    for part in spec.split(','):
        part = part.strip()
        if not part:
            continue
        if '-' in part:
            lo, hi = part.split('-', 1)
            seeds.update(range(int(lo), int(hi) + 1))
        else:
            seeds.add(int(part))
    return sorted(seeds)


def _resolve_workers(spec: str) -> int:
    if spec == 'auto':
        return max(1, (os.cpu_count() or 2) // 2)
    return max(1, int(spec))


def _build_rerun_cmd(z3_bin: Path, smt2: Path, timeout_s: int, seed: int,
                       config: Z3Config) -> str:
    parts = [str(z3_bin), f'-T:{timeout_s}', '-st', '-smt2', str(smt2),
             f'smt.random_seed={seed}', f'sat.random_seed={seed}']
    parts += list(config.args)
    return ' '.join(shlex.quote(p) for p in parts)


def _format_signature(sig: DiagnosticSignature) -> str:
    margin_s = ''
    if sig.runner_up:
        ru_label, ru_conf = sig.runner_up
        margin = sig.margin if sig.margin is not None else 0.0
        margin_s = f'  (runner-up: {ru_label} {ru_conf:.2f}, margin {margin:+.2f})'
    return f'{sig.label} (conf {sig.confidence:.2f}){margin_s}'


# -------------------- single-instance live display ---------------------------


def _run_single_live(*, smt2: Path, timeout_s: int, seed: int,
                       config: Z3Config, z3_bin: Path, extra_args: list[str],
                       plain: bool) -> Z3RunResult:
    """Run one z3 instance with a live dashboard (or plain stream)."""
    cons = console(plain)
    args = list(config.args) + list(extra_args)
    runner = Z3Runner(smt2=smt2, timeout_s=timeout_s, seed=seed,
                       z3_bin=z3_bin, extra_args=args)

    if plain:
        cons.print(f'# z3 {config.name} seed={seed} timeout={timeout_s}s')
        cons.print(f'# args: {config.shell_args()}')

        def on_event(ev: ProgressEvent) -> None:
            if ev.kind == 'tactic-start':
                cons.print(f'# tactic-start {ev.payload.get("tactic","?")} @ {ev.wall_s:.2f}s')
            elif ev.kind == 'smt-stats':
                p = ev.payload
                cons.print(f'# smt-stats @ {ev.wall_s:.2f}s  '
                            f'r={p["restarts"]} confl={p["conflicts"]} '
                            f'dec={p["decisions"]} prop={p["propagations"]} '
                            f'mem={p["memory_mb"]:.1f}MB')

        result = runner.run(on_event=on_event)
        return result

    # Rich live mode: rolling tail of recent events + status panel
    recent_events: list[ProgressEvent] = []

    def render() -> Panel:
        n_smt = sum(1 for e in recent_events if e.kind == 'smt-stats')
        n_nls = sum(1 for e in recent_events if e.kind == 'nlsat-line')
        lines: list[str] = []
        for ev in recent_events[-8:]:
            if ev.kind == 'tactic-start':
                lines.append(f'[cyan]tactic[/cyan]  {ev.payload.get("tactic","?")}'
                              f'  [dim]@ {ev.wall_s:.2f}s[/dim]')
            elif ev.kind == 'smt-stats':
                p = ev.payload
                lines.append(f'[green]smt[/green]    '
                              f'r={p["restarts"]} confl={p["conflicts"]} '
                              f'dec={p["decisions"]} prop={p["propagations"]} '
                              f'mem={p["memory_mb"]:.1f}MB  [dim]@ {ev.wall_s:.2f}s[/dim]')
            elif ev.kind == 'nlsat-line':
                p = ev.payload
                lines.append(f'[yellow]nlsat[/yellow]  c={p["conflicts"]} '
                              f'p={p["propagations"]} cl={p["clauses"]}  '
                              f'[dim]@ {ev.wall_s:.2f}s[/dim]')
        title = (f'z3 {config.name} seed={seed} T={timeout_s}s  '
                  f'[dim]({n_smt} smt-stats, {n_nls} nlsat)[/dim]')
        body = '\n'.join(lines) if lines else '[dim]waiting for z3...[/dim]'
        return Panel(body, title=title, border_style='blue')

    def on_event(ev: ProgressEvent) -> None:
        recent_events.append(ev)

    with Live(render(), console=cons, refresh_per_second=4,
               transient=True) as live:
        # Update the live panel periodically
        import threading
        stop = threading.Event()
        def updater() -> None:
            while not stop.is_set():
                live.update(render())
                time.sleep(0.25)
        t = threading.Thread(target=updater, daemon=True)
        t.start()
        try:
            result = runner.run(on_event=on_event)
        finally:
            stop.set()
            t.join(timeout=1.0)
    return result


# -------------------- multi-task dashboard -----------------------------------


def _short_event_summary(status) -> str:
    """One-line synopsis of a task's most recent event (used as a tail
    hint for the live signature column)."""
    if not status.events:
        return '[dim]starting...[/dim]'
    ev = status.events[-1]
    p = ev.payload
    k = status.last_event_kind
    if k == 'tactic-start':
        return f'tactic={p.get("tactic","?")}'
    if k == 'smt-stats':
        return (f'c={p.get("conflicts",0)} '
                 f'd={p.get("decisions",0)} '
                 f'mem={p.get("memory_mb",0):.0f}MB')
    if k == 'nlsat-line':
        return (f'nl_c={p.get("conflicts",0)} '
                 f'nl_cl={p.get("clauses",0)}')
    return f'{k}'


def _verdict_styled(verdict: str | None) -> str:
    if verdict is None:
        return '-'
    if verdict in ('sat', 'unsat'):
        return f'[bold green]{verdict}[/bold green]'
    if verdict in ('timeout', 'aborted', 'error'):
        return f'[red]{verdict}[/red]'
    return verdict


def _wall_str(status) -> str:
    """Wall column: live elapsed for running, final wall for done."""
    if status.status == 'running':
        e = status.elapsed_now()
        return f'{e:.1f}s' if e is not None else '-'
    if status.wall_s is not None:
        return f'{status.wall_s:.2f}s'
    return '-'


def _signature_str(status) -> str:
    """Live signature column: classifier label + confidence + tail hint."""
    if status.signature_label is not None:
        # Done — use final signature
        return f'{status.signature_label} ({status.signature_confidence:.2f})'
    if status.status == 'running':
        live = status.live_signature()
        if live is None:
            return '[dim]waiting...[/dim]'
        label, conf = live
        # Add a faint tail hint showing what's happening at the tactic level
        tail = _short_event_summary(status)
        return f'{label} ({conf:.2f})  [dim]{tail}[/dim]'
    return '-'


def _run_multi_dashboard(*, tasks: list[RaceTask], max_concurrent: int,
                           plain: bool) -> tuple[RaceTask | None, Z3RunResult | None, list]:
    """Run many tasks in parallel; show a build-system-style task table."""
    from ctac.solver.race import TaskStatus

    cons = console(plain)

    def render(state: dict[str, TaskStatus]) -> Table:
        n_done = sum(1 for s in state.values() if s.status == 'done')
        n_run = sum(1 for s in state.values() if s.status == 'running')
        n_pend = sum(1 for s in state.values() if s.status == 'pending')
        title = (f'ctac z3 ({len(tasks)} tasks, -j {max_concurrent})  '
                  f'[dim]done={n_done} running={n_run} pending={n_pend}[/dim]')
        tbl = Table(title=title, show_lines=False)
        tbl.add_column('task')
        tbl.add_column('status')
        tbl.add_column('verdict')
        tbl.add_column('wall', justify='right')
        tbl.add_column('signature')
        for label, s in state.items():
            if s.status == 'running':
                status_cell = '[cyan]running[/cyan]'
            elif s.status == 'done':
                status_cell = '[green]done[/green]'
            elif s.status == 'error':
                status_cell = '[red]error[/red]'
            else:
                status_cell = '[dim]pending[/dim]'

            tbl.add_row(label, status_cell, _verdict_styled(s.verdict),
                         _wall_str(s), _signature_str(s))
        return tbl

    if plain:
        # Plain mode: log lifecycle transitions (start/done) — no live elapsed
        cons.print(f'# ctac z3: {len(tasks)} tasks, -j {max_concurrent}')
        for t in tasks:
            cons.print(f'#   pending: {t.label}')
        announced: set[str] = set()

        def on_status_plain(state: dict[str, 'TaskStatus']) -> None:
            for label, s in state.items():
                if s.status == 'running' and label not in announced:
                    announced.add(label)
                    cons.print(f'start  {label}')

        def on_complete_plain(task: RaceTask, result: Z3RunResult) -> None:
            sig = (f'{result.signature.label}/{result.signature.confidence:.2f}'
                    if result.signature else '-')
            cons.print(f'done   {task.label:<40} {result.verdict:<8} '
                        f'{result.wall_s:>6.2f}s   {sig}')

        race_result = race(tasks, max_concurrent=max_concurrent,
                            on_complete=on_complete_plain,
                            on_status=on_status_plain)
    else:
        # Rich live dashboard
        from rich.live import Live as _Live
        initial_state = {t.label: __import__('ctac.solver.race', fromlist=['TaskStatus']).TaskStatus(label=t.label, status='pending') for t in tasks}
        with _Live(render(initial_state), console=cons, refresh_per_second=4,
                    transient=False, auto_refresh=False) as live:
            def on_status_rich(state: dict[str, 'TaskStatus']) -> None:
                live.update(render(state), refresh=True)

            race_result = race(tasks, max_concurrent=max_concurrent,
                                on_complete=None,
                                on_status=on_status_rich,
                                status_refresh_s=0.25)

    return race_result.winner_task, race_result.winner_result, race_result.all_results


# -------------------- the command --------------------------------------------


@app.command('z3', rich_help_panel=VERIFY_PANEL, epilog=_Z3_EPILOG,
              help='Run z3 with classification + seed/config racing.')
def z3_cmd(
    smt2: Optional[Path] = typer.Argument(
        None, exists=False,
        help='SMT2 input file (omit only with --list-configs).'),
    timeout: int = typer.Option(60, '-T', '--timeout',
                                  help='Per-task z3 timeout in seconds.'),
    seed: int = typer.Option(0, '--seed',
                              help='Single-task seed (ignored if --seeds is set).'),
    seeds: Optional[str] = typer.Option(
        None, '--seeds',
        help='Seed range/list, e.g. "0-7" or "0,2,7-9". Triggers seed sweep.'),
    configs: Optional[str] = typer.Option(
        None, '--configs',
        help='Comma-separated config names (default, alt-then, bp-off, ...). '
              'Omit for single "default" config.'),
    jobs: str = typer.Option('auto', '-j', '--jobs',
                              help='Parallel worker count, or "auto" (= cpu/2).'),
    z3_bin: Optional[Path] = typer.Option(
        None, '--z3', help='Path to z3 binary (else CTAC_Z3 env or $PATH).'),
    save_rerun: Optional[Path] = typer.Option(
        None, '--save-rerun', help='Write the winning rerun command to this path.'),
    save_config: Optional[Path] = typer.Option(
        None, '--save-config', help='Save winning Z3Config as JSON to this path.'),
    show_output: bool = typer.Option(
        False, '--show-output',
        help='Print the winning task\'s z3 stdout (model, get-info :reason-unknown, '
              'unsat-core, etc. — whatever the smt2 asked for and z3 returned).'),
    save_output: Optional[Path] = typer.Option(
        None, '--save-output',
        help='Write the winning task\'s z3 stdout to a file. Useful for capturing '
              'large models.'),
    list_configs: bool = typer.Option(
        False, '--list-configs', help='Print available configs and exit.'),
    plain: bool = typer.Option(False, '--plain', help=PLAIN_HELP),
    agent: bool = agent_option(),
    z3_extra: Optional[list[str]] = typer.Argument(
        None, help='Args after `--` are passed verbatim to z3.'),
) -> None:
    _ = agent
    cons = console(plain_requested(plain))

    # --list-configs (no smt2 needed)
    if list_configs:
        start = smt2 if smt2 else Path.cwd()
        pool = resolve_configs(start)
        if plain_requested(plain):
            for c in pool:
                args_s = ' '.join(c.args) if c.args else '(no args)'
                cons.print(f'{c.name:<22} {args_s}')
                if c.description:
                    cons.print(f'{"":<22} # {c.description}')
        else:
            tbl = Table(title='Available z3 configs', show_lines=False)
            tbl.add_column('name')
            tbl.add_column('args')
            tbl.add_column('description', style='dim')
            for c in pool:
                tbl.add_row(c.name, ' '.join(c.args), c.description)
            cons.print(tbl)
        raise typer.Exit(0)

    if smt2 is None:
        cons.print('[red]error:[/red] missing SMT2 argument '
                    '(or use --list-configs)')
        raise typer.Exit(2)
    if not smt2.exists():
        cons.print(f'[red]error:[/red] file not found: {smt2}')
        raise typer.Exit(2)

    z3_path = resolve_z3_bin(z3_bin)
    workers = _resolve_workers(jobs)
    extra_args = list(z3_extra or [])

    # Resolve configs
    config_names = [s.strip() for s in configs.split(',')] if configs else None
    if config_names is None:
        # Single default config — but still allow extra_args pass-through.
        config_list = [Z3Config(name='default', args=tuple(extra_args))]
    else:
        config_list = resolve_configs(smt2, config_names)
        if extra_args:
            # Append extras to every named config
            config_list = [Z3Config(name=c.name, args=c.args + tuple(extra_args),
                                      description=c.description)
                            for c in config_list]

    # Resolve seeds
    seed_list = _parse_seeds(seeds) if seeds else [seed]

    # MODE selection
    n_configs = len(config_list)
    n_seeds = len(seed_list)
    n_tasks = n_configs * n_seeds

    if n_tasks == 1:
        # MODE 1: single instance, live display
        cfg = config_list[0]
        s = seed_list[0]
        result = _run_single_live(
            smt2=smt2, timeout_s=timeout, seed=s, config=cfg,
            z3_bin=z3_path, extra_args=[], plain=plain_requested(plain))
        _print_single_result(cons, result, cfg, s, smt2, timeout, z3_path,
                              save_rerun, save_config, show_output, save_output,
                              plain_requested(plain))
        return

    # MODE 2/3: race across tasks
    tasks = [RaceTask(config=c, seed=s, smt2=smt2, timeout_s=timeout,
                       z3_bin=z3_path)
             for c in config_list for s in seed_list]

    winner_task, winner_result, all_results = _run_multi_dashboard(
        tasks=tasks, max_concurrent=workers, plain=plain_requested(plain))

    _print_race_summary(cons, winner_task, winner_result, all_results,
                          smt2, timeout, z3_path, save_rerun, save_config,
                          show_output, save_output, plain_requested(plain))


def _print_single_result(cons, result: Z3RunResult, cfg: Z3Config, seed: int,
                          smt2: Path, timeout: int, z3_bin: Path,
                          save_rerun: Path | None, save_config: Path | None,
                          show_output: bool, save_output: Path | None,
                          plain: bool) -> None:
    cons.print()
    cons.print(f'verdict   : [bold]{result.verdict}[/bold]')
    cons.print(f'wall      : {result.wall_s:.2f}s')
    cons.print(f'signature : {_format_signature(result.signature)}')
    cons.print(f'rationale : {result.signature.rationale}')
    if result.signature.suggested_actions:
        cons.print('actions   : ' + '; '.join(result.signature.suggested_actions))
    cmd = _build_rerun_cmd(z3_bin, smt2, timeout, seed, cfg)
    cons.print()
    cons.print('rerun:')
    cons.print(f'  {cmd}')
    if save_rerun:
        save_rerun.write_text(f'#!/bin/bash\n# generated by ctac z3\n{cmd}\n')
        save_rerun.chmod(0o755)
        cons.print(f'(rerun script saved to {save_rerun})')
    if save_config:
        save_winning_config(cfg, save_config)
        cons.print(f'(config saved to {save_config})')
    _emit_z3_output(cons, result.stdout, show_output, save_output)


def _emit_z3_output(cons, stdout: str, show_output: bool,
                      save_output: Path | None) -> None:
    """Print the winner's z3 stdout (model, get-info, etc.) on demand."""
    if save_output is not None:
        save_output.write_text(stdout)
        cons.print(f'(z3 stdout saved to {save_output})')
    if show_output:
        cons.print()
        cons.print('--- z3 stdout ---')
        cons.print(stdout, highlight=False, markup=False, end='')
        if not stdout.endswith('\n'):
            cons.print()
        cons.print('--- end z3 stdout ---')


def _print_race_summary(cons, winner_task: RaceTask | None,
                          winner_result: Z3RunResult | None,
                          all_results: list,
                          smt2: Path, timeout: int, z3_bin: Path,
                          save_rerun: Path | None, save_config: Path | None,
                          show_output: bool, save_output: Path | None,
                          plain: bool) -> None:
    cons.print()
    if winner_task is None:
        cons.print('[red]no winner[/red] — all tasks failed to produce sat/unsat')
        if all_results:
            cons.print('losers:')
            for t, r in all_results:
                cons.print(f'  {t.label:<40} {r.verdict:<8} {r.wall_s:.2f}s')
        raise typer.Exit(1)

    cons.print(f'[bold green]winner[/bold green]: {winner_task.label}')
    cons.print(f'verdict   : [bold]{winner_result.verdict}[/bold]')
    cons.print(f'wall      : {winner_result.wall_s:.2f}s')
    if winner_result.signature:
        cons.print(f'signature : {_format_signature(winner_result.signature)}')
        cons.print(f'rationale : {winner_result.signature.rationale}')
    cmd = _build_rerun_cmd(z3_bin, smt2, timeout, winner_task.seed,
                              winner_task.config)
    cons.print()
    cons.print('rerun:')
    cons.print(f'  {cmd}')
    if save_rerun:
        save_rerun.write_text(f'#!/bin/bash\n# generated by ctac z3\n{cmd}\n')
        save_rerun.chmod(0o755)
        cons.print(f'(rerun script saved to {save_rerun})')
    if save_config:
        save_winning_config(winner_task.config, save_config)
        cons.print(f'(config saved to {save_config})')
    _emit_z3_output(cons, winner_result.stdout, show_output, save_output)
