from __future__ import annotations

import re
import shlex
import tempfile
import os
import time
from pathlib import Path
from typing import Annotated, Optional

import typer

from ctac.analysis.symbols import canonical_symbol
from ctac.parse import ParseError, parse_path
from ctac.smt.encoding.path_skeleton import sanitize_ident
from ctac.smt.runner import parse_z3_args, run_z3_solver
from ctac.smt import available_encodings, build_vc, render_smt_script
from ctac.smt.z3_model import parse_z3_sat_output, z3_model_to_tac_model_text
from ctac.tool.cli_runtime import PLAIN_HELP, agent_option, app, console, plain_requested
from ctac.tool.input_resolution import resolve_tac_input_path, resolve_user_path

_SYMBOL_LINE = re.compile(r"^\s*([A-Za-z_][A-Za-z0-9_]*):([A-Za-z0-9_]+)\s*$")


def _model_symbol_sorts(symbol_table_text: str) -> dict[str, str]:
    out: dict[str, str] = {}
    for line in symbol_table_text.splitlines():
        m = _SYMBOL_LINE.match(line)
        if m is None:
            continue
        sym = canonical_symbol(m.group(1), strip_var_suffixes=True)
        out[sanitize_ident(sym)] = m.group(2)
    return out


@app.command("smt")
def smt_cmd(
    path: Optional[Path] = typer.Argument(None),
    plain: bool = typer.Option(False, "--plain", help=PLAIN_HELP),
    agent: bool = agent_option(),
    encoding: Annotated[
        str,
        typer.Option(
            "--encoding",
            help="SMT VC encoding strategy (default: sea_vc).",
        ),
    ] = "sea_vc",
    output_path: Annotated[
        Optional[Path],
        typer.Option("-o", "--output", help="Write SMT-LIB output to this file."),
    ] = None,
    run: bool = typer.Option(
        False,
        "--run/--no-run",
        help="Run Z3 on the generated SMT-LIB instance.",
    ),
    z3_path: Annotated[
        str,
        typer.Option("--z3-path", help="Path to z3 executable (default: z3)."),
    ] = "z3",
    z3_args: Annotated[
        str,
        typer.Option("--z3-args", help="Extra options passed to z3 as a shell-like string."),
    ] = "",
    tactic: Annotated[
        str,
        typer.Option("--tactic", help="Z3 default tactic (`tactic.default_tactic`, default: default)."),
    ] = "default",
    seed: Annotated[
        int,
        typer.Option("--seed", help="Z3 random seed (`smt.random_seed`, default: 0)."),
    ] = 0,
    timeout: Annotated[
        Optional[int],
        typer.Option("--timeout", min=1, help="Z3 timeout in seconds (`-T:<seconds>`)."),
    ] = None,
    model_output_path: Annotated[
        Optional[Path],
        typer.Option(
            "--model",
            help="Write TAC model output to this path when solver returns sat.",
        ),
    ] = None,
    unsat_core: bool = typer.Option(
        False,
        "--unsat-core",
        help=(
            "Emit named TAC asserts and Z3 unsat-core options; with --run, print core on unsat. "
            "Cannot be combined with --model."
        ),
    ),
    debug: bool = typer.Option(
        False,
        "--debug/--no-debug",
        help="Print solver interaction details for debugging.",
    ),
) -> None:
    """Emit an SMT-LIB VC for a TAC program.

    Preconditions: loop-free TAC, exactly one AssertCmd, and the AssertCmd is
    the last command in its block.

    Query semantics: SAT iff the assertion-failure state is reachable.
    Use `--run` to execute z3 and `--model` to write SAT model in TAC format.
    """
    _ = agent
    plain = plain_requested(plain)
    c = console(plain)
    if unsat_core and model_output_path is not None:
        msg = "cannot combine --unsat-core with --model"
        c.print(f"input error: {msg}" if plain else f"[red]input error:[/red] {msg}")
        raise typer.Exit(1)
    known_encodings = ", ".join(available_encodings())
    try:
        user_path, user_warnings = resolve_user_path(path)
        tac_path, input_warnings = resolve_tac_input_path(user_path)
        tac = parse_path(tac_path)
        script = build_vc(tac, encoding=encoding, unsat_core=unsat_core)
        smt_text = render_smt_script(script)
    except ParseError as e:
        c.print(f"parse error: {e}" if plain else f"[red]parse error:[/red] {e}")
        raise typer.Exit(1) from e
    except ValueError as e:
        msg = f"{e} (available encodings: {known_encodings})"
        c.print(f"input error: {msg}" if plain else f"[red]input error:[/red] {msg}")
        raise typer.Exit(1) from e

    if plain:
        if tac.path:
            c.print(f"# path: {tac.path}", markup=False)
        c.print(f"# encoding: {encoding}", markup=False)
        for w in user_warnings + input_warnings:
            c.print(f"# input warning: {w}", markup=False)

    if output_path is not None:
        output_path.write_text(smt_text, encoding="utf-8")
        if plain:
            c.print(f"# wrote smt: {output_path}", markup=False)
        else:
            c.print(f"[cyan]wrote smt[/cyan]: [bold]{output_path}[/bold]")
        if not run:
            return

    if not run:
        c.print(smt_text, markup=False, end="")
        return

    run_text = smt_text if unsat_core else smt_text + "(get-model)\n"
    extra_args = parse_z3_args(z3_args)
    replay_script_path: Path | None = None
    if debug:
        fd, tmp_name = tempfile.mkstemp(prefix="ctac-smt-z3-", suffix=".smt2")
        with os.fdopen(fd, "w", encoding="utf-8") as f:
            f.write(run_text)
        replay_script_path = Path(tmp_name)
    started_at = time.monotonic()
    try:
        if plain:
            z3_res = run_z3_solver(
                smt_text=run_text,
                z3_path=z3_path,
                timeout_seconds=timeout,
                seed=seed,
                tactic=tactic,
                extra_args=extra_args,
            )
        else:
            last_bucket = -1

            with c.status("[cyan]running z3... 0s[/cyan]", spinner="dots") as st:

                def _progress(elapsed_s: float) -> None:
                    nonlocal last_bucket
                    bucket = int(elapsed_s // 5) * 5
                    if bucket != last_bucket:
                        last_bucket = bucket
                        st.update(f"[cyan]running z3... {bucket}s[/cyan]")

                z3_res = run_z3_solver(
                    smt_text=run_text,
                    z3_path=z3_path,
                    timeout_seconds=timeout,
                    seed=seed,
                    tactic=tactic,
                    extra_args=extra_args,
                    progress_cb=_progress,
                )
    except KeyboardInterrupt as e:
        c.print("interrupted: terminated z3 cleanly" if plain else "[yellow]interrupted[/yellow]: terminated z3 cleanly")
        raise typer.Exit(130) from e
    except OSError as e:
        c.print(f"z3 launch error: {e}" if plain else f"[red]z3 launch error:[/red] {e}")
        raise typer.Exit(1) from e
    elapsed_s = time.monotonic() - started_at

    if plain:
        c.print(f"# solver: {' '.join(z3_res.argv)}", markup=False)
        c.print(f"# solver exit_code: {z3_res.exit_code}", markup=False)
        c.print(f"# solver elapsed_sec: {elapsed_s:.2f}", markup=False)
    else:
        c.print(f"[cyan]solver[/cyan]: {' '.join(z3_res.argv)}")
        c.print(f"[cyan]solver exit_code[/cyan]: {z3_res.exit_code}")
        c.print(f"[cyan]solver elapsed[/cyan]: {elapsed_s:.2f}s")
    if replay_script_path is not None:
        replay_argv = list(z3_res.argv[:-1]) + [str(replay_script_path)]
        c.print(f"# debug replay smt: {replay_script_path}", markup=False)
        c.print(f"# debug replay cmd: {shlex.join(replay_argv)}", markup=False)
        c.print("# debug z3 stdin begin", markup=False)
        c.print(run_text, markup=False, end="")
        c.print("# debug z3 stdin end", markup=False)
    sat_out = parse_z3_sat_output(z3_res.stdout, unsat_core=unsat_core)
    status = "timeout" if z3_res.timed_out else sat_out.status
    c.print(status, markup=False)
    if unsat_core and status == "unsat" and sat_out.unsat_core_text.strip():
        c.print(sat_out.unsat_core_text.rstrip(), markup=False)
    if debug:
        c.print("# debug z3 stdout begin", markup=False)
        c.print(z3_res.stdout, markup=False, end="" if z3_res.stdout.endswith("\n") else "\n")
        c.print("# debug z3 stdout end", markup=False)
    if z3_res.stderr.strip():
        c.print(f"# solver stderr: {z3_res.stderr.strip()}", markup=False)
    if debug:
        c.print("# debug z3 stderr begin", markup=False)
        c.print(z3_res.stderr, markup=False, end="" if z3_res.stderr.endswith("\n") else "\n")
        c.print("# debug z3 stderr end", markup=False)
    if z3_res.exit_code != 0 and status != "timeout":
        raise typer.Exit(1)

    if status != "sat":
        if status == "timeout":
            raise typer.Exit(2)
        return

    if model_output_path is None:
        c.print("# sat model available; pass --model <path> to write TAC model", markup=False)
        return

    try:
        tac_model_text, model_warnings = z3_model_to_tac_model_text(
            sat_out.model_text,
            symbol_sort=_model_symbol_sorts(tac.symbol_table_text),
        )
    except ValueError as e:
        c.print(f"model conversion error: {e}" if plain else f"[red]model conversion error:[/red] {e}")
        raise typer.Exit(1) from e

    model_output_path.write_text(tac_model_text, encoding="utf-8")
    if plain:
        c.print(f"# wrote model: {model_output_path}", markup=False)
        for w in model_warnings:
            c.print(f"# model warning: {w}", markup=False)
    else:
        c.print(f"[cyan]wrote model[/cyan]: [bold]{model_output_path}[/bold]")
