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
from ctac.tool.cli_runtime import (
    PLAIN_HELP,
    VERIFY_PANEL,
    agent_option,
    app,
    complete_choices,
    complete_smt_encodings,
    console,
    plain_requested,
)
from ctac.tool.project_io import ingest_or_write_text, resolve_project_or_tac

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


_SMT_EPILOG = (
    "[bold green]What it does[/bold green]  Emit an SMT-LIB VC from "
    "loop-free, single-assert TAC. Encoding [cyan]sea_vc[/cyan] (QF_UFNIA): "
    "DSA + block-reachability, sound bv256 domain constraints, bytemap-as-UF "
    "+ range-axiom support. It is currently the only supported encoder — "
    "the historical QF_BV path-predicate encoder was removed and would need "
    "to be rebuilt from scratch if BV semantics become necessary.\n\n"
    "[bold green]Query semantics[/bold green]  [cyan]SAT[/cyan] iff the "
    "assertion-failure state is reachable. [cyan]UNSAT[/cyan] means the "
    "assertion holds.\n\n"
    "[bold green]Preconditions[/bold green]  Loop-free TAC; exactly one "
    "[cyan]AssertCmd[/cyan] (run [cyan]ctac ua[/cyan] to merge multi-assert "
    "inputs); [cyan]AssertCmd[/cyan] must be the last command in its block; "
    "no critical edges in the CFG (sea_vc's predecessor exclusivity is "
    "unsound on critical edges); "
    "bytemap usage must be [cyan]bytemap-free[/cyan] or [cyan]bytemap-ro[/cyan] "
    "(check with [cyan]ctac stats --plain[/cyan]).\n\n"
    "[bold green]Examples[/bold green]\n\n"
    "[cyan]ctac smt f.tac --plain[/cyan]"
    "  [dim]# print VC to stdout[/dim]\n\n"
    "[cyan]ctac smt f.tac --plain -o out.smt2[/cyan]"
    "  [dim]# write file[/dim]\n\n"
    "[cyan]ctac smt f.tac --plain --run[/cyan]"
    "  [dim]# invoke z3[/dim]\n\n"
    "[cyan]ctac smt f.tac --plain --run --model m.txt[/cyan]"
    "  [dim]# write TAC model[/dim]\n\n"
    "[cyan]ctac smt f.tac --plain --run --unsat-core[/cyan]"
    "  [dim]# name asserts, print core[/dim]\n\n"
    "[cyan]ctac smt f.tac --plain --run --timeout 60 --z3-args \"smt.random_seed=7\"[/cyan]\n\n"
    "[cyan]ctac smt f.tac --plain --run --debug[/cyan]"
    "  [dim]# print z3 stdin/stdout + replay cmd[/dim]"
)


@app.command("smt", rich_help_panel=VERIFY_PANEL, epilog=_SMT_EPILOG)
def smt_cmd(
    path: Optional[Path] = typer.Argument(
        None, help="Path to .tac / .sbf.json file, or a Certora output directory."
    ),
    plain: bool = typer.Option(False, "--plain", help=PLAIN_HELP),
    agent: bool = agent_option(),
    encoding: Annotated[
        str,
        typer.Option(
            "--encoding",
            help="SMT VC encoding strategy (default: sea_vc).",
            autocompletion=complete_smt_encodings(),
        ),
    ] = "sea_vc",
    output_path: Annotated[
        Optional[Path],
        typer.Option("-o", "--output", help="Write SMT-LIB output to this file."),
    ] = None,
    run: bool = typer.Option(
        False,
        "--run/--no-run",
        "--solve/--no-solve",
        help="Run Z3 on the generated SMT-LIB instance (--solve is an alias to disambiguate from `ctac run`).",
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
    tight_logic: bool = typer.Option(
        False,
        "--tight-logic",
        help=(
            "Pick the tightest SMT-LIB logic the VC fits into (e.g. QF_NIA when "
            "no uninterpreted functions are needed). Default is the broader "
            "QF_UFNIA so solver tactics stay uniform across outputs."
        ),
    ),
    guard_statics: bool = typer.Option(
        False,
        "--guard-statics",
        help=(
            "Guard the static-def equalities of each block by its "
            "block-reachability variable: per defining block, emit a "
            "single `(=> BLK_<bid> (and (= lhs1 rhs1) (= lhs2 rhs2) "
            "...))` over the conjunction of that block's static "
            "equalities. Default emits each `(= lhs rhs)` "
            "unconditionally; entry-block defs are unaffected (entry "
            "guard is `true`)."
        ),
    ),
    guard_dynamics: bool = typer.Option(
        False,
        "--guard-dynamics",
        help=(
            "Encode each dynamic (DSA-merged) assignment as a block-"
            "guarded equality `(=> BLK_<bid> (= lhs rhs))` per "
            "defining block (deduped by RHS). Default merges the "
            "per-block defs into a single `(= lhs (ite ...))` "
            "selected by block guards."
        ),
    ),
    cfg_encoding: Annotated[
        str,
        typer.Option(
            "--cfg-encoding",
            help=(
                "CFG-constraint encoding strategy. "
                "bwd0 (default): predecessor-oriented edge-feasibility "
                "OR-of-ANDs. bwd1: per-edge clausal implications "
                "(predecessor). fwd: successor-oriented one-way "
                "implication. fwd-bwd: fwd plus a backward `BLK_i => "
                "BLK_idom(i)` clause for each non-entry block (gives "
                "BCP a 1-hop backward propagation path). fwd-edge / "
                "bwd-edge: per-edge Bool variables with biconditional "
                "block-existence."
            ),
            autocompletion=complete_choices(
                ["bwd0", "bwd1", "fwd", "fwd-bwd", "fwd-edge", "bwd-edge"]
            ),
        ),
    ] = "bwd0",
    narrow_range: bool = typer.Option(
        False,
        "--narrow-range",
        help=(
            "For every static `R = Apply(safe_math_narrow_bvN:bif, ...)` "
            "assignment, emit an in-range axiom `(<= 0 R BV256_MAX)` "
            "based on the LHS's declared sort. The encoder otherwise "
            "treats narrow as identity on the inner expression, leaving "
            "the LHS unbounded. Currently only bv256 LHS values get the "
            "axiom; other bv widths are silent. Default off."
        ),
    ),
    store_reduce: bool = typer.Option(
        False,
        "--store-reduce/--no-store-reduce",
        help=(
            "Build a per-bytemap chain data structure during encoding. "
            "Prunes shadowed Store entries when a later Store at the "
            "same key supersedes an earlier one; preserves the "
            "(ite ... (M_old idx)) shared-sibling form when no shadow "
            "fires; and drops define-fun lines for bytemap symbols not "
            "reachable from any Select query (their content is inlined "
            "into the chain that reads them). Sound by the array "
            "Store/Select axiom. Default off — preserves byte-identical "
            "output for the existing eager emission."
        ),
    ),
    debug: bool = typer.Option(
        False,
        "--debug/--no-debug",
        help="Print solver interaction details for debugging.",
    ),
) -> None:
    """Emit an SMT-LIB VC; optionally invoke z3."""
    _ = agent
    plain = plain_requested(plain)
    c = console(plain)
    if unsat_core and model_output_path is not None:
        msg = "cannot combine --unsat-core with --model"
        c.print(f"input error: {msg}" if plain else f"[red]input error:[/red] {msg}")
        raise typer.Exit(1)
    known_encodings = ", ".join(available_encodings())
    try:
        resolved = resolve_project_or_tac(path)
        tac = parse_path(resolved.tac_path)
        # bytemap-rw used to be rejected here; sea_vc now encodes Store
        # via lambda-style ``define-fun`` per-map definitions
        # (function-level ITE for DSA-dynamic merges; ``Select`` is
        # unchanged as function application). See sea_vc.py for shape.
        script = build_vc(
            tac,
            encoding=encoding,
            unsat_core=unsat_core,
            tight_logic=tight_logic,
            guard_statics=guard_statics,
            guard_dynamics=guard_dynamics,
            cfg_encoding=cfg_encoding,
            narrow_range=narrow_range,
            store_reduce=store_reduce,
        )
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
        for w in resolved.warnings:
            c.print(f"# input warning: {w}", markup=False)
        for w in script.warnings:
            c.print(f"# encoder warning: {w}", markup=False)

    # smt produces an .smt2 sibling of HEAD — non-HEAD-advancing.
    # Project ingestion only fires when the user gave us a project dir
    # AND no -o; explicit -o keeps the legacy path. The result is always
    # also written to a real on-disk path (either user's or project
    # symlink), so the post-write `--run` flow still finds it.
    written_smt_path, _smt_info = ingest_or_write_text(
        explicit_output=output_path,
        project=resolved.project,
        text=smt_text,
        command="smt",
        kind="smt",
        advance_head=False,
    )
    if written_smt_path is not None:
        if plain:
            c.print(f"# wrote smt: {written_smt_path}", markup=False)
        else:
            c.print(f"[cyan]wrote smt[/cyan]: [bold]{written_smt_path}[/bold]")
        if not run:
            return

    if not run:
        c.print(smt_text, markup=False, end="")
        return

    # z3's `-model` flag handles model printing cleanly — no trailing
    # `(get-model)` needed in the script text.
    run_text = smt_text
    want_model = not unsat_core
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
                want_model=want_model,
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
                    want_model=want_model,
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
