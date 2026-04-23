from __future__ import annotations

from pathlib import Path
from typing import Annotated, Optional

import typer
from rich.table import Table
from rich.text import Text

from ctac.ast.highlight import highlight_tac_line
from ctac.ast.nodes import AssignExpCmd, AssignHavocCmd
from ctac.ast.run_format import (
    MODEL_HAVOC_FALLBACK_NUM,
    coerce_value_kind,
    format_value_plain_local,
    format_value_rich,
    model_fallback_value,
    source_prefix_for_cmd,
    strip_meta_suffix,
    values_equal,
)
from ctac.analysis import BytemapCapability, classify_bytemap_usage
from ctac.eval import MemoryModel, RunConfig, Value, parse_model_path, run_program, value_to_text
from ctac.parse import ParseError, parse_path
from ctac.tool.cli_runtime import (
    PLAIN_HELP,
    VERIFY_PANEL,
    agent_option,
    app,
    console,
    plain_requested,
)
from ctac.tool.commands_cfg_pp_search import normalize_printer_name, parse_user_value
from ctac.tool.input_resolution import resolve_model_input_path, resolve_tac_input_path, resolve_user_path
from ctac.ast.pretty import configured_printer


_RUN_EPILOG = (
    "[bold]Examples:[/bold]\n\n"
    "[cyan]ctac run f.tac --plain[/cyan]"
    "  [dim]# zero-havoc run[/dim]\n\n"
    "[cyan]ctac run dir/ --plain[/cyan]"
    "  [dim]# auto-resolve .tac + model[/dim]\n\n"
    "[cyan]ctac run f.tac --plain --trace[/cyan]"
    "  [dim]# per-instruction trace[/dim]\n\n"
    "[cyan]ctac run f.tac --plain --model m.txt --trace[/cyan]"
    "  [dim]# replay a z3 model[/dim]\n\n"
    "[cyan]ctac run f.tac --plain --model m.txt --validate[/cyan]"
    "  [dim]# compare vs model[/dim]\n\n"
    "[cyan]ctac run f.tac --plain --havoc-mode random --entry B1[/cyan]"
    "  [dim]# random havocs from block B1[/dim]\n\n"
    "[bold]Exit codes:[/bold] 0 ok, 2 stopped (assume failed), 3 error/max_steps."
)


@app.command(rich_help_panel=VERIFY_PANEL, epilog=_RUN_EPILOG)
def run(
    path: Optional[Path] = typer.Argument(
        None, help="Path to .tac / .sbf.json file, or a Certora output directory."
    ),
    plain: bool = typer.Option(False, "--plain", help=PLAIN_HELP),
    agent: bool = agent_option(),
    trace: bool = typer.Option(
        False,
        "--trace/--no-trace",
        help="Show execution trace with per-instruction values and taken branches.",
    ),
    entry: Annotated[
        Optional[str],
        typer.Option("--entry", metavar="NBID", help="Start execution at this block id (default: first block)."),
    ] = None,
    max_steps: Annotated[
        int,
        typer.Option("--max-steps", min=1, help="Safety cap on executed instructions."),
    ] = 50_000,
    havoc_mode: Annotated[
        str,
        typer.Option(
            "--havoc-mode",
            help="How AssignHavocCmd gets a value: zero (default), random, ask.",
        ),
    ] = "zero",
    printer: Annotated[
        str,
        typer.Option(
            "--printer",
            help="Pretty-printer for trace lines. Built-ins: human (default), raw.",
        ),
    ] = "human",
    strip_var_suffixes: bool = typer.Option(
        True,
        "--strip-var-suffix/--keep-var-suffix",
        help="Strip TAC var suffixes like ':1' in traced symbols (default: strip).",
    ),
    weak_is_strong: bool = typer.Option(
        False,
        "--weak-is-strong",
        help="Parse snippet weak refs as strong refs (annotations use strong dereference).",
    ),
    human: bool = typer.Option(
        True,
        "--human/--no-human",
        help="Enable human-oriented pattern rewrites in trace pretty-printer (default: on).",
    ),
    model: Annotated[
        Optional[Path],
        typer.Option(
            "--model",
            help="Path to TAC-model text or SMT-LIB model output (optional sat/unknown prefix supported).",
        ),
    ] = None,
    fallback: Annotated[
        Optional[Path],
        typer.Option(
            "--fallback",
            help="Fallback model path: used for havoc values only when --model has no value.",
        ),
    ] = None,
    validate: bool = typer.Option(
        False,
        "--validate/--no-validate",
        help="Compare computed assignments against model values and report mismatches.",
    ),
) -> None:
    """Execute TAC with a concrete interpreter.

    Semantics: ``assume`` failures stop the run silently (no counterexample
    — the path is infeasible); ``assert`` failures continue and accumulate
    as ``assert_fail`` counts. Havoc behavior is controlled by
    ``--havoc-mode zero|random|ask`` (default ``zero``), or replayed from
    a model via ``--model``. Bytemap symbols load from memory entries in
    the model and feed ``Select`` lookups.
    """
    _ = agent
    plain = plain_requested(plain)
    c = console(plain)
    try:
        user_path, user_warnings = resolve_user_path(path)
        tac_path, input_warnings = resolve_tac_input_path(user_path)
        tac = parse_path(tac_path, weak_is_strong=weak_is_strong)
    except ParseError as e:
        if plain:
            c.print(f"parse error: {e}")
        else:
            c.print(f"[red]parse error:[/red] {e}")
        raise typer.Exit(1) from e
    except ValueError as e:
        if plain:
            c.print(f"input error: {e}")
        else:
            c.print(f"[red]input error:[/red] {e}")
        raise typer.Exit(1) from e

    capability = classify_bytemap_usage(tac.program, tac.symbol_sorts)
    if capability is BytemapCapability.BYTEMAP_RW:
        msg = (
            f"executing bytemap writes (Store) is not yet supported; "
            f"input classified as {capability.value}. "
            f"bytemap-free and bytemap-ro are supported."
        )
        c.print(f"input error: {msg}" if plain else f"[red]input error:[/red] {msg}")
        raise typer.Exit(1)

    hm = havoc_mode.strip().lower()
    if hm not in ("zero", "random", "ask"):
        raise typer.BadParameter("use one of: zero, random, ask", param_hint="--havoc-mode")

    input_warnings_run = list(user_warnings) + list(input_warnings)
    if model is None and user_path.is_dir():
        try:
            auto_model, auto_model_w = resolve_model_input_path(
                user_path,
                tac_path=tac_path,
                kind="auto model",
            )
        except ValueError as e:
            raise typer.BadParameter(str(e), param_hint="path") from e
        input_warnings_run.extend(auto_model_w)
        model = auto_model

    if fallback is not None and model is None:
        raise typer.BadParameter("--fallback requires --model", param_hint="--fallback")

    if model is not None:
        try:
            resolved_model, model_input_w = resolve_model_input_path(
                model,
                tac_path=tac_path,
                kind="model",
            )
        except ValueError as e:
            raise typer.BadParameter(str(e), param_hint="--model") from e
        input_warnings_run.extend(model_input_w)
        model = resolved_model
    if fallback is not None:
        try:
            resolved_fallback, fallback_input_w = resolve_model_input_path(
                fallback,
                tac_path=tac_path,
                kind="fallback model",
            )
        except ValueError as e:
            raise typer.BadParameter(str(e), param_hint="--fallback") from e
        input_warnings_run.extend(fallback_input_w)
        fallback = resolved_fallback

    if model is None and fallback is not None:
        input_warnings_run.append("fallback model ignored because primary model was not resolved")
        fallback = None

    if validate and model is None:
        raise typer.BadParameter("--validate requires --model", param_hint="--validate")

    printer_name = normalize_printer_name(printer)
    pp_backend = configured_printer(
        printer_name,
        strip_var_suffixes=strip_var_suffixes,
        human_patterns=human,
    )
    model_values: dict[str, Value] = {}
    model_warnings: list[str] = []
    model_memory: dict[str, MemoryModel] = {}
    fallback_model_values: dict[str, Value] = {}
    fallback_model_warnings: list[str] = []
    if model is not None:
        try:
            model_res = parse_model_path(model)
        except OSError as e:
            c.print(f"[red]model read error:[/red] {e}" if not plain else f"model read error: {e}")
            raise typer.Exit(1) from e
        except ValueError as e:
            c.print(f"[red]model parse error:[/red] {e}" if not plain else f"model parse error: {e}")
            raise typer.Exit(1) from e
        model_values = model_res.values
        model_warnings = model_res.warnings
        model_memory = model_res.memory
    if fallback is not None:
        try:
            fb_res = parse_model_path(fallback)
        except OSError as e:
            c.print(f"[red]fallback model read error:[/red] {e}" if not plain else f"fallback model read error: {e}")
            raise typer.Exit(1) from e
        except ValueError as e:
            c.print(f"[red]fallback model parse error:[/red] {e}" if not plain else f"fallback model parse error: {e}")
            raise typer.Exit(1) from e
        fallback_model_values = fb_res.values
        fallback_model_warnings = fb_res.warnings

    def _ask(symbol: str, kind: str) -> Value:
        while True:
            prompt = f"havoc {symbol} ({kind})"
            raw = typer.prompt(prompt)
            try:
                return parse_user_value(raw, kind)
            except ValueError as e:
                c.print(f"[red]{e}[/red]" if not plain else str(e))

    def _model_lookup(values: dict[str, Value], symbol: str) -> Value | None:
        if symbol in values:
            return values[symbol]
        stripped = strip_meta_suffix(symbol)
        if stripped in values:
            return values[stripped]
        return None

    model_havoc_hits = 0
    model_havoc_fallback_hits = 0
    model_havoc_sentinel_fallback = 0

    def _ask_or_model(symbol: str, kind: str) -> Value:
        nonlocal model_havoc_hits, model_havoc_fallback_hits, model_havoc_sentinel_fallback
        mv = _model_lookup(model_values, symbol)
        if mv is not None:
            model_havoc_hits += 1
            return coerce_value_kind(mv, kind)
        fb = _model_lookup(fallback_model_values, symbol)
        if fb is not None:
            model_havoc_fallback_hits += 1
            return coerce_value_kind(fb, kind)
        model_havoc_sentinel_fallback += 1
        return model_fallback_value(kind)

    ask_cb = _ask if hm == "ask" else None
    run_havoc_mode = hm
    if model is not None:
        ask_cb = _ask_or_model
        run_havoc_mode = "ask"

    rcfg = RunConfig(
        entry_block=entry,
        max_steps=max_steps,
        havoc_mode=run_havoc_mode,  # type: ignore[arg-type]
        ask_value=ask_cb,
        strip_var_suffixes=strip_var_suffixes,
        memory_store=dict(model_memory),
    )
    res = run_program(tac.program, config=rcfg, pretty_cmd=pp_backend.print_cmd)

    mismatch_count = 0
    missing_expected = 0
    mismatch_samples: list[str] = []
    if validate and model_values:
        for ev in res.events:
            if ev.value is None:
                continue
            if not isinstance(ev.cmd, (AssignExpCmd, AssignHavocCmd)):
                continue
            expected = _model_lookup(model_values, ev.cmd.lhs)
            if expected is None:
                missing_expected += 1
                continue
            expected_cast = coerce_value_kind(expected, ev.value.kind)
            ev.expected = expected_cast
            if not values_equal(ev.value, expected_cast):
                ev.mismatch = True
                mismatch_count += 1
                if len(mismatch_samples) < 15:
                    mismatch_samples.append(
                        f"{ev.block_id}: {ev.cmd.lhs} got {value_to_text(ev.value)} expected {value_to_text(expected_cast)}"
                    )
        if mismatch_count > 0 and not trace:
            c.print(
                f"[red]validation mismatch[/red]: {mismatch_count} assignment(s) differ from model"
                if not plain
                else f"validation mismatch: {mismatch_count} assignment(s) differ from model"
            )
            for line in mismatch_samples:
                c.print(f"  - {line}")
            if mismatch_count > len(mismatch_samples):
                c.print(f"  - ... {mismatch_count - len(mismatch_samples)} more")
    elif validate and not model_values:
        c.print(
            "[yellow]validate requested but model has no parsed scalar values[/yellow]"
            if not plain
            else "validate requested but model has no parsed scalar values"
        )

    if tac.path:
        c.print(f"# path: {tac.path}")
    for w in input_warnings_run:
        c.print(f"# input warning: {w}")
    c.print(f"# mode: run (havoc={run_havoc_mode}, max_steps={max_steps})")
    if model is not None:
        c.print(f"# model: {model}")
        c.print(f"# model values: {len(model_values)}")
        if model_memory:
            total_entries = sum(len(m.entries) for m in model_memory.values())
            c.print(f"# model memory: {len(model_memory)} bytemap(s), {total_entries} entry(ies)")
        for w in model_warnings:
            c.print(f"# model warning: {w}")
        if fallback is not None:
            c.print(f"# fallback model: {fallback}")
            c.print(f"# fallback model values: {len(fallback_model_values)}")
            for w in fallback_model_warnings:
                c.print(f"# fallback model warning: {w}")
        c.print(
            f"# model havoc: hits={model_havoc_hits}, fallback_hits={model_havoc_fallback_hits}, "
            f"sentinel_fallback={model_havoc_sentinel_fallback}"
            f" (value={MODEL_HAVOC_FALLBACK_NUM})"
        )
    if validate:
        c.print(f"# validate: mismatches={mismatch_count}, missing_expected={missing_expected}")
    c.print(f"# status: {res.status} ({res.reason})")

    if trace:
        cur_block: str | None = None
        block_table: Table | None = None
        for ev in res.events:
            src_prefix = source_prefix_for_cmd(ev.cmd, tac.metas)
            if ev.block_id != cur_block:
                if block_table is not None:
                    c.print(block_table)
                    c.print("")
                cur_block = ev.block_id
                c.print(f"[bold]{cur_block}:[/bold]" if not plain else f"{cur_block}:")
                if not plain:
                    block_table = Table.grid(expand=True)
                    block_table.add_column(ratio=3, overflow="ellipsis")
                    block_table.add_column(
                        ratio=1,
                        justify="left",
                        no_wrap=True,
                        overflow="ellipsis",
                    )
                else:
                    block_table = None

            if not ev.rendered and not ev.note:
                continue

            if plain:
                if src_prefix:
                    c.print(f"  {src_prefix}")
                if ev.value is not None:
                    suffix = ""
                    if ev.mismatch and ev.expected is not None:
                        suffix = f"    !! expected {format_value_plain_local(ev.expected)}"
                    c.print(f"  {ev.rendered}    {format_value_plain_local(ev.value)}{suffix}")
                elif ev.note:
                    c.print(f"  {ev.rendered}    {ev.note}")
                else:
                    c.print(f"  {ev.rendered}")
                continue

            assert block_table is not None
            if src_prefix:
                block_table.add_row(Text(src_prefix, style="grey50"), Text(""))

            left_style = ev.color if ev.color else None
            left = highlight_tac_line(ev.rendered or "", base_style=left_style)

            if ev.value is not None:
                right = format_value_rich(ev.value)
                if ev.mismatch and ev.expected is not None:
                    right.append("  ")
                    right.append("!= expected ", style="bold red")
                    right.append(format_value_plain_local(ev.expected), style="bold red")
            elif ev.note:
                note_style = f"bold {ev.color}" if ev.color else "bold cyan"
                right = Text(ev.note, style=note_style, justify="left")
            else:
                right = Text("")

            block_table.add_row(left, right)

        if block_table is not None and not plain:
            c.print(block_table)
        c.print("")

    c.print(f"steps: {res.steps}")
    c.print(f"executed_blocks: {len(res.executed_blocks)}")
    c.print(f"assert_ok: {res.assert_ok}")
    c.print(f"assert_fail: {res.assert_fail}")

    if res.status == "stopped":
        raise typer.Exit(2)
    if res.status in ("error", "max_steps"):
        raise typer.Exit(3)
