from __future__ import annotations

from pathlib import Path
from typing import Annotated, Optional

import typer
from rich.table import Table
from rich.text import Text

from ctac.ast.highlight import highlight_tac_line
from ctac.ast.nodes import ApplyExpr, AssignExpCmd, AssignHavocCmd, TacExpr
from ctac.ast.run_format import (
    MODEL_HAVOC_FALLBACK_NUM,
    bytecode_addr_for_cmd,
    coerce_value_kind,
    format_value_plain_local,
    format_value_rich,
    model_fallback_value,
    source_prefix_for_cmd,
    strip_meta_suffix,
    values_equal,
)
from ctac.eval import (
    Evaluator,
    MemoryModel,
    RunConfig,
    UnknownValueError,
    Value,
    canonical_symbol,
    parse_model_path,
    run_program,
    value_to_text,
)
from ctac.parse import ParseError, parse_path
from ctac.tool.cli_runtime import (
    PLAIN_HELP,
    VERIFY_PANEL,
    agent_option,
    app,
    complete_choices,
    console,
    plain_requested,
)
from ctac.tool.commands_cfg_pp_search import normalize_printer_name, parse_user_value
from ctac.tool.input_resolution import resolve_model_input_path, resolve_tac_input_path, resolve_user_path
from ctac.tool.project_io import resolve_project_or_tac
from ctac.ast.pretty import configured_printer
from ctac.project import Project
from ctac.rewrite.trail import Trail


def _discover_project_trail(project: Project) -> tuple[Trail | None, str | None]:
    """Compose every trail-kind object whose ancestor chain reaches
    HEAD. Returns ``(None, None)`` when no such trail exists.

    A trail emitted after ``rw`` has parent = the rw'd object. So:
    - HEAD = the rw'd object → the trail's direct parent matches HEAD;
      apply it.
    - HEAD = the original .tac → walk parents of each trail; if HEAD
      is among them (the rw'd object's ancestor chain), the trail
      applies to the upstream replay.

    Multiple rw steps each emit a trail; concatenation + Trail's
    transitive lookup compose them.
    """
    manifest = project.manifest
    head_sha = manifest.head
    if head_sha is None:
        return None, None

    def _ancestors(start: str) -> set[str]:
        seen: set[str] = set()
        stack = [start]
        while stack:
            cur = stack.pop()
            if cur in seen:
                continue
            seen.add(cur)
            info = manifest.objects.get(cur)
            if info is None:
                continue
            stack.extend(info.parents)
        return seen

    matching_paths: list[str] = []
    composed: Trail = Trail()
    for sha, info in manifest.objects.items():
        if info.kind != "trail":
            continue
        # The trail "applies" if HEAD is anywhere on its parents'
        # ancestor closure (or is itself one of the parents).
        applies = False
        for p in info.parents:
            if p == head_sha or head_sha in _ancestors(p):
                applies = True
                break
        if not applies:
            continue
        try:
            text = project.object_path(sha).read_text()
        except OSError:
            continue
        try:
            part = Trail.from_json(text)
        except ValueError:
            continue
        composed = composed.merge(part)
        if info.names:
            matching_paths.append(info.names[-1])
    if not composed.substitutions:
        return None, None
    return composed, ", ".join(matching_paths) if matching_paths else None


_RUN_EPILOG = (
    "[bold green]Semantics[/bold green]  [cyan]assume[/cyan] failures stop the "
    "run silently (the path is infeasible); [cyan]assert[/cyan] failures "
    "continue and accumulate as [cyan]assert_fail[/cyan] counts. Havoc "
    "behavior is controlled by "
    "[cyan]--havoc-mode zero|random|ask[/cyan] (default [cyan]zero[/cyan]), "
    "or replayed from a model via [cyan]--model[/cyan]. Bytemap symbols load "
    "from memory entries in the model when present; [cyan]Store[/cyan] "
    "produces a fresh map, [cyan]Ite[/cyan] picks the taken branch lazily. "
    "When concrete eval can't proceed (e.g. a [cyan]Select[/cyan] on a "
    "bytemap with no model entries), the LHS scalar of the surrounding "
    "[cyan]AssignExpCmd[/cyan] falls back to the model's value for that "
    "name; [cyan]assert[/cyan]s on unknown predicates are reported as "
    "[cyan]inconclusive[/cyan].\n\n"
    "[bold green]Exit codes[/bold green]  [cyan]0[/cyan] ok, [cyan]2[/cyan] "
    "stopped (assume failed), [cyan]3[/cyan] error/max_steps.\n\n"
    "[bold green]Examples[/bold green]\n\n"
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
    "  [dim]# random havocs from block B1[/dim]"
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
            autocompletion=complete_choices(["zero", "random", "ask"]),
        ),
    ] = "zero",
    printer: Annotated[
        str,
        typer.Option(
            "--printer",
            help="Pretty-printer for trace lines. Built-ins: human (default), raw.",
            autocompletion=complete_choices(["human", "raw"]),
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
    with_address: bool = typer.Option(
        False,
        "--with-address",
        help=(
            "In --trace output, prefix each command with its SBF bytecode "
            "address in hex (from the sbf.bytecode.address metadata key). "
            "Commands without an address get blank padding."
        ),
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
    trail: Annotated[
        Optional[Path],
        typer.Option(
            "--trail",
            help=(
                "Path to a rewrite-trail JSON sidecar (emitted by "
                "``ctac rw --trail``). When ``--model`` lacks a value "
                "for a havoc'd variable that was eliminated by the "
                "rewrite, the trail maps it to an expression over "
                "surviving model variables — avoiding the "
                "unconstrained-sentinel fallback. In project mode the "
                "trail is auto-discovered from HEAD's lineage."
            ),
        ),
    ] = None,
    validate: bool = typer.Option(
        False,
        "--validate/--no-validate",
        help="Compare computed assignments against model values and report mismatches.",
    ),
) -> None:
    """Concrete interpreter (trace, model replay)."""
    _ = agent
    plain = plain_requested(plain)
    c = console(plain)
    try:
        user_path, user_warnings = resolve_user_path(path)
        if user_path.is_dir() and Project.is_project(user_path):
            resolved = resolve_project_or_tac(user_path)
            tac_path = resolved.tac_path
            input_warnings = resolved.warnings
            run_project: Optional[Project] = resolved.project
        else:
            tac_path, input_warnings = resolve_tac_input_path(user_path)
            run_project = None
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

    # Trail loading: explicit --trail wins; otherwise in project mode
    # auto-discover trail objects whose parent is on HEAD's lineage.
    run_trail: Trail | None = None
    trail_source: str | None = None
    if trail is not None:
        try:
            run_trail = Trail.from_json(trail.read_text())
            trail_source = str(trail)
        except (OSError, ValueError) as e:
            c.print(f"[red]trail error:[/red] {e}" if not plain else f"trail error: {e}")
            raise typer.Exit(1) from e
    elif run_project is not None:
        run_trail, trail_source = _discover_project_trail(run_project)

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
    model_havoc_trail_hits = 0
    model_havoc_fallback_hits = 0
    model_havoc_sentinel_fallback = 0
    # Source of each `_ask_or_model` call in invocation order.
    # `_havoc_value` is called at most once per AssignHavocCmd in event
    # order, so this list lines up 1:1 with non-bytemap havoc events
    # whose `value` is set.
    havoc_sources_in_order: list[str] = []

    def _normalize(s: str) -> str:
        return canonical_symbol(s, strip_var_suffixes=strip_var_suffixes)

    # Stateless evaluator with read-only access to model_values; used
    # to evaluate trail replacement expressions when the model misses.
    trail_evaluator: Evaluator | None = None
    if run_trail is not None:
        trail_evaluator = Evaluator(
            store={},
            normalize_symbol=_normalize,
            symbol_sorts=dict(tac.symbol_sorts),
            model_values=dict(model_values),
        )

    def _eval_trail(expr: TacExpr) -> Value:
        # Wrapper over Evaluator.eval_expr that skips evaluating the
        # callee SymbolRef inside ``Apply(<builtin>:bif, x)``. The base
        # evaluator's eval_expr forces every arg, which fails on builtin
        # names like ``safe_math_narrow_bv256:bif`` (not a model value).
        assert trail_evaluator is not None
        if isinstance(expr, ApplyExpr) and expr.op == "Apply":
            return trail_evaluator._eval_apply(
                expr.op,
                [
                    # Args[0] is the callee SymbolRef — pass any value;
                    # _eval_apply consults the original AST at whole.args[0].
                    Value(kind="bv", data=0),
                    *[_eval_trail(a) for a in expr.args[1:]],
                ],
                expr,
            )
        if isinstance(expr, ApplyExpr):
            if expr.op == "Select":
                return trail_evaluator._eval_select(expr)
            if expr.op == "Ite" and len(expr.args) == 3:
                cond = _eval_trail(expr.args[0])
                return _eval_trail(
                    expr.args[1] if cond.data else expr.args[2]
                )
            return trail_evaluator._eval_apply(
                expr.op, [_eval_trail(a) for a in expr.args], expr
            )
        return trail_evaluator.eval_expr(expr)

    def _lookup_trail(symbol: str, kind: str) -> Value | None:
        if run_trail is None or trail_evaluator is None:
            return None
        replacement = run_trail.lookup(symbol)
        if replacement is None:
            return None
        try:
            v = _eval_trail(replacement)
        except (UnknownValueError, ValueError, KeyError, TypeError):
            return None
        return coerce_value_kind(v, kind)

    def _ask_or_model(symbol: str, kind: str) -> Value:
        nonlocal model_havoc_hits, model_havoc_trail_hits
        nonlocal model_havoc_fallback_hits, model_havoc_sentinel_fallback
        mv = _model_lookup(model_values, symbol)
        if mv is not None:
            model_havoc_hits += 1
            havoc_sources_in_order.append("model")
            return coerce_value_kind(mv, kind)
        tv = _lookup_trail(symbol, kind)
        if tv is not None:
            model_havoc_trail_hits += 1
            havoc_sources_in_order.append("trail")
            return tv
        fb = _model_lookup(fallback_model_values, symbol)
        if fb is not None:
            model_havoc_fallback_hits += 1
            havoc_sources_in_order.append("fallback")
            return coerce_value_kind(fb, kind)
        model_havoc_sentinel_fallback += 1
        havoc_sources_in_order.append("default")
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
        symbol_sorts=dict(tac.symbol_sorts),
        model_values=dict(model_values),
    )
    res = run_program(tac.program, config=rcfg, pretty_cmd=pp_backend.print_cmd)

    # Tag each model-driven havoc event with where its value came from
    # (model / fallback / sentinel default). Only AssignHavocCmd events
    # that produced a value go through `_ask_or_model`, in event order;
    # bytemap havocs short-circuit before `_havoc_value` so they aren't
    # in the source list.
    if model is not None and havoc_sources_in_order:
        src_iter = iter(havoc_sources_in_order)
        for ev_obj in res.events:
            if isinstance(ev_obj.cmd, AssignHavocCmd) and ev_obj.value is not None:
                try:
                    ev_obj.value_source = next(src_iter)
                except StopIteration:
                    break

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
        if run_trail is not None:
            src = trail_source if trail_source else "trail"
            c.print(
                f"# trail: {src} ({len(run_trail.substitutions)} substitution(s))"
            )
        c.print(
            f"# model havoc: hits={model_havoc_hits}"
            + (
                f", trail_hits={model_havoc_trail_hits}"
                if run_trail is not None
                else ""
            )
            + f", fallback_hits={model_havoc_fallback_hits}"
            + f", sentinel_fallback={model_havoc_sentinel_fallback}"
            + f" (value={MODEL_HAVOC_FALLBACK_NUM})"
        )
    if validate:
        c.print(f"# validate: mismatches={mismatch_count}, missing_expected={missing_expected}")
    c.print(f"# status: {res.status} ({res.reason})")

    # Bytecode address column: same grepable hex format as `ctac pp`
    # (`0x{addr:x}`, lowercase, no separators), 10-char width with
    # blank padding for cmds whose metadata is missing.
    def _addr_col(cmd: object) -> str:
        if not with_address:
            return ""
        addr = bytecode_addr_for_cmd(cmd, tac.metas)
        prefix = f"0x{addr:x}" if addr is not None else ""
        return f"{prefix:<10}  "

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
                    # Per-block, content-sized columns: the block's
                    # widest left cell dictates that block's gutter
                    # position. A single wide block (e.g. a long Ite
                    # cmd) pushes its own values right but does not
                    # shift columns in narrower blocks. `expand=True`
                    # would force every block to the terminal width and
                    # globally homogenize the gutter, defeating that.
                    # `padding=(0, 2)` gives 2 spaces between cells —
                    # without it, content-sized cells touch directly.
                    block_table = Table.grid(expand=False, padding=(0, 2))
                    block_table.add_column()
                    block_table.add_column(justify="left", no_wrap=True)
                else:
                    block_table = None

            if not ev.rendered and not ev.note:
                continue

            addr_col = _addr_col(ev.cmd)

            if plain:
                # `markup=False` for the trace lines: rendered TAC text
                # legitimately contains square brackets (`[2^64]`,
                # `[debug.pta_split_or_merge]`, range bounds, bit slices)
                # that Rich would otherwise try to parse as markup and
                # eat. Plain mode must round-trip the printer's output
                # byte-for-byte.
                if src_prefix:
                    c.print(f"  {src_prefix}", markup=False)
                if ev.value is not None:
                    suffix = ""
                    if ev.value_source == "default":
                        suffix = "    (default)"
                    if ev.memory_repr:
                        suffix += f"    {ev.memory_repr}"
                    if ev.mismatch and ev.expected is not None:
                        suffix += f"    !! expected {format_value_plain_local(ev.expected)}"
                    c.print(f"  {addr_col}{ev.rendered}    {format_value_plain_local(ev.value)}{suffix}", markup=False)
                elif ev.memory_repr:
                    # Bytemap update: the concretized store annotation is
                    # strictly more informative than the bare "bytemap
                    # update" note, so it replaces it.
                    c.print(f"  {addr_col}{ev.rendered}    {ev.memory_repr}", markup=False)
                elif ev.note:
                    c.print(f"  {addr_col}{ev.rendered}    {ev.note}", markup=False)
                else:
                    c.print(f"  {addr_col}{ev.rendered}", markup=False)
                continue

            assert block_table is not None
            if src_prefix:
                block_table.add_row(Text(src_prefix, style="grey50"), Text(""))

            left_style = ev.color if ev.color else None
            left = highlight_tac_line(ev.rendered or "", base_style=left_style)
            if addr_col:
                left = Text(addr_col, style="grey50") + left

            if ev.value is not None:
                right = format_value_rich(ev.value)
                if ev.value_source == "default":
                    right.append("  ")
                    right.append("(default)", style="bold yellow")
                if ev.memory_repr:
                    right.append("  ")
                    right.append(ev.memory_repr, style="grey50")
                if ev.mismatch and ev.expected is not None:
                    right.append("  ")
                    right.append("!= expected ", style="bold red")
                    right.append(format_value_plain_local(ev.expected), style="bold red")
            elif ev.memory_repr:
                right = Text(ev.memory_repr, style="grey50", justify="left")
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
    # Warnings encountered along the executed path. Surface them with
    # the count even at zero so the field is always present, then list
    # the messages so they stay visible when --trace is off.
    # Dedupe to keep the summary readable when the same warning fires
    # repeatedly (e.g. a stack-read PTA over-approximation hit on
    # every loop iteration); the count is occurrences, not unique-count.
    c.print(f"warnings: {len(res.warnings)}")
    if res.warnings:
        seen: dict[str, int] = {}
        for w in res.warnings:
            seen[w] = seen.get(w, 0) + 1
        for text, n in seen.items():
            suffix = f"  (x{n})" if n > 1 else ""
            c.print(f"  {text}{suffix}", style="bold bright_red", markup=False)

    if res.status == "stopped":
        raise typer.Exit(2)
    if res.status in ("error", "max_steps"):
        raise typer.Exit(3)
