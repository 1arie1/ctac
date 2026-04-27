"""`ctac absint` — abstract-interpreter-driven analyses.

For now the only exposed analysis is polynomial degree (a stats case
that ranks the program's non-linear expressions). Most absint work is
analysis in support of other transformations; this command surfaces
the analyses that produce useful standalone reports.
"""

from __future__ import annotations

import json
import time
from collections import Counter
from pathlib import Path
from typing import Annotated, Optional

import typer
from rich.markup import escape
from rich.tree import Tree

from ctac.analysis.abs_int import analyze_intervals, analyze_polynomial_degree
from ctac.analysis.abs_int.interval_ops import Interval, meet as iv_meet
from ctac.ast.pretty import configured_printer
from ctac.parse import ParseError, parse_path
from ctac.tool.cli_runtime import (
    ANALYZE_PANEL,
    FILTER_CMD_CONTAINS_HELP,
    FILTER_EXCLUDE_HELP,
    FILTER_FROM_HELP,
    FILTER_ID_CONTAINS_HELP,
    FILTER_ID_REGEX_HELP,
    FILTER_ONLY_HELP,
    FILTER_TO_HELP,
    PLAIN_HELP,
    agent_option,
    app,
    complete_choices,
    console,
    plain_requested,
)
from ctac.tool.filters import CfgFilterOptions, apply_cfg_filters
from ctac.tool.input_resolution import resolve_tac_input_path, resolve_user_path
from ctac.tool.stats_model import StatsCollection
from ctac.tool.stats_render import render_plain_stats, render_rich_stats_tree

_VALID_SHOW = ("degree", "interval", "all")
_DEFAULT_SHOW = "all"


def _parse_show_modes(raw: str) -> set[str]:
    valid = {"degree", "interval", "all"}
    items = {x.strip().lower() for x in raw.split(",") if x.strip()}
    if not items:
        raise typer.BadParameter("at least one mode required", param_hint="--show")
    unknown = sorted(items - valid)
    if unknown:
        raise typer.BadParameter(
            f"unknown --show mode(s): {', '.join(unknown)}", param_hint="--show"
        )
    if "all" in items:
        return valid - {"all"}
    return items


def _format_interval(iv: Interval) -> str:
    if iv.is_top():
        return "TOP"
    if iv.is_bot():
        return "BOT"
    lo = "-inf" if iv.lo is None else str(iv.lo)
    hi = "+inf" if iv.hi is None else str(iv.hi)
    return f"[{lo}, {hi}]"


def _format_duration(seconds: float) -> str:
    s = max(0.0, seconds)
    units = [
        (1.0, "s"),
        (1e-3, "ms"),
        (1e-6, "us"),
        (1e-9, "ns"),
    ]
    for scale, unit in units:
        if s >= scale or unit == "ns":
            val = s / scale
            return f"{val:.3g}{unit}"
    return "0ns"


_ABSINT_EPILOG = (
    "[bold green]Analyses[/bold green]  [cyan]--show[/cyan] is comma-separated, "
    "default [cyan]all[/cyan]:\n\n"
    "[cyan]degree[/cyan] (polynomial degree of every variable; ranks the program's "
    "non-linear expressions).\n\n"
    "[cyan]interval[/cyan] (per-variable integer interval inferred via DSA-aware "
    "abstract interpretation; surfaces tightest bounds + counts of TOP/BOT vars).\n\n"
    "Default prints summary stats. [cyan]--details[/cyan] adds top tables. "
    "[cyan]--json[/cyan] for machine-readable output.\n\n"
    "[bold green]Examples[/bold green]\n\n"
    "[cyan]ctac absint f.tac --plain[/cyan]"
    "  [dim]# all analyses, summary[/dim]\n\n"
    "[cyan]ctac absint f.tac --plain --details[/cyan]"
    "  [dim]# top tables for each enabled analysis[/dim]\n\n"
    "[cyan]ctac absint f.tac --plain --show interval --details[/cyan]"
    "  [dim]# tightest non-trivial intervals[/dim]\n\n"
    "[cyan]ctac absint f.tac --plain --json[/cyan]"
    "  [dim]# machine-readable[/dim]"
)


@app.command("absint", rich_help_panel=ANALYZE_PANEL, epilog=_ABSINT_EPILOG)
def absint_cmd(
    path: Optional[Path] = typer.Argument(
        None, help="Path to .tac / .sbf.json file, or a Certora output directory."
    ),
    plain: bool = typer.Option(False, "--plain", help=PLAIN_HELP),
    agent: bool = agent_option(),
    show: Annotated[
        str,
        typer.Option(
            "--show",
            help="Comma-separated analysis outputs: degree,all",
            autocompletion=complete_choices(list(_VALID_SHOW)),
        ),
    ] = _DEFAULT_SHOW,
    json_out: bool = typer.Option(
        False, "--json", help="Emit machine-readable JSON output."
    ),
    details: bool = typer.Option(
        False,
        "--details/--summary",
        help="Show top non-linear expression table in addition to summary stats.",
    ),
    max_items: int = typer.Option(
        20,
        "--max-items",
        min=1,
        help="Maximum rows in the top non-linear expression table when --details is enabled.",
    ),
    min_degree: int = typer.Option(
        2,
        "--min-degree",
        min=0,
        help="Filter the top non-linear table to expressions with degree at least this value.",
    ),
    raw_output: bool = typer.Option(
        False,
        "--raw",
        help="Use raw TAC command text in the detail rows (default: pretty-printed).",
    ),
    strip_var_suffixes: bool = typer.Option(
        True,
        "--strip-var-suffix/--keep-var-suffix",
        help="Strip TAC var suffixes like ':1' when rendering detail rows.",
    ),
    to_block: Annotated[
        Optional[str], typer.Option("--to", metavar="NBID", help=FILTER_TO_HELP)
    ] = None,
    from_block: Annotated[
        Optional[str], typer.Option("--from", metavar="NBID", help=FILTER_FROM_HELP)
    ] = None,
    only: Annotated[Optional[str], typer.Option("--only", help=FILTER_ONLY_HELP)] = None,
    id_contains: Annotated[
        Optional[str], typer.Option("--id-contains", help=FILTER_ID_CONTAINS_HELP)
    ] = None,
    id_regex: Annotated[
        Optional[str], typer.Option("--id-regex", help=FILTER_ID_REGEX_HELP)
    ] = None,
    cmd_contains: Annotated[
        Optional[str], typer.Option("--cmd-contains", help=FILTER_CMD_CONTAINS_HELP)
    ] = None,
    exclude: Annotated[
        Optional[str], typer.Option("--exclude", help=FILTER_EXCLUDE_HELP)
    ] = None,
) -> None:
    """Abstract-interpreter analyses (polynomial degree, ...)."""
    _ = agent
    plain = plain_requested(plain)
    c = console(plain)
    try:
        modes = _parse_show_modes(show)
        user_path, user_warnings = resolve_user_path(path)
        tac_path, input_warnings = resolve_tac_input_path(user_path)
        tac = parse_path(tac_path)
        filtered_program, filter_warnings = apply_cfg_filters(
            tac.program,
            CfgFilterOptions(
                to_block=to_block,
                from_block=from_block,
                only=only,
                id_contains=id_contains,
                id_regex=id_regex,
                cmd_contains=cmd_contains,
                exclude=exclude,
            ),
        )
    except ParseError as e:
        c.print(f"parse error: {e}" if plain else f"[red]parse error:[/red] {e}")
        raise typer.Exit(1) from e
    except ValueError as e:
        c.print(f"input error: {e}" if plain else f"[red]input error:[/red] {e}")
        raise typer.Exit(1) from e

    timings_sec: dict[str, float] = {}
    payload: dict[str, object] = {
        "path": tac.path,
        "show": sorted(modes),
        "blocks": len(filtered_program.blocks),
        "input_warnings": user_warnings + input_warnings,
        "filter_warnings": filter_warnings,
        "detail_rendering": "raw" if raw_output else "pretty",
    }

    pp = configured_printer(
        "raw" if raw_output else "human",
        strip_var_suffixes=strip_var_suffixes,
        human_patterns=True,
    )

    if "degree" in modes:
        t0 = time.perf_counter()
        result = analyze_polynomial_degree(filtered_program)
        timings_sec["degree"] = time.perf_counter() - t0
        # Build a (block_id, cmd_index) → rendered string map only for the
        # AssignExpCmds the analysis touched; cheap because the visit set
        # is bounded by |program|.
        rendered_by_point: dict[tuple[str, int], str] = {}
        cmd_by_point: dict[tuple[str, int], object] = {}
        for b in filtered_program.blocks:
            for idx, cmd in enumerate(b.commands):
                cmd_by_point[(b.id, idx)] = cmd
        for ed in result.expression_degrees:
            cmd = cmd_by_point.get((ed.block_id, ed.cmd_index))
            if cmd is not None:
                line = pp.print_cmd(cmd)
                rendered_by_point[(ed.block_id, ed.cmd_index)] = (
                    line if line else cmd.raw if hasattr(cmd, "raw") else ed.raw
                )

        # Distribution by integer degree (TOP / BOT counted separately).
        dist: Counter[int] = Counter()
        for v in result.final_state.values():
            if isinstance(v, int):
                dist[v] += 1
        # Top non-linear rows: filter by min_degree, sort descending, then
        # by block/cmd-index for stable display. TOP rows are reported
        # separately at the end of the detail block.
        nonlinear_rows = [
            ed
            for ed in result.expression_degrees
            if isinstance(ed.degree, int) and ed.degree >= min_degree
        ]
        nonlinear_rows.sort(
            key=lambda e: (-e.degree if isinstance(e.degree, int) else 0, e.block_id, e.cmd_index)
        )
        top_rows = nonlinear_rows[:max_items]

        top_rendered = [
            {
                "block_id": ed.block_id,
                "cmd_index": ed.cmd_index,
                "lhs": ed.lhs,
                "degree": ed.degree,
                "rendered": rendered_by_point.get((ed.block_id, ed.cmd_index), ed.raw),
            }
            for ed in top_rows
        ]

        # TOP-degree rows: list them at most max_items, regardless of
        # min_degree (they're degree-unknown, often the most interesting).
        top_unknown = [
            ed for ed in result.expression_degrees if not isinstance(ed.degree, int)
        ][:max_items]
        top_unknown_rendered = [
            {
                "block_id": ed.block_id,
                "cmd_index": ed.cmd_index,
                "lhs": ed.lhs,
                "degree": ed.degree,
                "rendered": rendered_by_point.get((ed.block_id, ed.cmd_index), ed.raw),
            }
            for ed in top_unknown
        ]

        payload["degree"] = {
            "symbols_total": len(result.final_state),
            "max_degree": result.program_max_degree,
            "saw_top": result.saw_top,
            "top_symbols_count": len(result.top_symbols),
            "distribution": {str(k): dist[k] for k in sorted(dist)},
            "nonlinear_count": len(nonlinear_rows),
            "min_degree_filter": min_degree,
            "top_nonlinear": top_rendered,
            "top_unknown": top_unknown_rendered,
        }

    if "interval" in modes:
        t0 = time.perf_counter()
        interval_result = analyze_intervals(
            filtered_program, symbol_sorts=tac.symbol_sorts
        )
        timings_sec["interval"] = time.perf_counter() - t0

        # Categorize static intervals: concrete (both bounds known),
        # partial (one side bound), TOP (both unknown), BOT (empty).
        concrete_count = 0
        partial_count = 0
        top_count = 0
        bot_count = 0
        for v in interval_result.static.values():
            if v.is_bot():
                bot_count += 1
            elif v.is_top():
                top_count += 1
            elif v.lo is None or v.hi is None:
                partial_count += 1
            else:
                concrete_count += 1

        # Per-var tightest interval seen anywhere (across `static` and
        # every block's `local`). Refinements never mutate static, so a
        # static var can have a tighter local view at one block; the
        # user's question "how tight is this value really known?" is
        # answered by the meet across all observed views. Sound for
        # display purposes (it's the strongest fact derivable about the
        # variable from the analysis output).
        tightest: dict[str, Interval] = {
            var: v for var, v in interval_result.static.items()
        }
        for block_local in interval_result.per_block_local.values():
            for var, v in block_local.items():
                prev = tightest.get(var)
                tightest[var] = v if prev is None else iv_meet(prev, v)
        rankable = [
            (var, v)
            for var, v in tightest.items()
            if v.lo is not None and v.hi is not None and not v.is_bot()
        ]
        rankable.sort(
            key=lambda kv: (
                kv[1].hi - kv[1].lo if kv[1].hi is not None and kv[1].lo is not None else 0,
                kv[0],
            )
        )
        top_intervals = [
            {
                "var": var,
                "interval": _format_interval(v),
                "lo": v.lo,
                "hi": v.hi,
            }
            for var, v in rankable[:max_items]
        ]

        payload["interval"] = {
            "static_symbols_total": len(interval_result.static),
            "concrete_count": concrete_count,
            "partial_count": partial_count,
            "top_count": top_count,
            "bot_count": bot_count,
            "blocks_with_local": len(interval_result.per_block_local),
            "local_entries_total": sum(
                len(d) for d in interval_result.per_block_local.values()
            ),
            "top_tightest": top_intervals,
        }

    payload["timings_sec"] = {k: timings_sec[k] for k in sorted(timings_sec)}

    if json_out:
        # Bypass Rich here: it soft-wraps long lines to terminal width,
        # which would corrupt JSON output (line continuations land
        # inside string values).
        typer.echo(json.dumps(payload, indent=2, sort_keys=True))
        return

    summary_stats = StatsCollection()
    summary_stats.add_str("input.path", str(tac.path or "-"))
    summary_stats.add_str("input.show", ", ".join(sorted(modes)))
    summary_stats.add_num("input.blocks", len(filtered_program.blocks))
    summary_stats.add_num("input.input_warnings", len(user_warnings) + len(input_warnings))
    summary_stats.add_num("input.filter_warnings", len(filter_warnings))
    for name in sorted(timings_sec):
        summary_stats.add_time(f"timings.{name}", timings_sec[name], unit="s")

    if "degree" in modes:
        deg_obj = payload["degree"]  # type: ignore[assignment]
        summary_stats.add_num("degree.symbols_total", deg_obj["symbols_total"])
        summary_stats.add_num("degree.max_degree", deg_obj["max_degree"])
        summary_stats.add_num("degree.saw_top", int(bool(deg_obj["saw_top"])))
        summary_stats.add_num("degree.top_symbols_count", deg_obj["top_symbols_count"])
        summary_stats.add_num("degree.nonlinear_count", deg_obj["nonlinear_count"])
        for k, v in deg_obj["distribution"].items():
            summary_stats.add_num(f"degree.distribution.deg_{k}", v)

    if "interval" in modes:
        iv_obj = payload["interval"]  # type: ignore[assignment]
        summary_stats.add_num("interval.static_symbols_total", iv_obj["static_symbols_total"])
        summary_stats.add_num("interval.concrete_count", iv_obj["concrete_count"])
        summary_stats.add_num("interval.partial_count", iv_obj["partial_count"])
        summary_stats.add_num("interval.top_count", iv_obj["top_count"])
        summary_stats.add_num("interval.bot_count", iv_obj["bot_count"])
        summary_stats.add_num("interval.blocks_with_local", iv_obj["blocks_with_local"])
        summary_stats.add_num("interval.local_entries_total", iv_obj["local_entries_total"])

    if not details:
        if plain:
            for line in render_plain_stats(summary_stats):
                c.print(line, markup=False)
        else:
            c.print(render_rich_stats_tree(summary_stats, root_label="absint_summary"))
        return

    if plain:
        if tac.path:
            c.print(f"# path: {tac.path}", no_wrap=True, markup=False)
        for w in user_warnings + input_warnings:
            c.print(f"# input warning: {w}", markup=False)
        for w in filter_warnings:
            c.print(f"# {w}", markup=False)
        c.print(f"# show: {', '.join(sorted(modes))}", markup=False)
        c.print(f"# blocks: {len(filtered_program.blocks)}", markup=False)

        if "degree" in modes:
            deg_obj = payload["degree"]  # type: ignore[assignment]
            c.print("degree:", markup=False)
            c.print(f"  time: {_format_duration(timings_sec.get('degree', 0.0))}", markup=False)
            c.print(
                (
                    f"  symbols_total: {deg_obj['symbols_total']}, "
                    f"max_degree: {deg_obj['max_degree']}, "
                    f"saw_top: {deg_obj['saw_top']}, "
                    f"top_symbols_count: {deg_obj['top_symbols_count']}, "
                    f"nonlinear_count: {deg_obj['nonlinear_count']}"
                ),
                markup=False,
            )
            for k in sorted(deg_obj["distribution"], key=lambda x: int(x)):
                c.print(f"  distribution[deg_{k}]: {deg_obj['distribution'][k]}", markup=False)
            top_rows = deg_obj["top_nonlinear"]  # type: ignore[index]
            if top_rows:
                c.print(
                    f"  top non-linear (degree >= {deg_obj['min_degree_filter']}, format: block:loc | deg | lhs | command):",
                    markup=False,
                )
                loc_w = max(9, max(len(f"{r['block_id']}:{r['cmd_index'] + 1}") for r in top_rows))
                lhs_w = max(3, max(len(str(r["lhs"])) for r in top_rows))
                for r in top_rows:
                    loc = f"{r['block_id']}:{r['cmd_index'] + 1}"
                    c.print(
                        f"  {loc:<{loc_w}} | {r['degree']:>3} | {str(r['lhs']):<{lhs_w}} | {r['rendered']}",
                        markup=False,
                    )
            top_unk = deg_obj["top_unknown"]  # type: ignore[index]
            if top_unk:
                c.print(
                    "  top unknown (degree=TOP, format: block:loc | lhs | command):",
                    markup=False,
                )
                loc_w = max(9, max(len(f"{r['block_id']}:{r['cmd_index'] + 1}") for r in top_unk))
                lhs_w = max(3, max(len(str(r["lhs"])) for r in top_unk))
                for r in top_unk:
                    loc = f"{r['block_id']}:{r['cmd_index'] + 1}"
                    c.print(
                        f"  {loc:<{loc_w}} | {str(r['lhs']):<{lhs_w}} | {r['rendered']}",
                        markup=False,
                    )

        if "interval" in modes:
            iv_obj = payload["interval"]  # type: ignore[assignment]
            c.print("interval:", markup=False)
            c.print(
                f"  time: {_format_duration(timings_sec.get('interval', 0.0))}",
                markup=False,
            )
            c.print(
                (
                    f"  static_symbols_total: {iv_obj['static_symbols_total']}, "
                    f"concrete: {iv_obj['concrete_count']}, "
                    f"partial: {iv_obj['partial_count']}, "
                    f"top: {iv_obj['top_count']}, "
                    f"bot: {iv_obj['bot_count']}, "
                    f"blocks_with_local: {iv_obj['blocks_with_local']}, "
                    f"local_entries: {iv_obj['local_entries_total']}"
                ),
                markup=False,
            )
            top_iv = iv_obj["top_tightest"]  # type: ignore[index]
            if top_iv:
                c.print(
                    "  tightest static intervals (format: var | interval):",
                    markup=False,
                )
                var_w = max(3, max(len(str(r["var"])) for r in top_iv))
                for r in top_iv:
                    c.print(
                        f"  {str(r['var']):<{var_w}} | {r['interval']}",
                        markup=False,
                    )
        return

    tree = Tree("[bold]Absint Summary[/bold]", guide_style="dim")

    def _node_text(label: str, value: str = "", notes: str = "") -> str:
        base = f"[cyan]{escape(label)}[/cyan]"
        if value:
            base += f" [dim]:[/dim] [bold]{escape(value)}[/bold]"
        if notes:
            base += f" [dim]- {escape(notes)}[/dim]"
        return base

    def _add_section(label: str, rows: list[tuple[str, str]]) -> Tree:
        sec = tree.add(f"[bold]{escape(label)}[/bold]")
        for metric, value in sorted(rows, key=lambda r: r[0]):
            sec.add(_node_text(metric, value))
        return sec

    _add_section(
        "input",
        [
            ("path", str(tac.path or "-")),
            ("show", ", ".join(sorted(modes))),
            ("blocks", str(len(filtered_program.blocks))),
        ],
    )

    if "degree" in modes:
        deg_obj = payload["degree"]  # type: ignore[assignment]
        sec = _add_section(
            "degree",
            [
                ("time", _format_duration(timings_sec.get("degree", 0.0))),
                ("symbols_total", str(deg_obj["symbols_total"])),
                ("max_degree", str(deg_obj["max_degree"])),
                ("saw_top", str(deg_obj["saw_top"])),
                ("top_symbols_count", str(deg_obj["top_symbols_count"])),
                ("nonlinear_count", str(deg_obj["nonlinear_count"])),
            ],
        )
        dist_node = sec.add(_node_text("distribution"))
        for k in sorted(deg_obj["distribution"], key=lambda x: int(x)):
            dist_node.add(_node_text(f"deg_{k}", str(deg_obj["distribution"][k])))
        top_rows = deg_obj["top_nonlinear"]  # type: ignore[index]
        if top_rows:
            top_node = sec.add(
                _node_text(
                    "top non-linear",
                    notes=f"degree >= {deg_obj['min_degree_filter']}; block:loc | lhs | command",
                )
            )
            for r in top_rows:
                top_node.add(
                    _node_text(
                        f"deg {r['degree']}  {r['block_id']}:{r['cmd_index'] + 1}",
                        str(r["lhs"]),
                        str(r["rendered"]),
                    )
                )
        top_unk = deg_obj["top_unknown"]  # type: ignore[index]
        if top_unk:
            unk_node = sec.add(_node_text("top unknown", notes="degree=TOP"))
            for r in top_unk:
                unk_node.add(
                    _node_text(
                        f"{r['block_id']}:{r['cmd_index'] + 1}",
                        str(r["lhs"]),
                        str(r["rendered"]),
                    )
                )

    if "interval" in modes:
        iv_obj = payload["interval"]  # type: ignore[assignment]
        sec = _add_section(
            "interval",
            [
                ("time", _format_duration(timings_sec.get("interval", 0.0))),
                ("static_symbols_total", str(iv_obj["static_symbols_total"])),
                ("concrete_count", str(iv_obj["concrete_count"])),
                ("partial_count", str(iv_obj["partial_count"])),
                ("top_count", str(iv_obj["top_count"])),
                ("bot_count", str(iv_obj["bot_count"])),
                ("blocks_with_local", str(iv_obj["blocks_with_local"])),
                ("local_entries_total", str(iv_obj["local_entries_total"])),
            ],
        )
        top_iv = iv_obj["top_tightest"]  # type: ignore[index]
        if top_iv:
            top_node = sec.add(
                _node_text("tightest static intervals", notes="var | interval")
            )
            for r in top_iv:
                top_node.add(_node_text(str(r["var"]), str(r["interval"])))

    c.print(tree)
