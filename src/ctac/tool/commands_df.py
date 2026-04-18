from __future__ import annotations

import json
import time
from dataclasses import asdict
from pathlib import Path
from typing import Annotated, Optional

import typer
from rich.markup import escape
from rich.tree import Tree

from ctac.ast.pretty import configured_printer
from ctac.analysis import (
    analyze_control_dependence,
    analyze_dsa,
    analyze_liveness,
    analyze_use_before_def,
    eliminate_dead_assignments,
    extract_def_use,
    normalize_program_symbols,
)
from ctac.parse import ParseError, parse_path
from ctac.tool.cli_runtime import PLAIN_HELP, agent_option, app, console, plain_requested
from ctac.tool.filters import CfgFilterOptions, apply_cfg_filters
from ctac.tool.input_resolution import resolve_tac_input_path, resolve_user_path


def _program_point_key(block_id: str, cmd_index: int) -> str:
    return f"{block_id}:{cmd_index}"


def _display_loc(
    block_id: str,
    cmd_index: int | None,
    *,
    pretty_loc_by_point: dict[tuple[str, int], int] | None = None,
    use_pretty_loc: bool = False,
) -> str:
    if cmd_index is None:
        return f"{block_id}:-"
    if use_pretty_loc and pretty_loc_by_point is not None:
        loc = pretty_loc_by_point.get((block_id, cmd_index))
        if loc is not None:
            return f"{block_id}:{loc}"
    return f"{block_id}:{cmd_index + 1}"


def _parse_show_modes(raw: str) -> set[str]:
    valid = {
        "def-use",
        "liveness",
        "dce",
        "use-before-def",
        "dsa",
        "control-dependence",
        "all",
    }
    items = {x.strip().lower() for x in raw.split(",") if x.strip()}
    if not items:
        raise typer.BadParameter("at least one mode required", param_hint="--show")
    unknown = sorted(items - valid)
    if unknown:
        raise typer.BadParameter(f"unknown --show mode(s): {', '.join(unknown)}", param_hint="--show")
    if "all" in items:
        return valid - {"all"}
    return items


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


@app.command("df")
def dataflow_cmd(
    path: Optional[Path] = typer.Argument(None),
    plain: bool = typer.Option(False, "--plain", help=PLAIN_HELP),
    agent: bool = agent_option(),
    show: Annotated[
        str,
        typer.Option(
            "--show",
            help=(
                "Comma-separated analysis outputs: def-use,liveness,dce,use-before-def,dsa,"
                "control-dependence,all"
            ),
        ),
    ] = "all",
    json_out: bool = typer.Option(False, "--json", help="Emit machine-readable JSON output."),
    details: bool = typer.Option(
        False,
        "--details/--summary",
        help="Show detailed per-item listings instead of concise summary stats.",
    ),
    max_items: int = typer.Option(
        20,
        "--max-items",
        min=1,
        help="Maximum detailed rows per section when --details is enabled.",
    ),
    raw_output: bool = typer.Option(
        False,
        "--raw",
        help="Use raw TAC command text for detail lines (default: pretty-printed lines).",
    ),
    strip_var_suffixes: bool = typer.Option(
        True,
        "--strip-var-suffix/--keep-var-suffix",
        help="Strip TAC var suffixes like ':1' in analysis symbols (default: strip).",
    ),
    to_block: Annotated[Optional[str], typer.Option("--to", metavar="NBID")] = None,
    from_block: Annotated[Optional[str], typer.Option("--from", metavar="NBID")] = None,
    only: Annotated[Optional[str], typer.Option("--only")] = None,
    id_contains: Annotated[Optional[str], typer.Option("--id-contains")] = None,
    id_regex: Annotated[Optional[str], typer.Option("--id-regex")] = None,
    cmd_contains: Annotated[Optional[str], typer.Option("--cmd-contains")] = None,
    exclude: Annotated[Optional[str], typer.Option("--exclude")] = None,
) -> None:
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
    t0 = time.perf_counter()
    normalized_program = normalize_program_symbols(
        filtered_program,
        strip_var_suffixes=strip_var_suffixes,
    )
    timings_sec["normalize"] = time.perf_counter() - t0
    t0 = time.perf_counter()
    du = extract_def_use(normalized_program, strip_var_suffixes=strip_var_suffixes)
    timings_sec["def-use"] = time.perf_counter() - t0
    lv = None
    render_by_point: dict[tuple[str, int], str] = {}
    pretty_loc_by_point: dict[tuple[str, int], int] = {}
    if details:
        pp = configured_printer(
            "raw" if raw_output else "human",
            strip_var_suffixes=strip_var_suffixes,
            human_patterns=True,
        )
        for b in normalized_program.blocks:
            vis_loc = 0
            for idx, cmd in enumerate(b.commands):
                line = pp.print_cmd(cmd)
                if line is not None and line != "":
                    vis_loc += 1
                    pretty_loc_by_point[(b.id, idx)] = vis_loc
                render_by_point[(b.id, idx)] = line if line else cmd.raw
    payload: dict[str, object] = {
        "path": tac.path,
        "show": sorted(modes),
        "blocks": len(filtered_program.blocks),
        "input_warnings": user_warnings + input_warnings,
        "filter_warnings": filter_warnings,
        "detail_rendering": "raw" if raw_output else "pretty",
    }

    if "def-use" in modes:
        payload["def_use"] = {
            "defs_by_symbol": {k: len(v) for k, v in sorted(du.definitions_by_symbol.items())},
            "uses_by_symbol": {k: len(v) for k, v in sorted(du.uses_by_symbol.items())},
        }
    if "liveness" in modes:
        t0 = time.perf_counter()
        lv = analyze_liveness(normalized_program, strip_var_suffixes=strip_var_suffixes, def_use=du)
        payload["liveness"] = {
            "live_in_by_block": lv.live_in_by_block,
            "live_out_by_block": lv.live_out_by_block,
            "live_before_command": {
                _program_point_key(pt.block_id, pt.cmd_index): vals
                for pt, vals in lv.live_before_command.items()
            },
            "live_after_command": {
                _program_point_key(pt.block_id, pt.cmd_index): vals
                for pt, vals in lv.live_after_command.items()
            },
        }
        timings_sec["liveness"] = time.perf_counter() - t0
    if "dce" in modes:
        if lv is None:
            t0 = time.perf_counter()
            lv = analyze_liveness(normalized_program, strip_var_suffixes=strip_var_suffixes, def_use=du)
            timings_sec.setdefault("liveness", time.perf_counter() - t0)
        t0 = time.perf_counter()
        dce = eliminate_dead_assignments(
            normalized_program,
            strip_var_suffixes=strip_var_suffixes,
            liveness=lv,
        )
        payload["dce"] = {
            "removed_count": len(dce.removed),
            "removed": [asdict(x) for x in dce.removed],
            "remaining_commands": sum(len(b.commands) for b in dce.program.blocks),
        }
        timings_sec["dce"] = time.perf_counter() - t0
    if "use-before-def" in modes:
        t0 = time.perf_counter()
        ubd = analyze_use_before_def(
            normalized_program,
            strip_var_suffixes=strip_var_suffixes,
            def_use=du,
        )
        payload["use_before_def"] = {"issues": [asdict(x) for x in ubd.issues]}
        timings_sec["use-before-def"] = time.perf_counter() - t0
    if "dsa" in modes:
        t0 = time.perf_counter()
        dsa = analyze_dsa(
            normalized_program,
            strip_var_suffixes=strip_var_suffixes,
            def_use=du,
        )
        payload["dsa"] = {"is_valid": dsa.is_valid, "issues": [asdict(x) for x in dsa.issues]}
        timings_sec["dsa"] = time.perf_counter() - t0
    if "control-dependence" in modes:
        t0 = time.perf_counter()
        cd = analyze_control_dependence(normalized_program)
        payload["control_dependence"] = asdict(cd)
        timings_sec["control-dependence"] = time.perf_counter() - t0
    payload["timings_sec"] = {k: timings_sec[k] for k in sorted(timings_sec)}

    if json_out:
        c.print(json.dumps(payload, indent=2, sort_keys=True))
        return

    def _total_counts(x: dict[str, int]) -> int:
        return sum(x.values())

    def _top_items(x: dict[str, int]) -> list[tuple[str, int]]:
        return sorted(x.items(), key=lambda kv: (-kv[1], kv[0]))[:max_items]

    def _live_size(vals: dict[str, tuple[str, ...]]) -> int:
        if not vals:
            return 0
        return max(len(v) for v in vals.values())

    if plain:
        if tac.path:
            c.print(f"# path: {tac.path}", no_wrap=True, markup=False)
        for w in user_warnings + input_warnings:
            c.print(f"# input warning: {w}", markup=False)
        for w in filter_warnings:
            c.print(f"# {w}", markup=False)
        c.print(f"# show: {', '.join(sorted(modes))}", markup=False)
        c.print(f"# blocks: {len(filtered_program.blocks)}", markup=False)

        if "def-use" in modes:
            defs = payload["def_use"]["defs_by_symbol"]  # type: ignore[index]
            uses = payload["def_use"]["uses_by_symbol"]  # type: ignore[index]
            c.print("def-use:", markup=False)
            c.print(f"  time: {_format_duration(timings_sec.get('def-use', 0.0))}", markup=False)
            c.print(
                (
                    "  symbols_with_defs: "
                    f"{len(defs)}, symbols_with_uses: {len(uses)}, "
                    f"total_defs: {_total_counts(defs)}, total_uses: {_total_counts(uses)}"
                ),
                markup=False,
            )
            if details:
                for sym, cnt in _top_items(defs):
                    c.print(f"  def_count[{sym}] = {cnt}", markup=False)
                for sym, cnt in _top_items(uses):
                    c.print(f"  use_count[{sym}] = {cnt}", markup=False)

        if "liveness" in modes:
            assert lv is not None
            blocks_with_live_in = sum(1 for x in lv.live_in_by_block.values() if x)
            c.print("liveness:", markup=False)
            c.print(f"  time: {_format_duration(timings_sec.get('liveness', 0.0))}", markup=False)
            c.print(
                (
                    f"  blocks_with_live_in: {blocks_with_live_in}, "
                    f"max_live_in_size: {_live_size(lv.live_in_by_block)}, "
                    f"max_live_out_size: {_live_size(lv.live_out_by_block)}"
                ),
                markup=False,
            )
            if details:
                for bid in sorted(lv.live_in_by_block)[:max_items]:
                    li = ", ".join(lv.live_in_by_block[bid])
                    lo = ", ".join(lv.live_out_by_block[bid])
                    c.print(f"  {bid}: live_in=[{li}] live_out=[{lo}]", markup=False)

        if "dce" in modes:
            dce_obj = payload["dce"]  # type: ignore[assignment]
            c.print("dce:", markup=False)
            c.print(f"  time: {_format_duration(timings_sec.get('dce', 0.0))}", markup=False)
            c.print(
                (
                    f"  removed_count: {dce_obj['removed_count']}, "
                    f"remaining_commands: {dce_obj['remaining_commands']}"
                ),
                markup=False,
            )
            if details:
                removed_rows = dce_obj["removed"][:max_items]
                if removed_rows:
                    c.print("  format: block:loc | symbol | command", markup=False)
                    loc_w = max(
                        9,
                        max(
                            len(
                                _display_loc(
                                    e["block_id"],
                                    e["cmd_index"],
                                    pretty_loc_by_point=pretty_loc_by_point,
                                    use_pretty_loc=not raw_output,
                                )
                            )
                            for e in removed_rows
                        ),
                    )
                    sym_w = max(6, max(len(str(e["symbol"])) for e in removed_rows))
                    for ent in removed_rows:
                        rendered = render_by_point.get((ent["block_id"], ent["cmd_index"]), ent["raw"])
                        loc = _display_loc(
                            ent["block_id"],
                            ent["cmd_index"],
                            pretty_loc_by_point=pretty_loc_by_point,
                            use_pretty_loc=not raw_output,
                        )
                        sym = str(ent["symbol"])
                        c.print(f"  {loc:<{loc_w}} | {sym:<{sym_w}} | {rendered}", markup=False)

        if "use-before-def" in modes:
            ubd_obj = payload["use_before_def"]  # type: ignore[assignment]
            issue_count = len(ubd_obj["issues"])
            c.print("use-before-def:", markup=False)
            c.print(f"  time: {_format_duration(timings_sec.get('use-before-def', 0.0))}", markup=False)
            c.print(f"  issues: {issue_count}", markup=False)
            if details:
                issue_rows = ubd_obj["issues"][:max_items]
                if issue_rows:
                    c.print("  format: block:loc | symbol | command", markup=False)
                    loc_w = max(
                        9,
                        max(
                            len(
                                _display_loc(
                                    i["block_id"],
                                    i["cmd_index"],
                                    pretty_loc_by_point=pretty_loc_by_point,
                                    use_pretty_loc=not raw_output,
                                )
                            )
                            for i in issue_rows
                        ),
                    )
                    sym_w = max(6, max(len(str(i["symbol"])) for i in issue_rows))
                    for issue in issue_rows:
                        rendered = render_by_point.get((issue["block_id"], issue["cmd_index"]), issue["raw"])
                        loc = _display_loc(
                            issue["block_id"],
                            issue["cmd_index"],
                            pretty_loc_by_point=pretty_loc_by_point,
                            use_pretty_loc=not raw_output,
                        )
                        sym = str(issue["symbol"])
                        c.print(f"  {loc:<{loc_w}} | {sym:<{sym_w}} | {rendered}", markup=False)

        if "dsa" in modes:
            dsa_obj = payload["dsa"]  # type: ignore[assignment]
            issue_count = len(dsa_obj["issues"])
            c.print("dsa:", markup=False)
            c.print(f"  time: {_format_duration(timings_sec.get('dsa', 0.0))}", markup=False)
            c.print(f"  is_valid: {dsa_obj['is_valid']}, issues: {issue_count}", markup=False)
            if details:
                issue_rows = dsa_obj["issues"][:max_items]
                if issue_rows:
                    c.print("  format: kind | block:loc | symbol | command", markup=False)
                    kind_w = max(4, max(len(str(i["kind"])) for i in issue_rows))
                    loc_w = max(
                        9,
                        max(
                            len(
                                _display_loc(
                                    i["block_id"],
                                    i["cmd_index"],
                                    pretty_loc_by_point=pretty_loc_by_point,
                                    use_pretty_loc=not raw_output,
                                )
                            )
                            for i in issue_rows
                        ),
                    )
                    sym_w = max(
                        6,
                        max(len(str(i["symbol"]) if i["symbol"] is not None else "-") for i in issue_rows),
                    )
                    for issue in issue_rows:
                        cmd_idx = issue["cmd_index"] if issue["cmd_index"] is not None else "-"
                        sym = issue["symbol"] if issue["symbol"] is not None else "-"
                        rendered = (
                            render_by_point.get((issue["block_id"], issue["cmd_index"]), issue["detail"])
                            if issue["cmd_index"] is not None
                            else issue["detail"]
                        )
                        loc = _display_loc(
                            issue["block_id"],
                            issue["cmd_index"],
                            pretty_loc_by_point=pretty_loc_by_point,
                            use_pretty_loc=not raw_output,
                        )
                        c.print(
                            f"  {issue['kind']:<{kind_w}} | {loc:<{loc_w}} | {str(sym):<{sym_w}} | {rendered}",
                            markup=False,
                        )

        if "control-dependence" in modes:
            cd_obj = payload["control_dependence"]  # type: ignore[assignment]
            c.print("control-dependence:", markup=False)
            c.print(
                f"  time: {_format_duration(timings_sec.get('control-dependence', 0.0))}",
                markup=False,
            )
            c.print(f"  edges: {len(cd_obj['edges'])}", markup=False)
            for src, dst in cd_obj["edges"][: max_items if details else 0]:
                c.print(f"  {src} -> {dst}", markup=False)
        return

    tree = Tree("[bold]Data-flow Summary[/bold]", guide_style="dim")

    def _node_text(label: str, value: str = "", notes: str = "", *, value_markup: bool = False) -> str:
        base = f"[cyan]{escape(label)}[/cyan]"
        if value:
            val = value if value_markup else escape(value)
            base += f" [dim]:[/dim] [bold]{val}[/bold]"
        if notes:
            base += f" [dim]- {escape(notes)}[/dim]"
        return base

    def _status_value(ok: bool, ok_text: str, bad_text: str) -> str:
        if ok:
            return f"[green]{escape(ok_text)}[/green]"
        return f"[red]{escape(bad_text)}[/red]"

    def _warning_value(count: int) -> str:
        if count > 0:
            return f"[yellow]{count}[/yellow]"
        return f"[green]{count}[/green]"

    def _add_section(label: str, rows: list[tuple[str, str, str, bool]]) -> Tree:
        sec = tree.add(f"[bold]{escape(label)}[/bold]")
        for metric, value, notes, value_markup in sorted(rows, key=lambda r: r[0]):
            sec.add(_node_text(metric, value, notes, value_markup=value_markup))
        return sec

    input_rows: list[tuple[str, str, str, bool]] = [
        ("path", str(tac.path or "-"), "", False),
        ("show", ", ".join(sorted(modes)), "", False),
        ("blocks", str(len(filtered_program.blocks)), "", False),
    ]
    if user_warnings or input_warnings:
        input_rows.append(
            (
                "input_warnings",
                _warning_value(len(user_warnings) + len(input_warnings)),
                "",
                True,
            )
        )
    if filter_warnings:
        input_rows.append(("filter_warnings", _warning_value(len(filter_warnings)), "", True))
    _add_section("input", input_rows)

    if "def-use" in modes:
        defs = payload["def_use"]["defs_by_symbol"]  # type: ignore[index]
        uses = payload["def_use"]["uses_by_symbol"]  # type: ignore[index]
        sec = _add_section(
            "def-use",
            [
                ("time", _format_duration(timings_sec.get("def-use", 0.0)), "", False),
                ("symbols_with_defs", str(len(defs)), "", False),
                ("symbols_with_uses", str(len(uses)), "", False),
                ("total_defs", str(_total_counts(defs)), "", False),
                ("total_uses", str(_total_counts(uses)), "", False),
            ],
        )
        if details:
            top = sec.add(_node_text("top symbols"))
            for sym, cnt in sorted(_top_items(defs), key=lambda kv: kv[0]):
                top.add(_node_text(f"def_count[{sym}]", str(cnt), "top"))
            for sym, cnt in sorted(_top_items(uses), key=lambda kv: kv[0]):
                top.add(_node_text(f"use_count[{sym}]", str(cnt), "top"))

    if "liveness" in modes:
        assert lv is not None
        blocks_with_live_in = sum(1 for x in lv.live_in_by_block.values() if x)
        sec = _add_section(
            "liveness",
            [
                ("time", _format_duration(timings_sec.get("liveness", 0.0)), "", False),
                ("blocks_with_live_in", str(blocks_with_live_in), "", False),
                ("max_live_in_size", str(_live_size(lv.live_in_by_block)), "", False),
                ("max_live_out_size", str(_live_size(lv.live_out_by_block)), "", False),
            ],
        )
        if details:
            pb = sec.add(_node_text("per-block"))
            for bid in sorted(lv.live_in_by_block)[:max_items]:
                li = ", ".join(lv.live_in_by_block[bid]) or "-"
                lo = ", ".join(lv.live_out_by_block[bid]) or "-"
                pb.add(_node_text(f"block[{bid}]", "-", f"live_in={li}; live_out={lo}"))

    if "dce" in modes:
        dce_obj = payload["dce"]  # type: ignore[assignment]
        sec = _add_section(
            "dce",
            [
                ("time", _format_duration(timings_sec.get("dce", 0.0)), "", False),
                ("removed_count", str(dce_obj["removed_count"]), "", False),
                ("remaining_commands", str(dce_obj["remaining_commands"]), "", False),
            ],
        )
        if details:
            removed = sec.add(_node_text("removed defs"))
            removed_entries = sorted(
                dce_obj["removed"],
                key=lambda e: (str(e["block_id"]), int(e["cmd_index"]), str(e["symbol"])),
            )[:max_items]
            for ent in removed_entries:
                rendered = render_by_point.get((ent["block_id"], ent["cmd_index"]), ent["raw"])
                removed.add(
                    _node_text(
                        f"remove {_display_loc(ent['block_id'], ent['cmd_index'], pretty_loc_by_point=pretty_loc_by_point, use_pretty_loc=not raw_output)}",
                        str(ent["symbol"]),
                        str(rendered),
                    )
                )

    if "use-before-def" in modes:
        ubd_obj = payload["use_before_def"]  # type: ignore[assignment]
        issue_count = len(ubd_obj["issues"])
        status = _status_value(issue_count == 0, "ok", "issues")
        sec = _add_section(
            "use-before-def",
            [
                ("time", _format_duration(timings_sec.get("use-before-def", 0.0)), "", False),
                ("status", status, "", True),
                ("issue_count", _warning_value(issue_count), "", True),
            ],
        )
        if details:
            issues = sec.add(_node_text("issues"))
            issues.add(_node_text("format", "block:loc | symbol | command"))
            issue_rows = sorted(
                ubd_obj["issues"],
                key=lambda i: (str(i["block_id"]), int(i["cmd_index"]), str(i["symbol"])),
            )[:max_items]
            for issue in issue_rows:
                rendered = render_by_point.get((issue["block_id"], issue["cmd_index"]), issue["raw"])
                issues.add(
                    _node_text(
                        _display_loc(
                            issue["block_id"],
                            issue["cmd_index"],
                            pretty_loc_by_point=pretty_loc_by_point,
                            use_pretty_loc=not raw_output,
                        ),
                        str(issue["symbol"]),
                        str(rendered),
                    )
                )

    if "dsa" in modes:
        dsa_obj = payload["dsa"]  # type: ignore[assignment]
        issue_count = len(dsa_obj["issues"])
        status = _status_value(bool(dsa_obj["is_valid"]), "valid", "invalid")
        sec = _add_section(
            "dsa",
            [
                ("time", _format_duration(timings_sec.get("dsa", 0.0)), "", False),
                ("status", status, "", True),
                ("issue_count", _warning_value(issue_count), "", True),
            ],
        )
        if details:
            issues = sec.add(_node_text("issues"))
            issues.add(_node_text("format", "kind | block:loc | symbol | command"))
            issue_rows = sorted(
                dsa_obj["issues"],
                key=lambda i: (
                    str(i["block_id"]),
                    int(i["cmd_index"]) if i["cmd_index"] is not None else -1,
                    str(i["symbol"]) if i["symbol"] is not None else "",
                    str(i["kind"]),
                ),
            )[:max_items]
            for issue in issue_rows:
                cmd_idx = issue["cmd_index"] if issue["cmd_index"] is not None else "-"
                sym = issue["symbol"] if issue["symbol"] is not None else "-"
                issues.add(
                    _node_text(
                        f"{issue['kind']} {_display_loc(issue['block_id'], issue['cmd_index'], pretty_loc_by_point=pretty_loc_by_point, use_pretty_loc=not raw_output)}",
                        str(sym),
                        str(
                            render_by_point.get((issue["block_id"], issue["cmd_index"]), issue["detail"])
                            if issue["cmd_index"] is not None
                            else issue["detail"]
                        ),
                    )
                )

    if "control-dependence" in modes:
        cd_obj = payload["control_dependence"]  # type: ignore[assignment]
        sec = _add_section(
            "control-dependence",
            [
                ("time", _format_duration(timings_sec.get("control-dependence", 0.0)), "", False),
                ("edge_count", str(len(cd_obj["edges"])), "", False),
            ],
        )
        if details:
            edges = sec.add(_node_text("edges"))
            for src, dst in sorted(cd_obj["edges"])[:max_items]:
                edges.add(_node_text(f"{src} -> {dst}"))

    c.print(tree)
