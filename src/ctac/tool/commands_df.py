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
from ctac.ast.run_format import pp_terminator_line
from ctac.analysis import (
    analyze_control_dependence,
    analyze_dsa,
    analyze_liveness,
    analyze_use_before_def,
    eliminate_dead_assignments,
    eliminate_useless_assumes,
    extract_def_use,
    normalize_program_symbols,
)
from ctac.graph import Cfg
from ctac.parse import ParseError, parse_path, render_tac_file
from ctac.tool.cli_runtime import PLAIN_HELP, agent_option, app, console, plain_requested
from ctac.tool.filters import CfgFilterOptions, apply_cfg_filters
from ctac.tool.input_resolution import resolve_tac_input_path, resolve_user_path
from ctac.tool.stats_model import StatsCollection
from ctac.tool.stats_render import render_plain_stats, render_rich_stats_tree


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
    aliases = {"useless-assume": "uce"}
    valid = {
        "def-use",
        "liveness",
        "dce",
        "uce",
        "use-before-def",
        "dsa",
        "control-dependence",
        "all",
    }
    items = {aliases.get(x.strip().lower(), x.strip().lower()) for x in raw.split(",") if x.strip()}
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


def _normalize_output_style(style: str) -> str:
    s = style.strip().lower()
    if s not in {"pp", "raw"}:
        raise typer.BadParameter("use one of: pp, raw", param_hint="--style")
    return s


def _render_program_pp_lines(
    program,
    *,
    strip_var_suffixes: bool,
) -> list[str]:
    pp = configured_printer(
        "human",
        strip_var_suffixes=strip_var_suffixes,
        human_patterns=True,
    )
    out: list[str] = []
    for b in Cfg(program).ordered_blocks():
        out.append(f"{b.id}:")
        for cmd in b.commands:
            line = pp.print_cmd(cmd)
            if line is not None and line != "":
                out.append(f"  {line}")
        term = pp_terminator_line(b, strip_var_suffixes=strip_var_suffixes)
        if term is not None:
            out.append(f"  {term}")
        elif b.successors:
            out.append(f"  goto {', '.join(b.successors)}")
        else:
            out.append("  stop")
        out.append("")
    return out


def _program_topologically_ordered(program):
    return type(program)(blocks=Cfg(program).ordered_blocks())


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
                "control-dependence,uce,all"
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
    weak_is_strong: bool = typer.Option(
        False,
        "--weak-is-strong",
        help="Parse snippet weak refs as strong refs (annotations behave as strong uses).",
    ),
    output_path: Annotated[
        Optional[Path],
        typer.Option("-o", "--output", help="Write transformed output to this path."),
    ] = None,
    output_style: Annotated[
        Optional[str],
        typer.Option("--style", help="Transformed output style: pp or raw."),
    ] = None,
    to_block: Annotated[Optional[str], typer.Option("--to", metavar="NBID")] = None,
    from_block: Annotated[Optional[str], typer.Option("--from", metavar="NBID")] = None,
    only: Annotated[Optional[str], typer.Option("--only")] = None,
    id_contains: Annotated[Optional[str], typer.Option("--id-contains")] = None,
    id_regex: Annotated[Optional[str], typer.Option("--id-regex")] = None,
    cmd_contains: Annotated[Optional[str], typer.Option("--cmd-contains")] = None,
    exclude: Annotated[Optional[str], typer.Option("--exclude")] = None,
) -> None:
    """Run TAC data-flow analyses and report summaries or detailed diagnostics."""
    _ = agent
    plain = plain_requested(plain)
    c = console(plain)
    style: str | None = None
    if output_style is not None:
        style = _normalize_output_style(output_style)
    try:
        modes = _parse_show_modes(show)
        user_path, user_warnings = resolve_user_path(path)
        tac_path, input_warnings = resolve_tac_input_path(user_path)
        tac = parse_path(tac_path, weak_is_strong=weak_is_strong)
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
    transformed_program = normalized_program
    has_transform_output = False
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
        weak_use_rows = [
            {
                "symbol": us.symbol,
                "block_id": us.block_id,
                "cmd_index": us.cmd_index,
                "cmd_kind": us.cmd_kind,
                "raw": us.raw,
            }
            for b in normalized_program.blocks
            for us in du.by_block[b.id].weak_use_sites
        ]
        payload["def_use"] = {
            "defs_by_symbol": {k: len(v) for k, v in sorted(du.definitions_by_symbol.items())},
            "uses_by_symbol": {k: len(v) for k, v in sorted(du.uses_by_symbol.items())},
            "weak_uses_by_symbol": {k: len(v) for k, v in sorted(du.weak_uses_by_symbol.items())},
            "weak_uses": weak_use_rows,
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
    if "uce" in modes or "useless-assume" in modes:
        t0 = time.perf_counter()
        uce = eliminate_useless_assumes(
            transformed_program,
            strip_var_suffixes=strip_var_suffixes,
        )
        payload["uce"] = {
            "removed_count": len(uce.removed),
            "removed": [asdict(x) for x in uce.removed],
            "remaining_commands": sum(len(b.commands) for b in uce.program.blocks),
        }
        transformed_program = uce.program
        has_transform_output = True
        timings_sec["uce"] = time.perf_counter() - t0
    if "dce" in modes:
        dce_input = transformed_program
        if dce_input is normalized_program and lv is not None:
            lv_for_dce = lv
        else:
            t0 = time.perf_counter()
            dce_du = (
                du
                if dce_input is normalized_program
                else extract_def_use(dce_input, strip_var_suffixes=strip_var_suffixes)
            )
            lv_for_dce = analyze_liveness(
                dce_input,
                strip_var_suffixes=strip_var_suffixes,
                def_use=dce_du,
            )
            if dce_input is normalized_program:
                lv = lv_for_dce
                timings_sec.setdefault("liveness", time.perf_counter() - t0)
        t0 = time.perf_counter()
        dce = eliminate_dead_assignments(
            dce_input,
            strip_var_suffixes=strip_var_suffixes,
            liveness=lv_for_dce,
        )
        payload["dce"] = {
            "removed_count": len(dce.removed),
            "removed": [asdict(x) for x in dce.removed],
            "remaining_commands": sum(len(b.commands) for b in dce.program.blocks),
        }
        transformed_program = dce.program
        has_transform_output = True
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

    wants_output = output_path is not None or style is not None
    if wants_output and not has_transform_output:
        raise typer.BadParameter(
            "transformed output is available only when at least one transform pass is selected (currently: dce, uce)",
            param_hint="-o/--style",
        )
    if output_path is not None and style is None:
        style = "raw"
    if output_path is None and style is not None and json_out:
        raise typer.BadParameter(
            "--style without -o is incompatible with --json output",
            param_hint="--style",
        )

    transformed_text: str | None = None
    transformed_lines: list[str] | None = None
    transformed_program_out = _program_topologically_ordered(transformed_program)
    if has_transform_output and style == "raw":
        transformed_text = render_tac_file(tac, program=transformed_program_out)
    elif has_transform_output and style == "pp":
        transformed_lines = _render_program_pp_lines(
            transformed_program_out,
            strip_var_suffixes=strip_var_suffixes,
        )

    if output_path is not None:
        assert style is not None
        text_to_write = (
            transformed_text
            if style == "raw"
            else ("\n".join(transformed_lines or []) + ("\n" if transformed_lines else ""))
        )
        output_path.write_text(text_to_write, encoding="utf-8")

    if json_out:
        c.print(json.dumps(payload, indent=2, sort_keys=True))
        if output_path is not None:
            c.print(f"# wrote transformed output: {output_path}")
        return

    def _total_counts(x: dict[str, int]) -> int:
        return sum(x.values())

    def _top_items(x: dict[str, int]) -> list[tuple[str, int]]:
        return sorted(x.items(), key=lambda kv: (-kv[1], kv[0]))[:max_items]

    def _live_size(vals: dict[str, tuple[str, ...]]) -> int:
        if not vals:
            return 0
        return max(len(v) for v in vals.values())

    summary_stats = StatsCollection()
    summary_stats.add_str("input.path", str(tac.path or "-"))
    summary_stats.add_str("input.show", ", ".join(sorted(modes)))
    summary_stats.add_num("input.blocks", len(filtered_program.blocks))
    summary_stats.add_num("input.input_warnings", len(user_warnings) + len(input_warnings))
    summary_stats.add_num("input.filter_warnings", len(filter_warnings))
    for name in sorted(timings_sec):
        summary_stats.add_time(f"timings.{name}", timings_sec[name], unit="s")

    if "def-use" in modes:
        defs = payload["def_use"]["defs_by_symbol"]  # type: ignore[index]
        uses = payload["def_use"]["uses_by_symbol"]  # type: ignore[index]
        weak_uses = payload["def_use"]["weak_uses_by_symbol"]  # type: ignore[index]
        summary_stats.add_num("def_use.symbols_with_defs", len(defs))
        summary_stats.add_num("def_use.symbols_with_uses", len(uses))
        summary_stats.add_num("def_use.symbols_with_weak_uses", len(weak_uses))
        summary_stats.add_num("def_use.total_defs", _total_counts(defs))
        summary_stats.add_num("def_use.total_uses", _total_counts(uses))
        summary_stats.add_num("def_use.total_weak_uses", _total_counts(weak_uses))

    if "liveness" in modes:
        assert lv is not None
        blocks_with_live_in = sum(1 for x in lv.live_in_by_block.values() if x)
        summary_stats.add_num("liveness.blocks_with_live_in", blocks_with_live_in)
        summary_stats.add_num("liveness.max_live_in_size", _live_size(lv.live_in_by_block))
        summary_stats.add_num("liveness.max_live_out_size", _live_size(lv.live_out_by_block))

    if "dce" in modes:
        dce_obj = payload["dce"]  # type: ignore[assignment]
        summary_stats.add_num("dce.removed_count", dce_obj["removed_count"])
        summary_stats.add_num("dce.remaining_commands", dce_obj["remaining_commands"])

    if "uce" in modes or "useless-assume" in modes:
        uce_obj = payload["uce"]  # type: ignore[assignment]
        summary_stats.add_num("uce.removed_count", uce_obj["removed_count"])
        summary_stats.add_num("uce.remaining_commands", uce_obj["remaining_commands"])

    if "use-before-def" in modes:
        ubd_obj = payload["use_before_def"]  # type: ignore[assignment]
        issue_count = len(ubd_obj["issues"])
        summary_stats.add_str("use_before_def.status", "ok" if issue_count == 0 else "issues")
        summary_stats.add_num("use_before_def.issue_count", issue_count)

    if "dsa" in modes:
        dsa_obj = payload["dsa"]  # type: ignore[assignment]
        issue_count = len(dsa_obj["issues"])
        summary_stats.add_str("dsa.status", "valid" if dsa_obj["is_valid"] else "invalid")
        summary_stats.add_num("dsa.issue_count", issue_count)

    if "control-dependence" in modes:
        cd_obj = payload["control_dependence"]  # type: ignore[assignment]
        summary_stats.add_num("control_dependence.edge_count", len(cd_obj["edges"]))

    if not details:
        if plain:
            for line in render_plain_stats(summary_stats):
                c.print(line, markup=False)
        else:
            c.print(render_rich_stats_tree(summary_stats, root_label="dataflow_summary"))

        if output_path is not None:
            c.print(f"# wrote transformed output: {output_path}", markup=False)
        if style is not None and output_path is None:
            c.print("# transformed output:", markup=False)
            if style == "raw":
                for ln in (transformed_text or "").splitlines():
                    c.print(ln, markup=False)
            else:
                for ln in transformed_lines or []:
                    c.print(ln, markup=False)
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

        if "def-use" in modes:
            defs = payload["def_use"]["defs_by_symbol"]  # type: ignore[index]
            uses = payload["def_use"]["uses_by_symbol"]  # type: ignore[index]
            weak_uses = payload["def_use"]["weak_uses_by_symbol"]  # type: ignore[index]
            c.print("def-use:", markup=False)
            c.print(f"  time: {_format_duration(timings_sec.get('def-use', 0.0))}", markup=False)
            c.print(
                (
                    "  symbols_with_defs: "
                    f"{len(defs)}, symbols_with_uses: {len(uses)}, "
                    f"symbols_with_weak_uses: {len(weak_uses)}, "
                    f"total_defs: {_total_counts(defs)}, total_uses: {_total_counts(uses)}, "
                    f"total_weak_uses: {_total_counts(weak_uses)}"
                ),
                markup=False,
            )
            if details:
                for sym, cnt in _top_items(defs):
                    c.print(f"  def_count[{sym}] = {cnt}", markup=False)
                for sym, cnt in _top_items(uses):
                    c.print(f"  use_count[{sym}] = {cnt}", markup=False)
                for sym, cnt in _top_items(weak_uses):
                    c.print(f"  weak_use_count[{sym}] = {cnt}", markup=False)
                weak_rows = sorted(
                    payload["def_use"]["weak_uses"],  # type: ignore[index]
                    key=lambda w: (str(w["block_id"]), int(w["cmd_index"]), str(w["symbol"])),
                )[:max_items]
                if weak_rows:
                    c.print("  weak_uses_format: block:loc | symbol | command", markup=False)
                    loc_w = max(
                        9,
                        max(
                            len(
                                _display_loc(
                                    w["block_id"],
                                    w["cmd_index"],
                                    pretty_loc_by_point=pretty_loc_by_point,
                                    use_pretty_loc=not raw_output,
                                )
                            )
                            for w in weak_rows
                        ),
                    )
                    sym_w = max(6, max(len(str(w["symbol"])) for w in weak_rows))
                    for w in weak_rows:
                        rendered = render_by_point.get((w["block_id"], w["cmd_index"]), w["raw"])
                        loc = _display_loc(
                            w["block_id"],
                            w["cmd_index"],
                            pretty_loc_by_point=pretty_loc_by_point,
                            use_pretty_loc=not raw_output,
                        )
                        c.print(f"  {loc:<{loc_w}} | {str(w['symbol']):<{sym_w}} | {rendered}", markup=False)

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

        if "uce" in modes or "useless-assume" in modes:
            uce_obj = payload["uce"]  # type: ignore[assignment]
            c.print("uce:", markup=False)
            c.print(f"  time: {_format_duration(timings_sec.get('uce', 0.0))}", markup=False)
            c.print(
                (
                    f"  removed_count: {uce_obj['removed_count']}, "
                    f"remaining_commands: {uce_obj['remaining_commands']}"
                ),
                markup=False,
            )
            if details:
                removed_rows = uce_obj["removed"][:max_items]
                if removed_rows:
                    c.print("  format: block:loc | symbol | reason | command", markup=False)
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
                    reason_w = max(6, max(len(str(e["reason"])) for e in removed_rows))
                    for ent in removed_rows:
                        rendered = render_by_point.get((ent["block_id"], ent["cmd_index"]), ent["raw"])
                        loc = _display_loc(
                            ent["block_id"],
                            ent["cmd_index"],
                            pretty_loc_by_point=pretty_loc_by_point,
                            use_pretty_loc=not raw_output,
                        )
                        sym = str(ent["symbol"])
                        reason = str(ent["reason"])
                        c.print(
                            f"  {loc:<{loc_w}} | {sym:<{sym_w}} | {reason:<{reason_w}} | {rendered}",
                            markup=False,
                        )

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
        if output_path is not None:
            c.print(f"# wrote transformed output: {output_path}", markup=False)
        if style is not None and output_path is None:
            c.print("# transformed output:", markup=False)
            if style == "raw":
                for ln in (transformed_text or "").splitlines():
                    c.print(ln, markup=False)
            else:
                for ln in transformed_lines or []:
                    c.print(ln, markup=False)
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
        weak_uses = payload["def_use"]["weak_uses_by_symbol"]  # type: ignore[index]
        sec = _add_section(
            "def-use",
            [
                ("time", _format_duration(timings_sec.get("def-use", 0.0)), "", False),
                ("symbols_with_defs", str(len(defs)), "", False),
                ("symbols_with_uses", str(len(uses)), "", False),
                ("symbols_with_weak_uses", str(len(weak_uses)), "", False),
                ("total_defs", str(_total_counts(defs)), "", False),
                ("total_uses", str(_total_counts(uses)), "", False),
                ("total_weak_uses", str(_total_counts(weak_uses)), "", False),
            ],
        )
        if details:
            top = sec.add(_node_text("top symbols"))
            for sym, cnt in sorted(_top_items(defs), key=lambda kv: kv[0]):
                top.add(_node_text(f"def_count[{sym}]", str(cnt), "top"))
            for sym, cnt in sorted(_top_items(uses), key=lambda kv: kv[0]):
                top.add(_node_text(f"use_count[{sym}]", str(cnt), "top"))
            for sym, cnt in sorted(_top_items(weak_uses), key=lambda kv: kv[0]):
                top.add(_node_text(f"weak_use_count[{sym}]", str(cnt), "top"))
            weak_rows = sorted(
                payload["def_use"]["weak_uses"],  # type: ignore[index]
                key=lambda w: (str(w["block_id"]), int(w["cmd_index"]), str(w["symbol"])),
            )[:max_items]
            if weak_rows:
                weak_node = sec.add(_node_text("weak-use sites"))
                weak_node.add(_node_text("format", "block:loc | symbol | command"))
                for w in weak_rows:
                    rendered = render_by_point.get((w["block_id"], w["cmd_index"]), w["raw"])
                    weak_node.add(
                        _node_text(
                            _display_loc(
                                w["block_id"],
                                w["cmd_index"],
                                pretty_loc_by_point=pretty_loc_by_point,
                                use_pretty_loc=not raw_output,
                            ),
                            str(w["symbol"]),
                            str(rendered),
                        )
                    )

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

    if "uce" in modes or "useless-assume" in modes:
        uce_obj = payload["uce"]  # type: ignore[assignment]
        sec = _add_section(
            "uce",
            [
                ("time", _format_duration(timings_sec.get("uce", 0.0)), "", False),
                ("removed_count", str(uce_obj["removed_count"]), "", False),
                ("remaining_commands", str(uce_obj["remaining_commands"]), "", False),
            ],
        )
        if details:
            removed = sec.add(_node_text("removed assumes"))
            removed_entries = sorted(
                uce_obj["removed"],
                key=lambda e: (str(e["block_id"]), int(e["cmd_index"]), str(e["symbol"])),
            )[:max_items]
            for ent in removed_entries:
                rendered = render_by_point.get((ent["block_id"], ent["cmd_index"]), ent["raw"])
                removed.add(
                    _node_text(
                        f"remove {_display_loc(ent['block_id'], ent['cmd_index'], pretty_loc_by_point=pretty_loc_by_point, use_pretty_loc=not raw_output)}",
                        str(ent["symbol"]),
                        f"{ent['reason']}; {rendered}",
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
    if output_path is not None:
        c.print(f"[cyan]wrote transformed output[/cyan]: [bold]{escape(str(output_path))}[/bold]")
    if style is not None and output_path is None:
        c.print("[bold]Transformed Output[/bold]")
        if style == "raw":
            for ln in (transformed_text or "").splitlines():
                c.print(ln, markup=False)
        else:
            for ln in transformed_lines or []:
                c.print(ln)
