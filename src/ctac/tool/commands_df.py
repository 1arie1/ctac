from __future__ import annotations

import json
from dataclasses import asdict
from pathlib import Path
from typing import Annotated, Optional

import typer
from rich.markup import escape
from rich.tree import Tree

from ctac.analysis import (
    analyze_control_dependence,
    analyze_dsa,
    analyze_liveness,
    analyze_use_before_def,
    eliminate_dead_assignments,
    extract_def_use,
)
from ctac.parse import ParseError, parse_path
from ctac.tool.cli_runtime import PLAIN_HELP, agent_option, app, console, plain_requested
from ctac.tool.filters import CfgFilterOptions, apply_cfg_filters
from ctac.tool.input_resolution import resolve_tac_input_path, resolve_user_path


def _program_point_key(block_id: str, cmd_index: int) -> str:
    return f"{block_id}:{cmd_index}"


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

    du = extract_def_use(filtered_program, strip_var_suffixes=strip_var_suffixes)
    lv = None
    payload: dict[str, object] = {
        "path": tac.path,
        "show": sorted(modes),
        "blocks": len(filtered_program.blocks),
        "input_warnings": user_warnings + input_warnings,
        "filter_warnings": filter_warnings,
    }

    if "def-use" in modes:
        payload["def_use"] = {
            "defs_by_symbol": {k: len(v) for k, v in sorted(du.definitions_by_symbol.items())},
            "uses_by_symbol": {k: len(v) for k, v in sorted(du.uses_by_symbol.items())},
        }
    if "liveness" in modes:
        lv = analyze_liveness(filtered_program, strip_var_suffixes=strip_var_suffixes, def_use=du)
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
    if "dce" in modes:
        if lv is None:
            lv = analyze_liveness(filtered_program, strip_var_suffixes=strip_var_suffixes, def_use=du)
        dce = eliminate_dead_assignments(
            filtered_program,
            strip_var_suffixes=strip_var_suffixes,
            liveness=lv,
        )
        payload["dce"] = {
            "removed_count": len(dce.removed),
            "removed": [asdict(x) for x in dce.removed],
            "remaining_commands": sum(len(b.commands) for b in dce.program.blocks),
        }
    if "use-before-def" in modes:
        ubd = analyze_use_before_def(
            filtered_program,
            strip_var_suffixes=strip_var_suffixes,
            def_use=du,
        )
        payload["use_before_def"] = {"issues": [asdict(x) for x in ubd.issues]}
    if "dsa" in modes:
        dsa = analyze_dsa(
            filtered_program,
            strip_var_suffixes=strip_var_suffixes,
            def_use=du,
        )
        payload["dsa"] = {"is_valid": dsa.is_valid, "issues": [asdict(x) for x in dsa.issues]}
    if "control-dependence" in modes:
        cd = analyze_control_dependence(filtered_program)
        payload["control_dependence"] = asdict(cd)

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
            c.print(
                (
                    f"  removed_count: {dce_obj['removed_count']}, "
                    f"remaining_commands: {dce_obj['remaining_commands']}"
                ),
                markup=False,
            )
            for ent in dce_obj["removed"][: max_items if details else 0]:
                c.print(
                    f"  remove {ent['block_id']}:{ent['cmd_index']} "
                    f"{ent['cmd_kind']} {ent['symbol']}  # {ent['raw']}",
                    markup=False,
                )

        if "use-before-def" in modes:
            ubd_obj = payload["use_before_def"]  # type: ignore[assignment]
            issue_count = len(ubd_obj["issues"])
            c.print("use-before-def:", markup=False)
            c.print(f"  issues: {issue_count}", markup=False)
            for issue in ubd_obj["issues"][: max_items if details else 0]:
                c.print(
                    f"  {issue['block_id']}:{issue['cmd_index']} {issue['symbol']} "
                    f"[{issue['cmd_kind']}] {issue['raw']}",
                    markup=False,
                )

        if "dsa" in modes:
            dsa_obj = payload["dsa"]  # type: ignore[assignment]
            issue_count = len(dsa_obj["issues"])
            c.print("dsa:", markup=False)
            c.print(f"  is_valid: {dsa_obj['is_valid']}, issues: {issue_count}", markup=False)
            for issue in dsa_obj["issues"][: max_items if details else 0]:
                cmd_idx = issue["cmd_index"] if issue["cmd_index"] is not None else "-"
                sym = issue["symbol"] if issue["symbol"] is not None else "-"
                c.print(
                    f"  {issue['kind']} {issue['block_id']}:{cmd_idx} {sym}  # {issue['detail']}",
                    markup=False,
                )

        if "control-dependence" in modes:
            cd_obj = payload["control_dependence"]  # type: ignore[assignment]
            c.print("control-dependence:", markup=False)
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
        for metric, value, notes, value_markup in rows:
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
                ("symbols_with_defs", str(len(defs)), "", False),
                ("symbols_with_uses", str(len(uses)), "", False),
                ("total_defs", str(_total_counts(defs)), "", False),
                ("total_uses", str(_total_counts(uses)), "", False),
            ],
        )
        if details:
            top = sec.add(_node_text("top symbols"))
            for sym, cnt in _top_items(defs):
                top.add(_node_text(f"def_count[{sym}]", str(cnt), "top"))
            for sym, cnt in _top_items(uses):
                top.add(_node_text(f"use_count[{sym}]", str(cnt), "top"))

    if "liveness" in modes:
        assert lv is not None
        blocks_with_live_in = sum(1 for x in lv.live_in_by_block.values() if x)
        sec = _add_section(
            "liveness",
            [
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
                ("removed_count", str(dce_obj["removed_count"]), "", False),
                ("remaining_commands", str(dce_obj["remaining_commands"]), "", False),
            ],
        )
        if details:
            removed = sec.add(_node_text("removed defs"))
            for ent in dce_obj["removed"][:max_items]:
                removed.add(
                    _node_text(
                        f"remove {ent['block_id']}:{ent['cmd_index']}",
                        str(ent["symbol"]),
                        str(ent["raw"]),
                    )
                )

    if "use-before-def" in modes:
        ubd_obj = payload["use_before_def"]  # type: ignore[assignment]
        issue_count = len(ubd_obj["issues"])
        status = _status_value(issue_count == 0, "ok", "issues")
        sec = _add_section(
            "use-before-def",
            [
                ("status", status, "", True),
                ("issue_count", _warning_value(issue_count), "", True),
            ],
        )
        if details:
            issues = sec.add(_node_text("issues"))
            for issue in ubd_obj["issues"][:max_items]:
                issues.add(
                    _node_text(
                        f"{issue['block_id']}:{issue['cmd_index']}",
                        str(issue["symbol"]),
                        str(issue["raw"]),
                    )
                )

    if "dsa" in modes:
        dsa_obj = payload["dsa"]  # type: ignore[assignment]
        issue_count = len(dsa_obj["issues"])
        status = _status_value(bool(dsa_obj["is_valid"]), "valid", "invalid")
        sec = _add_section(
            "dsa",
            [
                ("status", status, "", True),
                ("issue_count", _warning_value(issue_count), "", True),
            ],
        )
        if details:
            issues = sec.add(_node_text("issues"))
            for issue in dsa_obj["issues"][:max_items]:
                cmd_idx = issue["cmd_index"] if issue["cmd_index"] is not None else "-"
                sym = issue["symbol"] if issue["symbol"] is not None else "-"
                issues.add(
                    _node_text(
                        f"{issue['kind']} {issue['block_id']}:{cmd_idx}",
                        str(sym),
                        str(issue["detail"]),
                    )
                )

    if "control-dependence" in modes:
        cd_obj = payload["control_dependence"]  # type: ignore[assignment]
        sec = _add_section(
            "control-dependence",
            [("edge_count", str(len(cd_obj["edges"])), "", False)],
        )
        if details:
            edges = sec.add(_node_text("edges"))
            for src, dst in cd_obj["edges"][:max_items]:
                edges.add(_node_text(f"{src} -> {dst}"))

    c.print(tree)
