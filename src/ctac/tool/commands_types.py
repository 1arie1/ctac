"""`ctac types` — sound, possibly-incomplete kind inference for TAC registers.

Lattice ``Top | Int | Ptr | Bot``. Identifies registers used as
`Select`/`Store` indices (`Ptr`), arithmetic-only registers (`Int`),
and registers where the structural evidence is contradictory (`Bot`).
The most useful pivot for downstream work is ``--show ptr``: a list
of every register that is provably a pointer in the program.
"""

from __future__ import annotations

import contextlib
import json
import sys
from collections import Counter
from collections.abc import Iterator
from dataclasses import asdict
from pathlib import Path
from typing import Annotated, Optional, TextIO

import typer

from ctac.analysis.symbols import canonical_symbol, classify_sort
from ctac.analysis.type_infer import (
    TypeKind,
    TypeTraceEntry,
    TypeTraceSink,
    analyze_types,
)
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

_VALID_SHOW = ("all", "ptr", "int", "top", "bot")
_DEFAULT_SHOW = "all"


_TYPES_EPILOG = (
    "[bold green]What this answers[/bold green]  "
    "Which TAC registers are pointers (used as memory indices), which "
    "are integers (operands of arithmetic), and which are unconstrained.\n\n"
    "[bold green]Lattice[/bold green]  [cyan]Top[/cyan] (no commitment), "
    "[cyan]Int[/cyan], [cyan]Ptr[/cyan], [cyan]Bot[/cyan] (contradictory).\n\n"
    "[bold green]Soundness[/bold green]  Never claims [cyan]Int[/cyan] "
    "for a register that is actually a pointer, or vice-versa. May label "
    "[cyan]Top[/cyan] when use evidence is insufficient.\n\n"
    "[bold green]Examples[/bold green]\n\n"
    "[cyan]ctac types f.tac --plain[/cyan]"
    "  [dim]# full table + summary counts[/dim]\n\n"
    "[cyan]ctac types f.tac --plain --show ptr[/cyan]"
    "  [dim]# only the pointer registers[/dim]\n\n"
    "[cyan]ctac types f.tac --plain --by-class[/cyan]"
    "  [dim]# group by union-find equivalence class[/dim]\n\n"
    "[cyan]ctac types f.tac --plain --json[/cyan]"
    "  [dim]# machine-readable[/dim]"
)


@contextlib.contextmanager
def _open_trace_file(path: Path | None) -> Iterator[TextIO | None]:
    """Yield a writable text stream for ``--trace``, or ``None`` if disabled.

    ``path == Path("-")`` writes to stdout (mirroring ``ctac rw --trace``);
    any other path is opened for writing."""
    if path is None:
        yield None
        return
    if str(path) == "-":
        yield sys.stdout
        return
    with path.open("w") as fh:
        yield fh


def _make_trace_sink(
    fh: TextIO | None, *, only_canon: set[str] | None
) -> TypeTraceSink | None:
    """JSONL writer with an optional per-class filter.

    ``only_canon`` is the set of canonical symbol names whose events the
    user wants. When set, an event is written iff at least one of its
    affected symbols (after canonicalization) is in the set OR the event's
    affected symbol shares a canonical name with one in the set."""
    if fh is None:
        return None

    def sink(entry: TypeTraceEntry) -> None:
        if only_canon is not None:
            symbols_canon = {canonical_symbol(s) for s in entry.symbols}
            if symbols_canon.isdisjoint(only_canon):
                return
        # asdict on a frozen dataclass yields a stable mapping; sorted keys
        # give deterministic output for tests / diffs.
        fh.write(json.dumps(asdict(entry), sort_keys=True) + "\n")

    return sink


def _parse_show(raw: str) -> set[str]:
    items = {x.strip().lower() for x in raw.split(",") if x.strip()}
    if not items:
        raise typer.BadParameter("at least one show kind required", param_hint="--show")
    valid = set(_VALID_SHOW)
    unknown = sorted(items - valid)
    if unknown:
        raise typer.BadParameter(
            f"unknown --show kind(s): {', '.join(unknown)}", param_hint="--show"
        )
    if "all" in items:
        return {"ptr", "int", "top", "bot"}
    return items


@app.command("types", rich_help_panel=ANALYZE_PANEL, epilog=_TYPES_EPILOG)
def types_cmd(
    path: Optional[Path] = typer.Argument(
        None, help="Path to .tac / .sbf.json file, or a Certora output directory."
    ),
    plain: bool = typer.Option(False, "--plain", help=PLAIN_HELP),
    agent: bool = agent_option(),
    show: Annotated[
        str,
        typer.Option(
            "--show",
            help="Comma-separated kinds to display: ptr,int,top,bot,all.",
            autocompletion=complete_choices(list(_VALID_SHOW)),
        ),
    ] = _DEFAULT_SHOW,
    by_class: bool = typer.Option(
        False,
        "--by-class",
        help=(
            "Group output by union-find equivalence class. Each class "
            "shows its kind and member symbols. Useful for spotting "
            "registers that share an equivalence class via copy / "
            "narrow / alignment passthrough."
        ),
    ),
    json_out: bool = typer.Option(
        False, "--json", help="Emit machine-readable JSON output."
    ),
    include_memory: bool = typer.Option(
        False,
        "--include-memory/--scalars-only",
        help=(
            "Include memory-sorted symbols (bytemap / ghostmap) in the "
            "output. Default off — kind inference applies to scalar "
            "values only."
        ),
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
    trace: Annotated[
        Optional[Path],
        typer.Option(
            "--trace",
            metavar="PATH",
            help=(
                "Write a JSONL constraint-event trace to PATH (use ``-`` "
                "for stdout). One record per meet, union, and per-"
                "AssignExpCmd RHS evaluation; fields: phase, iteration, "
                "block_id, cmd_index, kind, rule, symbols, before, after, "
                "detail, changed. Diagnostic for `Top`/`Bot` outcomes."
            ),
        ),
    ] = None,
    trace_symbol: Annotated[
        Optional[str],
        typer.Option(
            "--trace-symbol",
            metavar="SYM[,SYM...]",
            help=(
                "Comma-separated canonical symbol names to filter the "
                "trace by. Only events whose `symbols` field includes one "
                "of the names (after canonicalization) are written. "
                "Without this flag every event is emitted."
            ),
        ),
    ] = None,
) -> None:
    """Infer per-register kinds (Top / Int / Ptr / Bot) for a TAC program."""
    _ = agent
    plain = plain_requested(plain)
    c = console(plain)
    try:
        kinds_to_show = _parse_show(show)
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

    only_canon: set[str] | None = None
    if trace_symbol is not None:
        only_canon = {
            canonical_symbol(s.strip()) for s in trace_symbol.split(",") if s.strip()
        }
        if not only_canon:
            raise typer.BadParameter(
                "at least one symbol required", param_hint="--trace-symbol"
            )

    with _open_trace_file(trace) as trace_fh:
        sink = _make_trace_sink(trace_fh, only_canon=only_canon)
        result = analyze_types(filtered_program, trace_sink=sink)

    # Filter memory-sorted symbols out by default. classify_sort treats
    # `bytemap` and `ghostmap` as MEMORY; everything else (bv256, bool,
    # int) is SCALAR. Symbols not in the symbol table (rare; usually
    # internal temporaries) keep the default SCALAR classification.
    sorts = tac.symbol_sorts
    name_to_kind: dict[str, TypeKind] = {}
    for name, k in result.kind.items():
        if not include_memory:
            sort = sorts.get(name, "")
            if sort and classify_sort(sort).value == "memory":
                continue
        name_to_kind[name] = k

    counts: Counter[str] = Counter()
    for k in name_to_kind.values():
        counts[k.value] += 1

    payload: dict[str, object] = {
        "path": tac.path,
        "blocks": len(filtered_program.blocks),
        "input_warnings": user_warnings + input_warnings,
        "filter_warnings": filter_warnings,
        "iterations": result.iterations,
        "show": sorted(kinds_to_show),
        "counts": {
            "top": counts.get("Top", 0),
            "int": counts.get("Int", 0),
            "ptr": counts.get("Ptr", 0),
            "bot": counts.get("Bot", 0),
        },
    }

    if by_class:
        # Group by class root, but only keep classes that have at least
        # one displayed-kind member.
        class_rows: list[dict[str, object]] = []
        for root, members in result.class_members.items():
            visible_members = [m for m in members if m in name_to_kind]
            if not visible_members:
                continue
            kind_str = result.kind[visible_members[0]].value
            if kind_str.lower() not in kinds_to_show:
                continue
            class_rows.append(
                {
                    "root": root,
                    "kind": kind_str,
                    "size": len(visible_members),
                    "members": visible_members,
                }
            )
        class_rows.sort(key=lambda r: (r["kind"], -int(r["size"]), str(r["root"])))
        payload["classes"] = class_rows
    else:
        flat_rows = [
            {"name": name, "kind": k.value}
            for name, k in name_to_kind.items()
            if k.value.lower() in kinds_to_show
        ]
        flat_rows.sort(key=lambda r: (r["kind"], str(r["name"])))
        payload["symbols"] = flat_rows

    if json_out:
        typer.echo(json.dumps(payload, indent=2, sort_keys=True))
        return

    if plain:
        if tac.path:
            c.print(f"# path: {tac.path}", markup=False)
        for w in user_warnings + input_warnings:
            c.print(f"# input warning: {w}", markup=False)
        for w in filter_warnings:
            c.print(f"# {w}", markup=False)
        c.print(f"# blocks: {len(filtered_program.blocks)}", markup=False)
        c.print(f"# iterations: {result.iterations}", markup=False)
        cnt = payload["counts"]  # type: ignore[index]
        c.print(
            f"counts: ptr={cnt['ptr']}  int={cnt['int']}  top={cnt['top']}  bot={cnt['bot']}",
            markup=False,
        )
        if by_class:
            rows = payload["classes"]  # type: ignore[index]
            if not rows:
                return
            c.print("classes (kind | size | root | members):", markup=False)
            for r in rows:
                members_str = ", ".join(str(m) for m in r["members"])  # type: ignore[arg-type]
                c.print(
                    f"  {str(r['kind']):<3} | {int(r['size']):>4} | {str(r['root'])} | {members_str}",
                    markup=False,
                )
        else:
            rows = payload["symbols"]  # type: ignore[index]
            if not rows:
                return
            c.print("symbols (kind | name):", markup=False)
            for r in rows:
                c.print(f"  {str(r['kind']):<3} | {str(r['name'])}", markup=False)
        return

    # Rich output: a compact table.
    from rich.table import Table

    cnt = payload["counts"]  # type: ignore[index]
    c.print(
        f"[bold]types[/bold]  iterations={result.iterations}  "
        f"ptr=[bold]{cnt['ptr']}[/bold]  int=[bold]{cnt['int']}[/bold]  "
        f"top=[bold]{cnt['top']}[/bold]  bot=[bold]{cnt['bot']}[/bold]"
    )
    if by_class:
        rows = payload["classes"]  # type: ignore[index]
        if not rows:
            return
        table = Table(show_lines=False)
        table.add_column("kind")
        table.add_column("size", justify="right")
        table.add_column("root")
        table.add_column("members")
        for r in rows:
            members_str = ", ".join(str(m) for m in r["members"])  # type: ignore[arg-type]
            table.add_row(str(r["kind"]), str(r["size"]), str(r["root"]), members_str)
        c.print(table)
    else:
        rows = payload["symbols"]  # type: ignore[index]
        if not rows:
            return
        table = Table(show_lines=False)
        table.add_column("kind")
        table.add_column("name")
        for r in rows:
            table.add_row(str(r["kind"]), str(r["name"]))
        c.print(table)
