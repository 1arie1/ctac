"""``ctac op-diff`` — per-stat frequency delta between two TAC files.

Fastest way to spot encoder drift between two Certora Prover versions.
Parses both sides, runs ``collect_tac_stats`` on each, and prints the
delta grouped by section (``expression_ops``, ``command_kinds``,
``memory``, ``nonlinear_ops``, ``overview``). Rows with zero delta are
hidden by default; ``--show-unchanged`` surfaces them for audit use.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Annotated

import typer

from ctac.parse import ParseError, parse_path
from ctac.tool.cli_runtime import (
    COMPARE_PANEL,
    PLAIN_HELP,
    agent_option,
    app,
    console,
    plain_requested,
)
from ctac.tool.commands_stats import collect_tac_stats
from ctac.tool.input_resolution import resolve_tac_input_path, resolve_user_path
from ctac.tool.stats_model import StatType, StatValue


# Order matters: sections render in this order when `--show all`.
_SECTIONS: tuple[str, ...] = (
    "overview",
    "expression_ops",
    "nonlinear_ops",
    "command_kinds",
    "memory",
    "top_blocks_by_command_count",
)

# Skip keys that are never interesting for a cross-build diff
# (they're about the file path, not its content).
_SKIP_KEYS: frozenset[str] = frozenset({"overview.path"})


def _stats_dict(path: Path) -> dict[str, StatValue]:
    """Flat ``dotted-path -> StatValue`` view of `collect_tac_stats`."""
    tac = parse_path(path)
    stats = collect_tac_stats(tac, by_cmd_kind=True, top_blocks=0)
    return {e.path: e.value for e in stats.entries()}


def _section_of(key: str) -> str:
    return key.split(".", 1)[0]


def _parse_show(show: str) -> set[str]:
    """Parse ``--show`` into a set of section names (or {"all"})."""
    parts = {p.strip() for p in show.split(",") if p.strip()}
    if not parts or parts == {"all"}:
        return {"all"}
    invalid = parts - set(_SECTIONS) - {"all"}
    if invalid:
        raise typer.BadParameter(
            f"unknown section(s): {', '.join(sorted(invalid))}. "
            f"Valid: {', '.join(_SECTIONS)}, all.",
            param_hint="--show",
        )
    if "all" in parts:
        return {"all"}
    return parts


_NUMERIC_KINDS = (StatType.NUM, StatType.TIME)


def _is_numeric_stat(sv: StatValue | None) -> bool:
    return sv is not None and sv.kind in _NUMERIC_KINDS


def _delta(
    left: StatValue | None, right: StatValue | None
) -> tuple[object, object, object | None, bool]:
    """Return ``(left_value, right_value, numeric_delta_or_None, changed)``.

    If either side is numeric, the missing side is treated as 0 (so a
    stat that appears only on the right shows as ``0 -> N (+N)``
    rather than the noisy ``None -> N``). For string-valued stats, a
    missing side stays ``None`` so the diff is self-explanatory.
    """
    l_num = _is_numeric_stat(left)
    r_num = _is_numeric_stat(right)
    if l_num or r_num:
        lv = left.value if l_num else 0
        rv = right.value if r_num else 0
        delta = rv - lv  # type: ignore[operator]
        return lv, rv, delta, delta != 0
    lv = left.value if left is not None else None
    rv = right.value if right is not None else None
    return lv, rv, None, lv != rv


def _fmt_row(key: str, left_v: object, right_v: object, delta: object | None) -> str:
    """Plain format for one diff row (section-local key)."""
    local = key.split(".", 1)[1] if "." in key else key
    if delta is None:
        # String-valued or one-sided.
        return f"{local}: {left_v!s} -> {right_v!s}"
    # Numeric.
    sign = "+" if delta > 0 else ""  # type: ignore[operator]
    return f"{local}: {left_v} -> {right_v}  ({sign}{delta})"


def _plain_output(
    c,
    left_path: Path,
    right_path: Path,
    left_stats: dict[str, StatValue],
    right_stats: dict[str, StatValue],
    requested: set[str],
    show_unchanged: bool,
    quiet: bool,
) -> bool:
    """Emit the plain-text diff. Returns True iff at least one delta was printed."""
    if not quiet:
        c.print(f"# left:  {left_path}")
        c.print(f"# right: {right_path}")
    c.print("op-diff:")
    printed_any = False
    for section in _SECTIONS:
        if requested != {"all"} and section not in requested:
            continue
        keys = sorted(
            k for k in (set(left_stats) | set(right_stats))
            if _section_of(k) == section and k not in _SKIP_KEYS
        )
        section_rows: list[str] = []
        for key in keys:
            lv, rv, delta, changed = _delta(left_stats.get(key), right_stats.get(key))
            if not changed and not show_unchanged:
                continue
            section_rows.append(_fmt_row(key, lv, rv, delta))
        if not section_rows:
            continue
        c.print(f"  {section}:")
        for row in section_rows:
            c.print(f"    {row}")
        printed_any = True
    if not printed_any:
        c.print("  (no deltas)")
    return printed_any


def _json_output(
    left_path: Path,
    right_path: Path,
    left_stats: dict[str, StatValue],
    right_stats: dict[str, StatValue],
    requested: set[str],
    show_unchanged: bool,
) -> str:
    out: dict[str, object] = {
        "left": str(left_path),
        "right": str(right_path),
        "sections": {},
    }
    sections_out: dict[str, list[dict[str, object]]] = {}
    for section in _SECTIONS:
        if requested != {"all"} and section not in requested:
            continue
        keys = sorted(
            k for k in (set(left_stats) | set(right_stats))
            if _section_of(k) == section and k not in _SKIP_KEYS
        )
        rows: list[dict[str, object]] = []
        for key in keys:
            lv, rv, delta, changed = _delta(left_stats.get(key), right_stats.get(key))
            if not changed and not show_unchanged:
                continue
            rows.append(
                {"key": key, "left": lv, "right": rv, "delta": delta, "changed": changed}
            )
        if rows:
            sections_out[section] = rows
    out["sections"] = sections_out
    return json.dumps(out, indent=2, sort_keys=False) + "\n"


_OPDIFF_EPILOG = (
    "[bold green]What it does[/bold green]  Parses both inputs, runs the "
    "[cyan]ctac stats[/cyan] collector on each, and prints the per-stat delta "
    "grouped by section ([cyan]expression_ops[/cyan], "
    "[cyan]command_kinds[/cyan], [cyan]memory[/cyan], "
    "[cyan]nonlinear_ops[/cyan], [cyan]overview[/cyan]). Rows with zero "
    "delta are suppressed; pass [cyan]--show-unchanged[/cyan] to include them "
    "(useful for auditing).\n\n"
    "[bold green]Sibling commands[/bold green]  [cyan]cfg-match[/cyan] for "
    "block correspondence, [cyan]bb-diff[/cyan] for per-block semantic diffs, "
    "[cyan]op-diff[/cyan] for whole-file operator counts — fastest way to "
    "spot encoder drift between two Prover versions.\n\n"
    "[bold green]Examples[/bold green]\n\n"
    "[cyan]ctac op-diff a.tac b.tac --plain[/cyan]"
    "  [dim]# all non-zero deltas[/dim]\n\n"
    "[cyan]ctac op-diff a.tac b.tac --plain --show expression_ops[/cyan]"
    "  [dim]# just op-count delta[/dim]\n\n"
    "[cyan]ctac op-diff a.tac b.tac --plain --show-unchanged[/cyan]"
    "  [dim]# every stat, not just changes[/dim]\n\n"
    "[cyan]ctac op-diff a.tac b.tac --json[/cyan]"
    "  [dim]# machine-readable output[/dim]"
)


@app.command("op-diff", rich_help_panel=COMPARE_PANEL, epilog=_OPDIFF_EPILOG)
def op_diff_cmd(
    left: Annotated[
        Path,
        typer.Argument(
            ...,
            exists=True,
            dir_okay=True,
            readable=True,
            help="Left-hand TAC / .sbf.json file or directory.",
        ),
    ],
    right: Annotated[
        Path,
        typer.Argument(
            ...,
            exists=True,
            dir_okay=True,
            readable=True,
            help="Right-hand TAC / .sbf.json file or directory.",
        ),
    ],
    plain: bool = typer.Option(False, "--plain", help=PLAIN_HELP),
    agent: bool = agent_option(),
    show: str = typer.Option(
        "all",
        "--show",
        help=(
            "Comma-separated sections to include: expression_ops, "
            "command_kinds, memory, nonlinear_ops, overview, "
            "top_blocks_by_command_count. Default 'all'."
        ),
    ),
    show_unchanged: bool = typer.Option(
        False,
        "--show-unchanged",
        help="Include stats with a zero delta (audit mode).",
    ),
    json_out: bool = typer.Option(
        False,
        "--json",
        help="Emit machine-readable JSON instead of the plain grouped view.",
    ),
    quiet: bool = typer.Option(
        False,
        "-q",
        "--quiet",
        help="Suppress the `# left:` / `# right:` header lines (plain mode only).",
    ),
) -> None:
    """Per-stat frequency delta between two TAC files (grouped by section)."""
    _ = agent
    plain = plain_requested(plain)
    c = console(plain)
    try:
        left_user, left_w = resolve_user_path(left)
        right_user, right_w = resolve_user_path(right)
        left_resolved, left_tw = resolve_tac_input_path(left_user)
        right_resolved, right_tw = resolve_tac_input_path(right_user)
    except ValueError as e:
        c.print(f"input error: {e}" if plain else f"[red]input error:[/red] {e}")
        raise typer.Exit(1) from e

    for w in left_w + left_tw:
        c.print(f"# left warning: {w}")
    for w in right_w + right_tw:
        c.print(f"# right warning: {w}")

    try:
        requested = _parse_show(show)
    except typer.BadParameter:
        raise

    try:
        left_stats = _stats_dict(left_resolved)
        right_stats = _stats_dict(right_resolved)
    except ParseError as e:
        c.print(f"parse error: {e}" if plain else f"[red]parse error:[/red] {e}")
        raise typer.Exit(1) from e

    if json_out:
        # Bypass Rich to avoid terminal-width wrapping that would corrupt
        # long strings (file paths, hex constants) into invalid JSON.
        print(
            _json_output(
                left_resolved,
                right_resolved,
                left_stats,
                right_stats,
                requested,
                show_unchanged,
            ),
            end="",
        )
        return

    _plain_output(
        c,
        left_resolved,
        right_resolved,
        left_stats,
        right_stats,
        requested,
        show_unchanged,
        quiet,
    )
