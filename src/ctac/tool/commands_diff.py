from __future__ import annotations

import difflib
from pathlib import Path

import typer
from rich.table import Table

from ctac.diff.match_cfg import compare_matched_blocks, match_cfg_blocks
from ctac.parse import ParseError, parse_path
from ctac.tool.cli_runtime import PLAIN_HELP, agent_option, app, console, plain_requested
from ctac.tool.input_resolution import resolve_tac_input_path


def truncate_diff_lines(lines: list[str], max_lines: int) -> tuple[list[str], int]:
    if max_lines < 0:
        return lines, 0
    if len(lines) <= max_lines:
        return lines, 0
    keep = lines[:max_lines]
    omitted = len(lines) - max_lines
    return keep, omitted


@app.command("cfg-match")
def match_cfg_cmd(
    left: Path = typer.Argument(..., exists=True, dir_okay=True, readable=True),
    right: Path = typer.Argument(..., exists=True, dir_okay=True, readable=True),
    plain: bool = typer.Option(False, "--plain", help=PLAIN_HELP),
    agent: bool = agent_option(),
    min_score: float = typer.Option(
        0.45,
        "--min-score",
        min=0.0,
        max=1.0,
        help="Minimum pair score to consider as a block match.",
    ),
    const_weight: float = typer.Option(
        0.20,
        "--const-weight",
        min=0.0,
        max=1.0,
        help="Weight of constant-signature overlap in block matching.",
    ),
    max_rows: int = typer.Option(
        120,
        "--max-rows",
        min=1,
        help="Maximum number of matched rows to print.",
    ),
    weak_is_strong: bool = typer.Option(
        False,
        "--weak-is-strong",
        help="Parse snippet weak refs as strong refs.",
    ),
) -> None:
    """Coarse CFG block matching with weighted structural/meta features."""
    _ = agent
    plain = plain_requested(plain)
    c = console(plain)
    try:
        left_tac_path, left_w = resolve_tac_input_path(left)
        right_tac_path, right_w = resolve_tac_input_path(right)
        a = parse_path(left_tac_path, weak_is_strong=weak_is_strong)
        b = parse_path(right_tac_path, weak_is_strong=weak_is_strong)
        for w in left_w:
            c.print(f"input warning: left: {w}" if plain else f"[yellow]input warning:[/yellow] left: {w}")
        for w in right_w:
            c.print(f"input warning: right: {w}" if plain else f"[yellow]input warning:[/yellow] right: {w}")
    except ParseError as e:
        c.print(f"parse error: {e}" if plain else f"[red]parse error:[/red] {e}")
        raise typer.Exit(1) from e
    except ValueError as e:
        c.print(f"input error: {e}" if plain else f"[red]input error:[/red] {e}")
        raise typer.Exit(1) from e

    mr = match_cfg_blocks(a, b, min_score=min_score, const_weight=const_weight)
    c.print(f"# left blocks: {len(a.program.blocks)}")
    c.print(f"# right blocks: {len(b.program.blocks)}")
    c.print(f"# matched: {len(mr.matches)}")
    c.print(f"# unmatched_left: {len(mr.unmatched_left)}")
    c.print(f"# unmatched_right: {len(mr.unmatched_right)}")
    c.print(f"# min_score: {min_score:.2f}")
    c.print(f"# const_weight: {const_weight:.2f}")
    c.print("")

    rows = mr.matches[:max_rows]
    if plain:
        for m in rows:
            parts = []
            for k in ("source", "function", "const", "print", "scope", "degree", "ops", "count", "addr"):
                if k in m.components:
                    parts.append(f"{k}={m.components[k]:.2f}")
            c.print(
                f"{m.left_id} -> {m.right_id}  score={m.score:.3f}  "
                + (" ".join(parts) if parts else "")
            )
    else:
        t = Table(title="CFG Block Matches", expand=True)
        t.add_column("left", no_wrap=True)
        t.add_column("right", no_wrap=True)
        t.add_column("score", justify="right", no_wrap=True)
        t.add_column("signals", overflow="ellipsis")
        for m in rows:
            sig = []
            for k in ("source", "function", "const", "print", "scope", "degree", "ops", "count", "addr"):
                if k in m.components:
                    sig.append(f"{k}:{m.components[k]:.2f}")
            t.add_row(
                m.left_id,
                m.right_id,
                f"{m.score:.3f}",
                "  ".join(sig),
            )
        c.print(t)

    if len(mr.matches) > max_rows:
        c.print(f"# ... truncated {len(mr.matches) - max_rows} more matched row(s)")
    if mr.unmatched_left:
        c.print("# unmatched left:")
        c.print(", ".join(mr.unmatched_left[:80]))
        if len(mr.unmatched_left) > 80:
            c.print(f"# ... {len(mr.unmatched_left) - 80} more left blocks")
    if mr.unmatched_right:
        c.print("# unmatched right:")
        c.print(", ".join(mr.unmatched_right[:80]))
        if len(mr.unmatched_right) > 80:
            c.print(f"# ... {len(mr.unmatched_right) - 80} more right blocks")


@app.command("bb-diff")
def bb_diff_cmd(
    left: Path = typer.Argument(..., exists=True, dir_okay=True, readable=True),
    right: Path = typer.Argument(..., exists=True, dir_okay=True, readable=True),
    plain: bool = typer.Option(False, "--plain", help=PLAIN_HELP),
    agent: bool = agent_option(),
    min_score: float = typer.Option(
        0.45,
        "--min-score",
        min=0.0,
        max=1.0,
        help="Minimum CFG match score to consider candidate block pairs.",
    ),
    const_weight: float = typer.Option(
        0.20,
        "--const-weight",
        min=0.0,
        max=1.0,
        help="Weight of constant-signature overlap in CFG block matching.",
    ),
    normalize_vars: bool = typer.Option(
        True,
        "--normalize-vars/--raw-vars",
        help="Normalize variable/register names in each matched block before comparison.",
    ),
    include_source: bool = typer.Option(
        False,
        "--with-source/--no-source",
        help="Include source-location lines in per-block compared lines.",
    ),
    drop_empty: bool = typer.Option(
        True,
        "--drop-empty/--keep-empty",
        help="Ignore pretty-printer-empty lines (e.g., skipped labels/annotations) in BB comparison.",
    ),
    max_blocks: int = typer.Option(
        20,
        "--max-blocks",
        min=1,
        help="Maximum number of changed matched blocks to print with diffs.",
    ),
    context_lines: int = typer.Option(
        2,
        "--context",
        min=0,
        max=8,
        help="Unified diff context lines per changed block.",
    ),
    max_diff_lines: int = typer.Option(
        120,
        "--max-diff-lines",
        min=1,
        help="Maximum diff lines printed per changed block.",
    ),
    weak_is_strong: bool = typer.Option(
        False,
        "--weak-is-strong",
        help="Parse snippet weak refs as strong refs.",
    ),
) -> None:
    """Compare matched basic blocks and print per-block semantic deltas."""
    _ = agent
    plain = plain_requested(plain)
    c = console(plain)
    try:
        left_tac_path, left_w = resolve_tac_input_path(left)
        right_tac_path, right_w = resolve_tac_input_path(right)
        a = parse_path(left_tac_path, weak_is_strong=weak_is_strong)
        b = parse_path(right_tac_path, weak_is_strong=weak_is_strong)
        for w in left_w:
            c.print(f"input warning: left: {w}" if plain else f"[yellow]input warning:[/yellow] left: {w}")
        for w in right_w:
            c.print(f"input warning: right: {w}" if plain else f"[yellow]input warning:[/yellow] right: {w}")
    except ParseError as e:
        c.print(f"parse error: {e}" if plain else f"[red]parse error:[/red] {e}")
        raise typer.Exit(1) from e
    except ValueError as e:
        c.print(f"input error: {e}" if plain else f"[red]input error:[/red] {e}")
        raise typer.Exit(1) from e

    mr = match_cfg_blocks(a, b, min_score=min_score, const_weight=const_weight)
    comps = compare_matched_blocks(
        a,
        b,
        match_result=mr,
        normalize_vars=normalize_vars,
        include_source=include_source,
        drop_empty_lines=drop_empty,
    )
    changed = [x for x in comps if x.changed]
    unchanged = [x for x in comps if not x.changed]

    c.print(f"# left blocks: {len(a.program.blocks)}")
    c.print(f"# right blocks: {len(b.program.blocks)}")
    c.print(f"# matched blocks: {len(comps)}")
    c.print(f"# changed matched blocks: {len(changed)}")
    c.print(f"# unchanged matched blocks: {len(unchanged)}")
    c.print(f"# unmatched left: {len(mr.unmatched_left)}")
    c.print(f"# unmatched right: {len(mr.unmatched_right)}")
    c.print(f"# const_weight: {const_weight:.2f}")
    c.print(f"# normalize_vars: {normalize_vars}")
    c.print(f"# with_source: {include_source}")
    c.print(f"# drop_empty: {drop_empty}")
    c.print(f"# max_diff_lines: {max_diff_lines}")
    c.print("")

    top = changed[:max_blocks]
    for bc in top:
        hdr = (
            f"## {bc.left_id} -> {bc.right_id}  "
            f"match={bc.match_score:.3f}  bb_similarity={bc.similarity:.3f}"
        )
        c.print(hdr if plain else f"[bold]{hdr}[/bold]")
        if not bc.diff_lines:
            c.print("  # no diff")
            continue
        dlines = list(
            difflib.unified_diff(
                bc.left_lines,
                bc.right_lines,
                fromfile=bc.left_id,
                tofile=bc.right_id,
                lineterm="",
                n=context_lines,
            )
        )
        shown, omitted = truncate_diff_lines(dlines, max_diff_lines)
        for ln in shown:
            c.print(ln)
        if omitted:
            c.print(f"# ... truncated {omitted} diff line(s) for this block")
        c.print("")

    if len(changed) > max_blocks:
        c.print(f"# ... truncated {len(changed) - max_blocks} more changed matched block(s)")
    if mr.unmatched_left:
        c.print("# unmatched left block ids:")
        c.print(", ".join(mr.unmatched_left[:100]))
        if len(mr.unmatched_left) > 100:
            c.print(f"# ... {len(mr.unmatched_left) - 100} more")
    if mr.unmatched_right:
        c.print("# unmatched right block ids:")
        c.print(", ".join(mr.unmatched_right[:100]))
        if len(mr.unmatched_right) > 100:
            c.print(f"# ... {len(mr.unmatched_right) - 100} more")
