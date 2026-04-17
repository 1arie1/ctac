from __future__ import annotations

import difflib
import os
import re
from pathlib import Path
from typing import Annotated, Any, Optional

import typer
from rich.console import Console
from rich.table import Table
from rich.text import Text

from ctac.ast.models import TacFile
from ctac.diff.match_cfg import compare_matched_blocks, match_cfg_blocks
from ctac.eval import RunConfig, Value, parse_tac_model_path, run_program, value_to_text
from ctac.graph import Cfg, CfgFilter, CfgStyle
from ctac.parse import ParseError, parse_path
from ctac.tac_ast.nodes import AssignExpCmd, AssignHavocCmd
from ctac.tac_ast.pretty import DEFAULT_PRINTERS, configured_printer, pretty_lines
from ctac.tool.highlight import TAC_THEME, highlight_tac_line

app = typer.Typer(no_args_is_help=True, add_completion=False)


def _console(plain: bool) -> Console:
    force_terminal = None if plain else True
    return Console(
        force_terminal=force_terminal,
        no_color=plain or bool(os.environ.get("NO_COLOR")),
        highlight=False,
        theme=TAC_THEME,
    )


def _plain_requested(plain: bool) -> bool:
    return plain or os.environ.get("CTAC_PLAIN", "").lower() in ("1", "true", "yes")


def _truncate_diff_lines(lines: list[str], max_lines: int) -> tuple[list[str], int]:
    """Return at most `max_lines` lines and how many were omitted."""
    if max_lines < 0:
        return lines, 0
    if len(lines) <= max_lines:
        return lines, 0
    keep = lines[:max_lines]
    omitted = len(lines) - max_lines
    return keep, omitted


def _print_tac_stats(tac: TacFile, *, plain: bool) -> None:
    c = _console(plain)
    n_blocks = len(tac.program.blocks)
    n_cmds = sum(len(b.commands) for b in tac.program.blocks)
    n_meta_keys = len(tac.metas)
    sym_lines = tac.symbol_table_text.count("\n") + (1 if tac.symbol_table_text else 0)

    if plain:
        c.print(f"path: {tac.path}")
        c.print(f"symbol_table_lines: {sym_lines}")
        c.print(f"blocks: {n_blocks}")
        c.print(f"commands: {n_cmds}")
        c.print(f"metas_top_keys: {n_meta_keys}")
    else:
        c.print(f"[bold]path[/bold] {tac.path}")
        c.print(f"[bold]symbol table[/bold] ~{sym_lines} lines")
        c.print(f"[bold]blocks[/bold] {n_blocks}")
        c.print(f"[bold]commands[/bold] {n_cmds}")
        c.print(f"[bold]metas keys[/bold] {n_meta_keys}")


def _run_stats(path: Path, *, plain: bool) -> None:
    plain = _plain_requested(plain)
    c = _console(plain)
    try:
        tac = parse_path(path)
    except ParseError as e:
        if plain:
            c.print(f"parse error: {e}")
        else:
            c.print(f"[red]parse error:[/red] {e}")
        raise typer.Exit(1) from e
    _print_tac_stats(tac, plain=plain)


_PATH_KW = dict(exists=True, dir_okay=False, readable=True)
_PLAIN_HELP = "Plain text only (no Rich styling); also set CTAC_PLAIN=1 or NO_COLOR."


@app.command()
def stats(
    path: Path = typer.Argument(..., **_PATH_KW),
    plain: bool = typer.Option(False, "--plain", help=_PLAIN_HELP),
) -> None:
    """Print summary statistics for a .tac file (blocks, commands, metas, symbol table size)."""
    _run_stats(path, plain=plain)


@app.command()
def parse(
    path: Path = typer.Argument(..., **_PATH_KW),
    plain: bool = typer.Option(False, "--plain", help=_PLAIN_HELP),
) -> None:
    """Parse a .tac file and print basic statistics (same output as ``ctac stats``)."""
    _run_stats(path, plain=plain)


@app.command("cfg-match")
def match_cfg_cmd(
    left: Path = typer.Argument(..., exists=True, dir_okay=False, readable=True),
    right: Path = typer.Argument(..., exists=True, dir_okay=False, readable=True),
    plain: bool = typer.Option(False, "--plain", help=_PLAIN_HELP),
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
) -> None:
    """Coarse CFG block matching with weighted structural/meta features."""
    plain = _plain_requested(plain)
    c = _console(plain)
    try:
        a = parse_path(left)
        b = parse_path(right)
    except ParseError as e:
        c.print(f"parse error: {e}" if plain else f"[red]parse error:[/red] {e}")
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
    left: Path = typer.Argument(..., exists=True, dir_okay=False, readable=True),
    right: Path = typer.Argument(..., exists=True, dir_okay=False, readable=True),
    plain: bool = typer.Option(False, "--plain", help=_PLAIN_HELP),
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
) -> None:
    """Compare matched basic blocks and print per-block semantic deltas."""
    plain = _plain_requested(plain)
    c = _console(plain)
    try:
        a = parse_path(left)
        b = parse_path(right)
    except ParseError as e:
        c.print(f"parse error: {e}" if plain else f"[red]parse error:[/red] {e}")
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
        # Recompute diff with requested context for compactness.
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
        shown, omitted = _truncate_diff_lines(dlines, max_diff_lines)
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


def _normalize_cfg_style(raw: str) -> CfgStyle:
    s = raw.strip().lower()
    if s in ("goto", "edges"):
        return s  # type: ignore[return-value]
    raise typer.BadParameter("use 'goto' or 'edges'", param_hint="--style")


def _normalize_printer_name(raw: str) -> str:
    name = raw.strip().lower()
    if name in DEFAULT_PRINTERS.names():
        return name
    raise typer.BadParameter(
        f"unknown printer {raw!r}; choose one of: {', '.join(DEFAULT_PRINTERS.names())}",
        param_hint="--printer",
    )


def _build_cfg_filter(
    *,
    to_block: str | None,
    from_block: str | None,
    only: str | None,
    id_contains: str | None,
    id_regex: str | None,
    cmd_contains: str | None,
    exclude: str | None,
) -> CfgFilter:
    return CfgFilter(
        to_id=to_block,
        from_id=from_block,
        only_ids=Cfg.parse_csv_ids(only),
        id_contains=id_contains,
        id_regex=id_regex,
        cmd_contains=cmd_contains,
        exclude_ids=Cfg.parse_csv_ids(exclude),
    )


def _parse_user_value(text: str, kind: str) -> Value:
    t = text.strip()
    if kind == "bool":
        if t.lower() in ("1", "true", "t", "yes", "y"):
            return Value("bool", True)
        if t.lower() in ("0", "false", "f", "no", "n"):
            return Value("bool", False)
        raise ValueError(f"expected bool for havoc ({t!r})")
    if t.startswith(("0x", "0X")):
        n = int(t, 16)
    else:
        n = int(t, 10)
    if kind == "bv":
        return Value("bv", n)
    return Value("int", n)


_META_SUFFIX_RE = re.compile(r":\d+$")


def _strip_meta_suffix(name: str) -> str:
    return _META_SUFFIX_RE.sub("", name)


def _coerce_value_kind(v: Value, target_kind: str) -> Value:
    if v.kind == target_kind:
        return v
    if target_kind == "bool":
        return Value("bool", bool(v.data) if v.kind == "bool" else int(v.data) != 0)
    if target_kind == "int":
        if v.kind == "bool":
            return Value("int", 1 if bool(v.data) else 0)
        return Value("int", int(v.data))
    # target_kind == "bv"
    if v.kind == "bool":
        return Value("bv", 1 if bool(v.data) else 0)
    return Value("bv", int(v.data) % MOD_256)


def _values_equal(lhs: Value, rhs: Value) -> bool:
    if lhs.kind == rhs.kind:
        if lhs.kind == "bool":
            return bool(lhs.data) == bool(rhs.data)
        if lhs.kind == "bv":
            return int(lhs.data) % MOD_256 == int(rhs.data) % MOD_256
        return int(lhs.data) == int(rhs.data)
    rhs_cast = _coerce_value_kind(rhs, lhs.kind)
    return _values_equal(lhs, rhs_cast)


MODEL_HAVOC_FALLBACK_NUM = 12_345_678


def _model_fallback_value(kind: str) -> Value:
    if kind == "bool":
        return Value("bool", True)
    if kind == "int":
        return Value("int", MODEL_HAVOC_FALLBACK_NUM)
    return Value("bv", MODEL_HAVOC_FALLBACK_NUM)


def _trim_path_left(path: str, max_chars: int) -> str:
    if max_chars <= 0:
        return ""
    if len(path) <= max_chars:
        return path
    if max_chars <= 2:
        return "…"
    tail_budget = max_chars - 2  # reserve for "…/"
    tail = path[-tail_budget:]
    slash = tail.find("/")
    if slash > 0:
        tail = tail[slash + 1 :]
    if len(tail) + 2 > max_chars:
        tail = tail[-(max_chars - 2) :]
    return "…/" + tail


def _source_prefix_for_cmd(cmd: Any, metas: dict[str, Any], *, max_path_chars: int = 56) -> str | None:
    meta_idx = getattr(cmd, "meta_index", None)
    if meta_idx is None:
        return None
    bucket = metas.get(str(meta_idx))
    if not isinstance(bucket, list):
        return None

    def _mk_prefix(spec_file: Any, line: Any) -> str | None:
        if not isinstance(spec_file, str):
            return None
        if not isinstance(line, int):
            return None
        return f"{_trim_path_left(spec_file, max_path_chars)}:{line}"

    for ent in bucket:
        if not isinstance(ent, dict):
            continue
        key = ent.get("key")
        val = ent.get("value")
        if not isinstance(key, dict):
            continue

        name = key.get("name")
        if name == "cvl.range" and isinstance(val, dict):
            start = val.get("start")
            if isinstance(start, dict):
                p = _mk_prefix(val.get("specFile"), start.get("line"))
                if p is not None:
                    return p
        if name == "sbf.source.segment" and isinstance(val, dict):
            rng = val.get("range")
            if isinstance(rng, dict):
                start = rng.get("start")
                if isinstance(start, dict):
                    p = _mk_prefix(rng.get("specFile"), start.get("line"))
                    if p is not None:
                        return p
    return None


MOD_256 = 1 << 256
SINGLE_REPR_SMALL_MAX = 15


def _format_dec_10k(n: int) -> str:
    """Group decimal digits by 10_000 chunks for readability."""
    sign = "-" if n < 0 else ""
    s = str(abs(n))
    if len(s) <= 4:
        return f"{sign}{s}"
    parts: list[str] = []
    while s:
        parts.append(s[-4:])
        s = s[:-4]
    parts.reverse()
    return sign + "_".join(parts)


def _ilog2_pow2(n: int) -> int:
    return n.bit_length() - 1


def _pow2_family_label(n: int) -> str | None:
    """
    Human-friendly label for powers of two and near-powers.

    Returns one of:
    - ``2^k``
    - ``2^k+1``
    - ``2^k-1``
    or ``None`` if not in this family.
    """
    if n <= 0:
        return None
    if n & (n - 1) == 0:
        return f"2^{_ilog2_pow2(n)}"
    m = n - 1
    if m > 0 and (m & (m - 1) == 0):
        return f"2^{_ilog2_pow2(m)}+1"
    p = n + 1
    if p > 0 and (p & (p - 1) == 0):
        return f"2^{_ilog2_pow2(p)}-1"
    return None


def _pow10_family_label(n: int, *, near_delta: int = 9) -> str | None:
    """
    Human-friendly label for powers of ten and near-powers.

    Examples:
    - ``10^8``
    - ``10^8+4``
    - ``10^8-3``
    """
    if n <= 0:
        return None

    p = 1
    k = 0
    while p < n:
        p *= 10
        k += 1
    # Now p >= n and p == 10^k.

    best_k = k
    best_p = p
    if k > 0:
        prev_p = p // 10
        if abs(n - prev_p) <= abs(n - p):
            best_k = k - 1
            best_p = prev_p

    d = n - best_p
    if d == 0:
        return f"10^{best_k}"
    if abs(d) <= near_delta:
        sign = "+" if d > 0 else "-"
        return f"10^{best_k}{sign}{abs(d)}"
    return None


def _signed_from_width(u: int, width: int) -> int:
    low = u & ((1 << width) - 1)
    sign_bit = 1 << (width - 1)
    return low - (1 << width) if (low & sign_bit) else low


def _is_zero_extended(u: int, width: int) -> bool:
    return (u >> width) == 0


def _is_sign_extended(u: int, width: int) -> bool:
    low_mask = (1 << width) - 1
    low = u & low_mask
    sign_bit = 1 << (width - 1)
    if low & sign_bit:
        ext = low | (MOD_256 - (1 << width))
    else:
        ext = low
    return ext == u


def _format_value_plain(v: Value) -> str:
    if v.kind == "bool":
        return "true" if bool(v.data) else "false"
    if v.kind == "int":
        n = int(v.data)
        if -SINGLE_REPR_SMALL_MAX <= n <= SINGLE_REPR_SMALL_MAX:
            return str(n)
        p2 = _pow2_family_label(abs(n)) if n >= 0 else None
        p10 = _pow10_family_label(abs(n)) if n >= 0 else None
        dec = _format_dec_10k(n)
        if abs(n) >= 256:
            s = f"{dec} ({hex(n)})"
            if p2:
                s += f" [{p2}]"
            if p10:
                s += f" [{p10}]"
            return s
        s = dec
        if p2:
            s += f" [{p2}]"
        if p10:
            s += f" [{p10}]"
        return s

    # bv
    u = int(v.data) % MOD_256
    if _is_zero_extended(u, 32) and u <= SINGLE_REPR_SMALL_MAX:
        return str(u)
    p2 = _pow2_family_label(u)
    p10 = _pow10_family_label(u)
    # Small zero-extended values: prefer decimal with hex hint.
    if _is_zero_extended(u, 32):
        s = f"{_format_dec_10k(u)} ({hex(u)})"
        if p2:
            s += f" [{p2}]"
        if p10:
            s += f" [{p10}]"
        return s
    # Typical sign-extended machine-size values: prefer signed decimal.
    for w in (8, 16, 32, 64):
        if _is_sign_extended(u, w):
            s = _signed_from_width(u, w)
            if s < 0:
                if -SINGLE_REPR_SMALL_MAX <= s <= SINGLE_REPR_SMALL_MAX:
                    return str(s)
                out = f"{_format_dec_10k(s)} ({hex(u)})"
                if p2:
                    out += f" [{p2}]"
                if p10:
                    out += f" [{p10}]"
                return out
            break
    out = hex(u)
    if p2:
        out += f" [{p2}]"
    if p10:
        out += f" [{p10}]"
    return out


def _format_value_rich(v: Value) -> Text:
    if v.kind == "bool":
        b = bool(v.data)
        if b:
            return Text("true", style="bold bright_green")
        return Text("false", style="bold bright_red")

    if v.kind == "int":
        n = int(v.data)
        if -SINGLE_REPR_SMALL_MAX <= n <= SINGLE_REPR_SMALL_MAX:
            return Text(str(n), style="bold bright_green")
        p2 = _pow2_family_label(abs(n)) if n >= 0 else None
        p10 = _pow10_family_label(abs(n)) if n >= 0 else None
        t = Text(_format_dec_10k(n), style="bold bright_green")
        if abs(n) >= 256:
            t.append(" ")
            t.append(f"({hex(n)})", style="yellow")
        if p2:
            t.append(" ")
            t.append(f"[{p2}]", style="bold magenta")
        if p10:
            t.append(" ")
            t.append(f"[{p10}]", style="bold bright_blue")
        return t

    # bv
    u = int(v.data) % MOD_256
    if _is_zero_extended(u, 32) and u <= SINGLE_REPR_SMALL_MAX:
        return Text(str(u), style="bold bright_green")
    p2 = _pow2_family_label(u)
    p10 = _pow10_family_label(u)
    if _is_zero_extended(u, 32):
        t = Text(_format_dec_10k(u), style="bold bright_green")
        t.append(" ")
        t.append(f"({hex(u)})", style="yellow")
        if p2:
            t.append(" ")
            t.append(f"[{p2}]", style="bold magenta")
        if p10:
            t.append(" ")
            t.append(f"[{p10}]", style="bold bright_blue")
        return t

    for w in (8, 16, 32, 64):
        if _is_sign_extended(u, w):
            s = _signed_from_width(u, w)
            if s < 0:
                if -SINGLE_REPR_SMALL_MAX <= s <= SINGLE_REPR_SMALL_MAX:
                    return Text(str(s), style="bold bright_red")
                t = Text(_format_dec_10k(s), style="bold bright_red")
                t.append(" ")
                t.append(f"({hex(u)})", style="yellow")
                if p2:
                    t.append(" ")
                    t.append(f"[{p2}]", style="bold magenta")
                if p10:
                    t.append(" ")
                    t.append(f"[{p10}]", style="bold bright_blue")
                return t
            break

    t = Text(hex(u), style="yellow")
    if p2:
        t.append(" ")
        t.append(f"[{p2}]", style="bold magenta")
    if p10:
        t.append(" ")
        t.append(f"[{p10}]", style="bold bright_blue")
    return t


@app.command()
def cfg(
    path: Path = typer.Argument(..., **_PATH_KW),
    plain: bool = typer.Option(False, "--plain", help=_PLAIN_HELP),
    style: Annotated[
        str,
        typer.Option(
            "--style",
            help="goto: block label + goto targets (default). edges: one 'src -> dst' line per edge.",
        ),
    ] = "goto",
    max_blocks: Annotated[
        Optional[int],
        typer.Option(
            "--max-blocks",
            help="List at most this many blocks in file order (default: all).",
        ),
    ] = None,
    check_refs: bool = typer.Option(
        True,
        "--check-refs/--no-check-refs",
        help="Append a warning when some successor id is not a defined block.",
    ),
    to_block: Annotated[
        Optional[str],
        typer.Option(
            "--to",
            metavar="NBID",
            help="Keep only blocks on some path ending here (NBId ∪ ancestors). Combine with --from for 'between'.",
        ),
    ] = None,
    from_block: Annotated[
        Optional[str],
        typer.Option(
            "--from",
            metavar="NBID",
            help="Keep only blocks reachable from here (NBId ∪ descendants). Combine with --to for 'between'.",
        ),
    ] = None,
    only: Annotated[
        Optional[str],
        typer.Option(
            "--only",
            help="Comma-separated NBIds; AND-ed with other structural filters if given.",
        ),
    ] = None,
    id_contains: Annotated[
        Optional[str],
        typer.Option("--id-contains", help="Keep blocks whose id contains this substring."),
    ] = None,
    id_regex: Annotated[
        Optional[str],
        typer.Option("--id-regex", help="Keep blocks whose id matches this Python regex (search)."),
    ] = None,
    cmd_contains: Annotated[
        Optional[str],
        typer.Option(
            "--cmd-contains",
            help="Keep blocks where at least one raw command line contains this substring.",
        ),
    ] = None,
    exclude: Annotated[
        Optional[str],
        typer.Option(
            "--exclude",
            help="Comma-separated NBIds to remove after other filters.",
        ),
    ] = None,
) -> None:
    """Print the control-flow graph structure as text (goto view by default).

    Filters use **intersection** (AND): e.g. ``--to X --id-contains foo`` keeps ancestors of ``X``
    whose ids contain ``foo``. ``--from A --to B`` keeps blocks on some path from ``A`` to ``B``.
    """
    plain = _plain_requested(plain)
    c = _console(plain)
    try:
        tac = parse_path(path)
    except ParseError as e:
        if plain:
            c.print(f"parse error: {e}")
        else:
            c.print(f"[red]parse error:[/red] {e}")
        raise typer.Exit(1) from e

    flt = _build_cfg_filter(
        to_block=to_block,
        from_block=from_block,
        only=only,
        id_contains=id_contains,
        id_regex=id_regex,
        cmd_contains=cmd_contains,
        exclude=exclude,
    )

    cfg_model = Cfg(tac.program)
    try:
        filtered_cfg, warnings = cfg_model.filtered(flt)
    except ValueError as e:
        if plain:
            c.print(f"cfg filter error: {e}")
        else:
            c.print(f"[red]cfg filter error:[/red] {e}")
        raise typer.Exit(2) from e

    if tac.path:
        c.print(f"# path: {tac.path}")
    for w in warnings:
        c.print(f"# {w}")
    if flt.any_active():
        c.print(f"# filter: {len(filtered_cfg.blocks)} of {len(tac.program.blocks)} block(s)")

    st = _normalize_cfg_style(style)
    for line in filtered_cfg.iter_lines(style=st, max_blocks=max_blocks, check_refs=check_refs):
        c.print(line)


@app.command()
def pp(
    path: Path = typer.Argument(..., **_PATH_KW),
    plain: bool = typer.Option(False, "--plain", help=_PLAIN_HELP),
    printer: Annotated[
        str,
        typer.Option(
            "--printer",
            help="Pretty-printer backend name. Built-ins: human (default), raw.",
        ),
    ] = "human",
    strip_var_suffixes: bool = typer.Option(
        True,
        "--strip-var-suffix/--keep-var-suffix",
        help="Strip TAC var meta suffixes like ':1' in printed symbols (default: strip).",
    ),
    max_blocks: Annotated[
        Optional[int],
        typer.Option("--max-blocks", help="List at most this many blocks in file order."),
    ] = None,
    to_block: Annotated[Optional[str], typer.Option("--to", metavar="NBID")] = None,
    from_block: Annotated[Optional[str], typer.Option("--from", metavar="NBID")] = None,
    only: Annotated[Optional[str], typer.Option("--only")] = None,
    id_contains: Annotated[Optional[str], typer.Option("--id-contains")] = None,
    id_regex: Annotated[Optional[str], typer.Option("--id-regex")] = None,
    cmd_contains: Annotated[Optional[str], typer.Option("--cmd-contains")] = None,
    exclude: Annotated[Optional[str], typer.Option("--exclude")] = None,
) -> None:
    """Pretty-print TAC as a goto program, using a selectable printer backend."""
    plain = _plain_requested(plain)
    c = _console(plain)
    try:
        tac = parse_path(path)
    except ParseError as e:
        if plain:
            c.print(f"parse error: {e}")
        else:
            c.print(f"[red]parse error:[/red] {e}")
        raise typer.Exit(1) from e

    flt = _build_cfg_filter(
        to_block=to_block,
        from_block=from_block,
        only=only,
        id_contains=id_contains,
        id_regex=id_regex,
        cmd_contains=cmd_contains,
        exclude=exclude,
    )
    try:
        filtered_cfg, warnings = Cfg(tac.program).filtered(flt)
    except ValueError as e:
        if plain:
            c.print(f"pp filter error: {e}")
        else:
            c.print(f"[red]pp filter error:[/red] {e}")
        raise typer.Exit(2) from e

    printer_name = _normalize_printer_name(printer)
    pp_backend = configured_printer(
        printer_name,
        strip_var_suffixes=strip_var_suffixes,
    )

    if tac.path:
        c.print(f"# path: {tac.path}")
    c.print(f"# printer: {printer_name}")
    for w in warnings:
        c.print(f"# {w}")
    if flt.any_active():
        c.print(f"# filter: {len(filtered_cfg.blocks)} of {len(tac.program.blocks)} block(s)")

    shown = 0
    for b in filtered_cfg.ordered_blocks():
        if max_blocks is not None and shown >= max_blocks:
            rest = len(filtered_cfg.blocks) - shown
            c.print(f"# ... truncated: {rest} more block(s) not listed (--max-blocks {max_blocks})")
            break
        c.print(highlight_tac_line(f"{b.id}:"))
        for cmd_line in pretty_lines(b.commands, printer=pp_backend):
            c.print(highlight_tac_line(f"  {cmd_line}"))
        if b.successors:
            c.print(highlight_tac_line(f"  goto {', '.join(b.successors)}"))
        else:
            c.print(highlight_tac_line("  stop"))
        c.print("")
        shown += 1


@app.command()
def run(
    path: Path = typer.Argument(..., **_PATH_KW),
    plain: bool = typer.Option(False, "--plain", help=_PLAIN_HELP),
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
    model: Annotated[
        Optional[Path],
        typer.Option(
            "--model",
            help="Path to a report/model file containing a 'TAC model begin/end' section.",
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
    """Execute TAC with a concrete interpreter (assume-fail stops, assert-fail continues)."""
    plain = _plain_requested(plain)
    c = _console(plain)
    try:
        tac = parse_path(path)
    except ParseError as e:
        if plain:
            c.print(f"parse error: {e}")
        else:
            c.print(f"[red]parse error:[/red] {e}")
        raise typer.Exit(1) from e

    hm = havoc_mode.strip().lower()
    if hm not in ("zero", "random", "ask"):
        raise typer.BadParameter("use one of: zero, random, ask", param_hint="--havoc-mode")
    if validate and model is None:
        raise typer.BadParameter("--validate requires --model", param_hint="--validate")
    if fallback is not None and model is None:
        raise typer.BadParameter("--fallback requires --model", param_hint="--fallback")

    printer_name = _normalize_printer_name(printer)
    pp_backend = configured_printer(printer_name, strip_var_suffixes=strip_var_suffixes)
    model_values: dict[str, Value] = {}
    model_warnings: list[str] = []
    fallback_model_values: dict[str, Value] = {}
    fallback_model_warnings: list[str] = []
    if model is not None:
        try:
            model_res = parse_tac_model_path(model)
        except OSError as e:
            c.print(f"[red]model read error:[/red] {e}" if not plain else f"model read error: {e}")
            raise typer.Exit(1) from e
        except ValueError as e:
            c.print(f"[red]model parse error:[/red] {e}" if not plain else f"model parse error: {e}")
            raise typer.Exit(1) from e
        model_values = model_res.values
        model_warnings = model_res.warnings
    if fallback is not None:
        try:
            fb_res = parse_tac_model_path(fallback)
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
                return _parse_user_value(raw, kind)
            except ValueError as e:
                c.print(f"[red]{e}[/red]" if not plain else str(e))

    def _model_lookup(values: dict[str, Value], symbol: str) -> Value | None:
        if symbol in values:
            return values[symbol]
        stripped = _strip_meta_suffix(symbol)
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
            return _coerce_value_kind(mv, kind)
        fb = _model_lookup(fallback_model_values, symbol)
        if fb is not None:
            model_havoc_fallback_hits += 1
            return _coerce_value_kind(fb, kind)
        model_havoc_sentinel_fallback += 1
        return _model_fallback_value(kind)

    ask_cb = _ask if hm == "ask" else None
    run_havoc_mode = hm
    if model is not None:
        # With a model, prefer model values for havoc and use sentinel values on misses.
        ask_cb = _ask_or_model
        run_havoc_mode = "ask"

    rcfg = RunConfig(
        entry_block=entry,
        max_steps=max_steps,
        havoc_mode=run_havoc_mode,  # type: ignore[arg-type]
        ask_value=ask_cb,
        strip_var_suffixes=strip_var_suffixes,
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
            expected_cast = _coerce_value_kind(expected, ev.value.kind)
            ev.expected = expected_cast
            if not _values_equal(ev.value, expected_cast):
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
    c.print(f"# mode: run (havoc={run_havoc_mode}, max_steps={max_steps})")
    if model is not None:
        c.print(f"# model: {model}")
        c.print(f"# model values: {len(model_values)}")
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
            src_prefix = _source_prefix_for_cmd(ev.cmd, tac.metas)
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
                # Keep plain mode grep-friendly and deterministic.
                if ev.value is not None:
                    suffix = ""
                    if ev.mismatch and ev.expected is not None:
                        suffix = f"    !! expected {_format_value_plain(ev.expected)}"
                    c.print(f"  {ev.rendered}    {_format_value_plain(ev.value)}{suffix}")
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
                right = _format_value_rich(ev.value)
                if ev.mismatch and ev.expected is not None:
                    right.append("  ")
                    right.append("!= expected ", style="bold red")
                    right.append(_format_value_plain(ev.expected), style="bold red")
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


def main() -> None:
    app()


if __name__ == "__main__":
    main()
