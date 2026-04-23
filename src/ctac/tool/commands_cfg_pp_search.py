from __future__ import annotations

import re
import sys
from collections import Counter, deque
from pathlib import Path
from typing import Annotated, Optional

import typer

from ctac.ast.pretty import DEFAULT_PRINTERS, configured_printer, pretty_lines
from ctac.ast.run_format import pp_terminator_line
from ctac.eval import Value
from ctac.graph import Cfg, CfgFilter, CfgStyle
from ctac.parse import ParseError, parse_path
from ctac.tool.cli_runtime import (
    FILTER_CMD_CONTAINS_HELP,
    FILTER_EXCLUDE_HELP,
    FILTER_FROM_HELP,
    FILTER_ID_CONTAINS_HELP,
    FILTER_ID_REGEX_HELP,
    FILTER_ONLY_HELP,
    FILTER_TO_HELP,
    INSPECT_PANEL,
    PLAIN_HELP,
    agent_option,
    app,
    complete_choices,
    complete_search_tokens,
    console,
    plain_requested,
)
from ctac.tool.input_resolution import resolve_tac_input_path, resolve_user_path


def normalize_cfg_style(raw: str) -> CfgStyle:
    s = raw.strip().lower()
    if s in ("goto", "edges", "dot", "blocks"):
        return s  # type: ignore[return-value]
    raise typer.BadParameter(
        "use 'goto', 'edges', 'dot', or 'blocks'", param_hint="--style"
    )


def normalize_printer_name(raw: str) -> str:
    name = raw.strip().lower()
    if name in DEFAULT_PRINTERS.names():
        return name
    raise typer.BadParameter(
        f"unknown printer {raw!r}; choose one of: {', '.join(DEFAULT_PRINTERS.names())}",
        param_hint="--printer",
    )


def build_cfg_filter(
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


def parse_user_value(text: str, kind: str) -> Value:
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


def search_matcher(
    *,
    pattern: str,
    regex: bool,
    case_sensitive: bool,
):
    if regex:
        flags = 0 if case_sensitive else re.IGNORECASE
        try:
            rx = re.compile(pattern, flags=flags)
        except re.error as e:
            raise typer.BadParameter(f"invalid --pattern regex: {e}", param_hint="pattern") from e
        return lambda text: rx.search(text) is not None

    needle = pattern if case_sensitive else pattern.casefold()

    def _match_literal(text: str) -> bool:
        hay = text if case_sensitive else text.casefold()
        return needle in hay

    return _match_literal


def search_match_iter(
    *,
    pattern: str,
    regex: bool,
    case_sensitive: bool,
):
    """Return ``text -> list[str]`` yielding a tally key per match.

    For regex patterns with a capture group, the first captured group is
    used (so ``BWAnd\\(R\\d+ (0x[0-9a-f]+)`` tallies mask constants).
    Otherwise the whole matched substring is used (``grep -o`` style).
    Literal patterns tally the pattern string once per substring hit.
    """
    if regex:
        flags = 0 if case_sensitive else re.IGNORECASE
        try:
            rx = re.compile(pattern, flags=flags)
        except re.error as e:
            raise typer.BadParameter(
                f"invalid --pattern regex: {e}", param_hint="pattern"
            ) from e

        def _iter_regex(text: str) -> list[str]:
            out: list[str] = []
            for m in rx.finditer(text):
                if m.groups():
                    g1 = m.group(1)
                    out.append(g1 if g1 is not None else m.group(0))
                else:
                    out.append(m.group(0))
            return out

        return _iter_regex

    needle = pattern if case_sensitive else pattern.casefold()

    def _iter_literal(text: str) -> list[str]:
        hay = text if case_sensitive else text.casefold()
        # Count non-overlapping occurrences of the literal.
        n = hay.count(needle)
        return [pattern] * n

    return _iter_literal


def run_search(
    *,
    path: Path | None,
    pattern: str,
    plain: bool,
    printer: str,
    strip_var_suffixes: bool,
    human: bool,
    regex: bool,
    case_sensitive: bool,
    max_matches: int,
    count_only: bool,
    blocks_only: bool,
    before: int | None = None,
    after: int | None = None,
    context: int = 0,
    count_by_match: bool = False,
    quiet: bool = False,
    to_block: str | None,
    from_block: str | None,
    only: str | None,
    id_contains: str | None,
    id_regex: str | None,
    cmd_contains: str | None,
    exclude: str | None,
    weak_is_strong: bool,
) -> None:
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

    flt = build_cfg_filter(
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
            c.print(f"search filter error: {e}")
        else:
            c.print(f"[red]search filter error:[/red] {e}")
        raise typer.Exit(2) from e

    # `--max-matches 0` means unlimited; compile to sys.maxsize so the
    # existing `total > max_matches` / `min(total, max_matches)` checks
    # keep working without a special case at each call site.
    if max_matches == 0:
        max_matches = sys.maxsize
    printer_name = normalize_printer_name(printer)
    pp_backend = configured_printer(
        printer_name,
        strip_var_suffixes=strip_var_suffixes,
        human_patterns=human,
    )
    matches = search_matcher(pattern=pattern, regex=regex, case_sensitive=case_sensitive)
    match_iter = (
        search_match_iter(pattern=pattern, regex=regex, case_sensitive=case_sensitive)
        if count_by_match
        else None
    )

    def _comment(text: str) -> None:
        """Print a ``#``-prefixed line unless --quiet is set."""
        if quiet:
            return
        c.print(f"# {text}")

    if tac.path:
        _comment(f"path: {tac.path}")
    for w in (user_warnings + input_warnings):
        _comment(f"input warning: {w}")
    _comment(f"printer: {printer_name}")
    _comment(f"mode: {'regex' if regex else 'literal'}")
    _comment(f"case_sensitive: {case_sensitive}")
    _comment(f"pattern: {pattern!r}")
    for w in warnings:
        _comment(w)
    if flt.any_active():
        _comment(f"filter: {len(filtered_cfg.blocks)} of {len(tac.program.blocks)} block(s)")

    # Resolve grep-style context flags. Explicit --before/--after (including
    # 0) win over --context; None means "fall back to --context".
    eff_before = before if before is not None else context
    eff_after = after if after is not None else context
    want_context = (eff_before > 0 or eff_after > 0) and not (count_only or blocks_only)

    def _fmt_match(bid: str, i: int, cmd, text: str) -> str:
        return f"{bid}:{i}: [{type(cmd).__name__}] {text}"

    def _fmt_ctx(bid: str, i: int, cmd, text: str) -> str:
        # grep convention: `-` separator for context rows.
        return f"{bid}:{i}- [{type(cmd).__name__}] {text}"

    total = 0
    blocks_hit: set[str] = set()
    counter: Counter[str] = Counter()
    for b in filtered_cfg.ordered_blocks():
        # Ring buffer of the last eff_before non-empty commands (for the
        # "before" view of the next match). Reset per block so context
        # never crosses block boundaries.
        before_buf: deque[tuple[int, object, str]] = deque(maxlen=max(eff_before, 1))
        last_emitted_idx = -1  # highest cmd index we've printed in this block
        after_remaining = 0    # countdown of trailing-context rows owed
        for idx, cmd in enumerate(b.commands):
            line = pp_backend.print_cmd(cmd)
            if line is None or line == "":
                continue
            if matches(line):
                total += 1
                blocks_hit.add(b.id)
                if count_by_match and match_iter is not None:
                    for key in match_iter(line):
                        counter[key] += 1

                if total > max_matches:
                    break
                if count_only or blocks_only or count_by_match:
                    continue

                # Gap separator: if there was printed content in this block
                # earlier but the upcoming rows don't touch it, emit `--`
                # like grep does between non-adjacent hit groups.
                if want_context and last_emitted_idx >= 0:
                    first_print_idx = (
                        before_buf[0][0] if (eff_before > 0 and before_buf) else idx
                    )
                    if first_print_idx > last_emitted_idx + 1:
                        c.print("--")

                # Flush before-context; skip rows already emitted as
                # after-context for the previous match.
                if eff_before > 0:
                    for bidx, bcmd, bline in before_buf:
                        if bidx > last_emitted_idx:
                            c.print(_fmt_ctx(b.id, bidx, bcmd, bline))
                            last_emitted_idx = bidx
                    before_buf.clear()

                c.print(_fmt_match(b.id, idx, cmd, line))
                last_emitted_idx = idx
                after_remaining = eff_after
            else:
                # Trailing-context emission for the previous match.
                if after_remaining > 0 and not (count_only or blocks_only):
                    c.print(_fmt_ctx(b.id, idx, cmd, line))
                    last_emitted_idx = idx
                    after_remaining -= 1
                if eff_before > 0:
                    before_buf.append((idx, cmd, line))
        if total > max_matches:
            break

    shown_total = min(total, max_matches)
    if count_by_match:
        _comment("count-by-match:")
        # Sort by count desc, then lexicographically asc.
        for key, cnt in sorted(counter.items(), key=lambda kv: (-kv[1], kv[0])):
            c.print(f"{cnt:>6}  {key}")
        _comment(f"total: {sum(counter.values())} across {len(blocks_hit)} block(s)")
        if total > max_matches:
            _comment(
                f"truncated after {max_matches} matches; raise --max-matches to see more"
            )
        return

    if blocks_only and not count_only:
        for bid in sorted(blocks_hit):
            c.print(bid)

    c.print(f"matches: {shown_total}")
    c.print(f"blocks_with_matches: {len(blocks_hit)}")
    if total > max_matches:
        _comment(
            f"truncated after {max_matches} matches; raise --max-matches to see more"
        )


_CFG_EPILOG = (
    "[bold green]Styles[/bold green]  [cyan]goto[/cyan] (block labels + goto "
    "targets, default), [cyan]edges[/cyan] (one [cyan]src -> dst[/cyan] line "
    "per edge, grep-friendly), [cyan]dot[/cyan] (Graphviz digraph; pipe to "
    "[cyan]dot -Tsvg[/cyan] for a picture), [cyan]blocks[/cyan] (one block "
    "id per line, no preamble — clean for shell loops).\n\n"
    "[bold green]Filters[/bold green]  Combine with AND. "
    "[cyan]--from A --to B[/cyan] keeps blocks on some path from A to B. "
    "[cyan]--id-contains[/cyan] / [cyan]--id-regex[/cyan] / "
    "[cyan]--cmd-contains[/cyan] / [cyan]--only[/cyan] / "
    "[cyan]--exclude[/cyan] all compose with that.\n\n"
    "[bold green]Examples[/bold green]\n\n"
    "[cyan]ctac cfg f.tac --plain[/cyan]\n\n"
    "[cyan]ctac cfg f.tac --plain --style edges --from entry --to 42_0_0[/cyan]"
    "  [dim]# slice on a CFG path[/dim]\n\n"
    "[cyan]ctac cfg f.tac --plain --id-regex '^assert_'[/cyan]"
    "  [dim]# blocks by id pattern[/dim]\n\n"
    "[cyan]ctac cfg f.tac --plain --style dot | dot -Tsvg -o cfg.svg[/cyan]"
    "  [dim]# render CFG[/dim]\n\n"
    "[cyan]for b in $(ctac cfg f.tac --plain --style blocks); do "
    "ctac search f.tac BWAnd --plain -q --only $b; done[/cyan]"
    "  [dim]# shell-loop over blocks[/dim]"
)


@app.command(rich_help_panel=INSPECT_PANEL, epilog=_CFG_EPILOG)
def cfg(
    path: Optional[Path] = typer.Argument(
        None, help="Path to .tac / .sbf.json file, or a Certora output directory."
    ),
    plain: bool = typer.Option(False, "--plain", help=PLAIN_HELP),
    agent: bool = agent_option(),
    style: Annotated[
        str,
        typer.Option(
            "--style",
            help=(
                "goto: block label + goto targets (default). edges: one 'src -> dst' line per edge. "
                "dot: Graphviz digraph (block id labels; asserts red, clog pastel, source tooltips). "
                "blocks: one block id per line, nothing else — clean for shell loops."
            ),
            autocompletion=complete_choices(["goto", "edges", "dot", "blocks"]),
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
    weak_is_strong: bool = typer.Option(
        False,
        "--weak-is-strong",
        help="Parse snippet weak refs as strong refs (annotations use strong deref).",
    ),
) -> None:
    """Print the CFG as text (goto / edges / dot)."""
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

    flt = build_cfg_filter(
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

    st = normalize_cfg_style(style)
    _pfx = "//" if st == "dot" else "#"
    # `blocks` style is purpose-built for shell-loop consumption: one
    # block id per line, nothing else. Skip the preamble entirely so
    # `for b in $(ctac cfg f.tac --plain --style blocks); ...` gets
    # pure ids rather than mixing header comments with ids.
    if st != "blocks":
        if tac.path:
            if st == "dot":
                c.print(f"{_pfx} path: {tac.path}", markup=False)
            else:
                c.print(f"{_pfx} path: {tac.path}")
        for w in (user_warnings + input_warnings):
            if st == "dot":
                c.print(f"{_pfx} input warning: {w}", markup=False)
            else:
                c.print(f"{_pfx} input warning: {w}")
        for w in warnings:
            if st == "dot":
                c.print(f"{_pfx} {w}", markup=False)
            else:
                c.print(f"{_pfx} {w}")
        if flt.any_active():
            msg = f"{_pfx} filter: {len(filtered_cfg.blocks)} of {len(tac.program.blocks)} block(s)"
            if st == "dot":
                c.print(msg, markup=False)
            else:
                c.print(msg)

    if st == "dot":
        for line in filtered_cfg.iter_dot(tac.metas, max_blocks=max_blocks, check_refs=check_refs):
            c.print(line, markup=False)
    else:
        for line in filtered_cfg.iter_lines(style=st, max_blocks=max_blocks, check_refs=check_refs):
            c.print(line)


_PP_EPILOG = (
    "[bold green]What it does[/bold green]  Default [cyan]human[/cyan] printer "
    "rewrites bit-field ops into slice notation (e.g. "
    "[cyan]Mul(Mod(Div(X 0x400) 0x100) 0x400)[/cyan] becomes "
    "[cyan]X[10..17][/cyan]), normalizes shifted masks, and collapses common "
    "idioms. [cyan]--printer raw[/cyan] disables the rewrites.\n\n"
    "Accepts the same filters as [cyan]ctac cfg[/cyan] "
    "([cyan]--from/--to/--only/--id-contains/--id-regex/--cmd-contains/--exclude[/cyan]), "
    "all combining with AND. Output goes to stdout unless [cyan]-o[/cyan] is given.\n\n"
    "[bold green]Examples[/bold green]\n\n"
    "[cyan]ctac pp f.tac --plain[/cyan]\n\n"
    "[cyan]ctac pp f.tac --plain --from A --to B[/cyan]"
    "  [dim]# slice on a CFG path[/dim]\n\n"
    "[cyan]ctac pp f.tac --plain --cmd-contains 'Select(M16'[/cyan]"
    "  [dim]# pin bytemap reads[/dim]\n\n"
    "[cyan]ctac pp f.tac -o f.htac[/cyan]"
    "  [dim]# write pretty-printed text[/dim]"
)


@app.command(rich_help_panel=INSPECT_PANEL, epilog=_PP_EPILOG)
def pp(
    path: Optional[Path] = typer.Argument(
        None, help="Path to .tac / .sbf.json file, or a Certora output directory."
    ),
    plain: bool = typer.Option(False, "--plain", help=PLAIN_HELP),
    agent: bool = agent_option(),
    output_path: Annotated[
        Optional[Path],
        typer.Option(
            "-o",
            "--output",
            help="Write pretty-printed output to this file (plain text) instead of stdout.",
        ),
    ] = None,
    printer: Annotated[
        str,
        typer.Option(
            "--printer",
            help="Pretty-printer backend name. Built-ins: human (default), raw.",
            autocompletion=complete_choices(["human", "raw"]),
        ),
    ] = "human",
    strip_var_suffixes: bool = typer.Option(
        True,
        "--strip-var-suffix/--keep-var-suffix",
        help="Strip TAC var meta suffixes like ':1' in printed symbols (default: strip).",
    ),
    human: bool = typer.Option(
        True,
        "--human/--no-human",
        help="Enable human-oriented pattern rewrites in pretty output (default: on).",
    ),
    max_blocks: Annotated[
        Optional[int],
        typer.Option("--max-blocks", help="List at most this many blocks in file order."),
    ] = None,
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
    weak_is_strong: bool = typer.Option(
        False,
        "--weak-is-strong",
        help="Parse snippet weak refs as strong refs (annotations use strong deref).",
    ),
) -> None:
    """Pretty-print TAC as a goto program with humanized expressions."""
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

    flt = build_cfg_filter(
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

    printer_name = normalize_printer_name(printer)
    pp_backend = configured_printer(
        printer_name,
        strip_var_suffixes=strip_var_suffixes,
        human_patterns=human,
    )

    from ctac.ast.highlight import highlight_tac_line

    # When writing to a file, accumulate plain-text lines; otherwise stream
    # highlighted output through the console.
    to_file = output_path is not None
    file_lines: list[str] = []

    def _emit(text: str, *, highlight: bool = False) -> None:
        if to_file:
            file_lines.append(text)
        elif highlight:
            c.print(highlight_tac_line(text))
        else:
            c.print(text)

    if tac.path:
        _emit(f"# path: {tac.path}")
    for w in (user_warnings + input_warnings):
        _emit(f"# input warning: {w}")
    _emit(f"# printer: {printer_name}")
    for w in warnings:
        _emit(f"# {w}")
    if flt.any_active():
        _emit(f"# filter: {len(filtered_cfg.blocks)} of {len(tac.program.blocks)} block(s)")

    shown = 0
    for b in filtered_cfg.ordered_blocks():
        if max_blocks is not None and shown >= max_blocks:
            rest = len(filtered_cfg.blocks) - shown
            _emit(f"# ... truncated: {rest} more block(s) not listed (--max-blocks {max_blocks})")
            break
        _emit(f"{b.id}:", highlight=True)
        for cmd_line in pretty_lines(b.commands, printer=pp_backend):
            _emit(f"  {cmd_line}", highlight=True)
        term_line = pp_terminator_line(b, strip_var_suffixes=strip_var_suffixes)
        if term_line is not None:
            _emit(f"  {term_line}", highlight=True)
        elif b.successors:
            _emit(f"  goto {', '.join(b.successors)}", highlight=True)
        else:
            _emit("  stop", highlight=True)
        _emit("")
        shown += 1

    if to_file:
        assert output_path is not None
        output_path.write_text("\n".join(file_lines) + ("\n" if file_lines else ""), encoding="utf-8")
        if plain:
            c.print(f"# wrote {output_path}", markup=False)
        else:
            c.print(f"[cyan]wrote[/cyan]: [bold]{output_path}[/bold]")


_SEARCH_EPILOG = (
    "[bold green]What it does[/bold green]  Pattern search inside parsed TAC "
    "commands (regex by default; [cyan]--literal[/cyan] for substring). "
    "Matches are anchored to a single command (no cross-command false "
    "positives) and respect block structure. Accepts the same "
    "[cyan]--from/--to/--only/...[/cyan] filters as [cyan]ctac pp[/cyan] / "
    "[cyan]ctac cfg[/cyan], combined with AND.\n\n"
    "Aliased as [cyan]ctac grep[/cyan] for muscle memory.\n\n"
    "[bold green]Printer choice[/bold green]  Default [cyan]--printer auto[/cyan] "
    "resolves to [cyan]raw[/cyan] under [cyan]--plain[/cyan] (so TAC operator "
    "names — [cyan]BWAnd[/cyan], [cyan]Mod[/cyan], [cyan]Select[/cyan], "
    "[cyan]safe_math_narrow_bv256:bif[/cyan], ... — match as typed) and to "
    "[cyan]human[/cyan] in interactive mode (humanized slice/mod syntax is "
    "easier to read). Pass [cyan]--printer human[/cyan] explicitly to force "
    "humanization even under [cyan]--plain[/cyan].\n\n"
    "[bold green]Shell quoting[/bold green]  Single-quote regex patterns to "
    "pass metacharacters through the shell without escaping. "
    "[cyan]'Mod\\(|BWAnd'[/cyan] matches either op; the [cyan]|[/cyan] stays "
    "an alternation rather than a shell pipe, and [cyan]\\([/cyan] escapes "
    "the literal paren for the regex engine.\n\n"
    "[bold green]Examples[/bold green]\n\n"
    "[cyan]ctac search f.tac 'BWAnd' --plain --count[/cyan]"
    "  [dim]# count BWAnd ops — raw form via auto[/dim]\n\n"
    "[cyan]ctac search f.tac 'Mod\\(|BWAnd' --plain --count[/cyan]"
    "  [dim]# alternation, single-quoted[/dim]\n\n"
    "[cyan]ctac search f.tac 'BWAnd' --plain -C 2[/cyan]"
    "  [dim]# 2 commands of context on each side[/dim]\n\n"
    "[cyan]ctac search f.tac '0x[0-9a-f]+' --plain --count-by-match[/cyan]"
    "  [dim]# hex constants by frequency[/dim]\n\n"
    "[cyan]ctac search f.tac 'BWAnd' --plain --count -q[/cyan]"
    "  [dim]# pipeable; awk '/^matches:/ {print $2}'[/dim]\n\n"
    "[cyan]ctac search f.tac 'assume.*\\[2\\^64' --plain --count[/cyan]"
    "  [dim]# count range guards[/dim]\n\n"
    "[cyan]ctac search f.tac Eq --plain --literal[/cyan]"
    "  [dim]# substring[/dim]\n\n"
    "[cyan]ctac search f.tac 'if \\(R[0-9]+\\) < \\1' --plain[/cyan]"
    "  [dim]# self-compare[/dim]\n\n"
    "[cyan]ctac search f.tac 'Select\\(M16' --plain --blocks-only[/cyan]"
    "  [dim]# blocks-only[/dim]\n\n"
    "[cyan]ctac grep f.tac havoc --plain --literal[/cyan]"
    "  [dim]# alias[/dim]"
)


@app.command("grep", rich_help_panel=INSPECT_PANEL, epilog=_SEARCH_EPILOG)
@app.command("search", rich_help_panel=INSPECT_PANEL, epilog=_SEARCH_EPILOG)
def search_cmd(
    path: Optional[Path] = typer.Argument(
        None, help="Path to .tac / .sbf.json file, or a Certora output directory."
    ),
    pattern: str = typer.Argument(
        ...,
        help="Pattern to search in rendered command lines.",
        autocompletion=complete_search_tokens(),
    ),
    plain: bool = typer.Option(False, "--plain", help=PLAIN_HELP),
    agent: bool = agent_option(),
    printer: Annotated[
        str,
        typer.Option(
            "--printer",
            help=(
                "Pretty-printer backend: auto (default — raw under --plain, human "
                "otherwise), human, or raw. Use raw to match on TAC operator "
                "names (BWAnd, Mod, Select, safe_math_narrow_bv256:bif, ...) — "
                "the human printer rewrites those into slice/mod syntax and "
                "hides them from pattern matching."
            ),
            autocompletion=complete_choices(["auto", "human", "raw"]),
        ),
    ] = "auto",
    strip_var_suffixes: bool = typer.Option(
        True,
        "--strip-var-suffix/--keep-var-suffix",
        help="Strip TAC var meta suffixes like ':1' in printed symbols (default: strip).",
    ),
    human: bool = typer.Option(
        True,
        "--human/--no-human",
        help="Enable human-oriented pattern rewrites in printed command lines (default: on).",
    ),
    regex: bool = typer.Option(
        True,
        "--regex/--literal",
        help="Interpret PATTERN as regex (default) or plain substring.",
    ),
    case_sensitive: bool = typer.Option(
        True,
        "--case-sensitive/--ignore-case",
        help="Case-sensitive matching (default) or case-insensitive.",
    ),
    max_matches: int = typer.Option(
        200,
        "--max-matches",
        min=0,
        help=(
            "Maximum number of matches to print/count before truncation. "
            "Use 0 for unlimited."
        ),
    ),
    count_only: bool = typer.Option(
        False,
        "--count",
        help="Print only total matches and blocks_with_matches.",
    ),
    blocks_only: bool = typer.Option(
        False,
        "--blocks-only",
        help="Print only block ids that contain at least one match.",
    ),
    count_by_match: bool = typer.Option(
        False,
        "--count-by-match",
        help=(
            "Tally distinct match values and print a frequency table "
            "(desc by count, then alphabetic). If the pattern has a "
            "capture group, the first group is used as the tally key; "
            "otherwise the whole match is used. Mutually exclusive with "
            "--count and --blocks-only."
        ),
    ),
    quiet: bool = typer.Option(
        False,
        "-q",
        "--quiet",
        help=(
            "Suppress the `#`-prefixed preamble and footer so the output "
            "is just numeric results / tally rows / block ids. Pair with "
            "--count for a two-line result that `awk` can parse directly."
        ),
    ),
    before: Optional[int] = typer.Option(
        None,
        "-B",
        "--before",
        min=0,
        help=(
            "Print N commands before each match within the same block "
            "(0 silences that side; default follows --context). Context "
            "never crosses block boundaries."
        ),
    ),
    after: Optional[int] = typer.Option(
        None,
        "-A",
        "--after",
        min=0,
        help=(
            "Print N commands after each match within the same block "
            "(0 silences that side; default follows --context)."
        ),
    ),
    context: int = typer.Option(
        0,
        "-C",
        "--context",
        min=0,
        help=(
            "Shorthand for --before N --after N. Explicit --before / --after "
            "override this on their side, even when set to 0."
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
    weak_is_strong: bool = typer.Option(
        False,
        "--weak-is-strong",
        help="Parse snippet weak refs as strong refs (annotations use strong deref).",
    ),
) -> None:
    """Regex / literal search over TAC commands (alias: `grep`)."""
    _ = agent
    if count_by_match and (count_only or blocks_only):
        raise typer.BadParameter(
            "--count-by-match is mutually exclusive with --count and --blocks-only",
            param_hint="--count-by-match",
        )
    # "auto" resolves to raw under --plain (agents / scripts want operator
    # names to match) and human otherwise (humans want readable expressions).
    # Explicit "--printer human"/"--printer raw" still wins.
    resolved_printer = printer
    if printer == "auto":
        resolved_printer = "raw" if plain_requested(plain) else "human"
    run_search(
        path=path,
        pattern=pattern,
        plain=plain,
        printer=resolved_printer,
        before=before,
        after=after,
        context=context,
        count_by_match=count_by_match,
        quiet=quiet,
        strip_var_suffixes=strip_var_suffixes,
        human=human,
        regex=regex,
        case_sensitive=case_sensitive,
        max_matches=max_matches,
        count_only=count_only,
        blocks_only=blocks_only,
        to_block=to_block,
        from_block=from_block,
        only=only,
        id_contains=id_contains,
        id_regex=id_regex,
        cmd_contains=cmd_contains,
        exclude=exclude,
        weak_is_strong=weak_is_strong,
    )
