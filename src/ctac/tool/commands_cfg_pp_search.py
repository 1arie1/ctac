from __future__ import annotations

import re
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
    console,
    plain_requested,
)
from ctac.tool.input_resolution import resolve_tac_input_path, resolve_user_path


def normalize_cfg_style(raw: str) -> CfgStyle:
    s = raw.strip().lower()
    if s in ("goto", "edges", "dot"):
        return s  # type: ignore[return-value]
    raise typer.BadParameter("use 'goto', 'edges', or 'dot'", param_hint="--style")


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

    printer_name = normalize_printer_name(printer)
    pp_backend = configured_printer(
        printer_name,
        strip_var_suffixes=strip_var_suffixes,
        human_patterns=human,
    )
    matches = search_matcher(pattern=pattern, regex=regex, case_sensitive=case_sensitive)

    if tac.path:
        c.print(f"# path: {tac.path}")
    for w in (user_warnings + input_warnings):
        c.print(f"# input warning: {w}")
    c.print(f"# printer: {printer_name}")
    c.print(f"# mode: {'regex' if regex else 'literal'}")
    c.print(f"# case_sensitive: {case_sensitive}")
    c.print(f"# pattern: {pattern!r}")
    for w in warnings:
        c.print(f"# {w}")
    if flt.any_active():
        c.print(f"# filter: {len(filtered_cfg.blocks)} of {len(tac.program.blocks)} block(s)")

    total = 0
    blocks_hit: set[str] = set()
    for b in filtered_cfg.ordered_blocks():
        for idx, cmd in enumerate(b.commands):
            line = pp_backend.print_cmd(cmd)
            if line is None or line == "":
                continue
            if not matches(line):
                continue
            total += 1
            blocks_hit.add(b.id)

            if total > max_matches:
                break
            if count_only:
                continue
            if blocks_only:
                continue
            c.print(f"{b.id}:{idx}: [{type(cmd).__name__}] {line}")
        if total > max_matches:
            break

    shown_total = min(total, max_matches)
    if blocks_only and not count_only:
        for bid in sorted(blocks_hit):
            c.print(bid)

    c.print(f"matches: {shown_total}")
    c.print(f"blocks_with_matches: {len(blocks_hit)}")
    if total > max_matches:
        c.print(f"# truncated after {max_matches} matches; raise --max-matches to see more")


_CFG_EPILOG = (
    "[bold green]Styles[/bold green]  [cyan]goto[/cyan] (block labels + goto "
    "targets, default), [cyan]edges[/cyan] (one [cyan]src -> dst[/cyan] line "
    "per edge, grep-friendly), [cyan]dot[/cyan] (Graphviz digraph; pipe to "
    "[cyan]dot -Tpng[/cyan] for a picture).\n\n"
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
    "[cyan]ctac cfg f.tac --plain --style dot | dot -Tpng -o cfg.png[/cyan]"
    "  [dim]# render CFG[/dim]"
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
                "dot: Graphviz digraph (block id labels; asserts red, clog pastel, source tooltips)."
            ),
            autocompletion=complete_choices(["goto", "edges", "dot"]),
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
    "[bold green]Examples[/bold green]\n\n"
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
    pattern: str = typer.Argument(..., help="Pattern to search in rendered command lines."),
    plain: bool = typer.Option(False, "--plain", help=PLAIN_HELP),
    agent: bool = agent_option(),
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
        min=1,
        help="Maximum number of matches to print/count before truncation.",
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
    run_search(
        path=path,
        pattern=pattern,
        plain=plain,
        printer=printer,
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
