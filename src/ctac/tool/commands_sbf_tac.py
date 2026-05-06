from __future__ import annotations

import re
from pathlib import Path
from typing import Annotated, Optional

import typer
from rich.table import Table
from rich.text import Text

from ctac.ast.highlight import highlight_tac_line
from ctac.ast.pretty import configured_printer
from ctac.ast.run_format import bytecode_addr_for_cmd
from ctac.graph import Cfg
from ctac.parse import ParseError, parse_path
from ctac.tool.cli_runtime import (
    COMPARE_PANEL,
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
from ctac.tool.commands_cfg_pp_search import (
    build_cfg_filter,
    normalize_printer_name,
    parse_address_range,
)
from ctac.tool.input_resolution import resolve_tac_input_path
from ctac.tool.project_io import ingest_or_write_text


_SBF_TAC_EPILOG = (
    "[bold green]What it does[/bold green]  Joins each SBF instruction with "
    "the TAC commands that share its bytecode address (metadata key "
    "[cyan]sbf_bytecode_address[/cyan] in [cyan].sbf.json[/cyan]; "
    "[cyan]sbf.bytecode.address[/cyan] in [cyan].tac[/cyan] dumps). One "
    "SBF instruction typically lowers to several TAC commands; the join "
    "view makes the lowering visible at a glance.\n\n"
    "[bold green]Output[/bold green]  Three columns: address, SBF "
    "instruction, TAC command. The first row of each address group "
    "carries the SBF instruction; continuation rows leave the SBF "
    "column blank, one per matching TAC command. TAC cmds without an "
    "[cyan]sbf_bytecode_address[/cyan] are not shown — many are "
    "synthesized (constants, register init, annotations) and would "
    "just add noise.\n\n"
    "[bold green]Examples[/bold green]\n\n"
    "[cyan]ctac sbf-tac prog.sbf.json prog.tac --plain[/cyan]\n\n"
    "[cyan]ctac sbf-tac prog.sbf.json prog.tac --plain --from B12[/cyan]"
    "  [dim]# slice from sbf block B12[/dim]\n\n"
    "[cyan]ctac sbf-tac prog.sbf.json prog.tac --plain --address-range 0x5f000-0x5f200[/cyan]"
    "  [dim]# pin a bytecode window[/dim]\n\n"
    "[cyan]ctac sbf-tac prog.sbf.json prog.tac --plain | grep 0x5f088[/cyan]"
    "  [dim]# all rows for one bytecode address[/dim]"
)


_INLINE_COMMENT_RE = re.compile(r"/\*.*?\*/")


def _compact_sbf_line(s: str) -> str:
    """Drop ``/* ... */`` comments from an SBF instruction text.

    Production SBF dumps annotate every instruction with comments like
    ``/* 0x5f0c0 */ /*call_id=151*/ /*inlined_function_name=…*/``; in
    a side-by-side join the bytecode address is already in column 0 and
    the inlined-function metadata can run hundreds of characters wide,
    pushing the TAC column off-screen. The original file (and
    ``ctac pp <sbf>.sbf.json``) still has the comments for when you
    need them.
    """
    return _INLINE_COMMENT_RE.sub("", s).rstrip()


@app.command("sbf-tac", rich_help_panel=COMPARE_PANEL, epilog=_SBF_TAC_EPILOG)
def sbf_tac(
    sbf: Path = typer.Argument(
        ...,
        exists=True,
        dir_okay=True,
        readable=True,
        help="Path to .sbf.json (or a directory containing one).",
    ),
    tac: Path = typer.Argument(
        ...,
        exists=True,
        dir_okay=True,
        readable=True,
        help="Path to .tac (or directory).",
    ),
    plain: bool = typer.Option(False, "--plain", help=PLAIN_HELP),
    agent: bool = agent_option(),
    output_path: Annotated[
        Optional[Path],
        typer.Option(
            "-o",
            "--output",
            help="Write joined output to this file (plain text) instead of stdout.",
        ),
    ] = None,
    printer: Annotated[
        str,
        typer.Option(
            "--printer",
            help="Pretty-printer backend. Built-ins: human (default), raw.",
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
    to_block: Annotated[
        Optional[str],
        typer.Option("--to", metavar="NBID", help=FILTER_TO_HELP),
    ] = None,
    from_block: Annotated[
        Optional[str],
        typer.Option("--from", metavar="NBID", help=FILTER_FROM_HELP),
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
    address_range: Annotated[
        Optional[str],
        typer.Option(
            "--address-range",
            metavar="LO-HI",
            help=(
                "Show only SBF instructions whose bytecode address is in "
                "the inclusive range [LO, HI]. LO/HI accept hex (0x...) "
                "or decimal. Blocks left with no rows are skipped. "
                "(Same flag spelling as `ctac pp --address-range`.)"
            ),
        ),
    ] = None,
    weak_is_strong: bool = typer.Option(
        False,
        "--weak-is-strong",
        help="Parse snippet weak refs as strong refs.",
    ),
) -> None:
    """Annotate each SBF instruction with the TAC commands at the same bytecode address."""
    _ = agent
    plain = plain_requested(plain)
    c = console(plain)
    try:
        sbf_path, sbf_warnings = resolve_tac_input_path(sbf)
        tac_path, tac_warnings = resolve_tac_input_path(tac)
        sbf_tac_file = parse_path(sbf_path, weak_is_strong=weak_is_strong)
        tac_file = parse_path(tac_path, weak_is_strong=weak_is_strong)
    except ParseError as e:
        c.print(f"parse error: {e}" if plain else f"[red]parse error:[/red] {e}")
        raise typer.Exit(1) from e
    except ValueError as e:
        c.print(f"input error: {e}" if plain else f"[red]input error:[/red] {e}")
        raise typer.Exit(1) from e

    addr_rng: tuple[int, int] | None = None
    if address_range is not None:
        try:
            addr_rng = parse_address_range(address_range)
        except ValueError as e:
            c.print(f"input error: {e}" if plain else f"[red]input error:[/red] {e}")
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
        filtered_sbf, filter_warnings = Cfg(sbf_tac_file.program).filtered(
            flt, preserve_successors=True,
        )
    except ValueError as e:
        c.print(f"filter error: {e}" if plain else f"[red]filter error:[/red] {e}")
        raise typer.Exit(2) from e

    printer_name = normalize_printer_name(printer)
    sbf_printer = configured_printer(
        printer_name,
        strip_var_suffixes=strip_var_suffixes,
        human_patterns=human,
    )
    tac_printer = configured_printer(
        printer_name,
        strip_var_suffixes=strip_var_suffixes,
        human_patterns=human,
    )

    # Build address -> [tac line] index from the full TAC program.
    # Skip cmds the printer drops (annotations / labels / etc.) and
    # cmds without a bytecode address — those would never join.
    tac_index: dict[int, list[str]] = {}
    for b in tac_file.program.blocks:
        for cmd in b.commands:
            addr = bytecode_addr_for_cmd(cmd, tac_file.metas)
            if addr is None:
                continue
            line = tac_printer.print_cmd(cmd)
            if line is None or line == "":
                continue
            tac_index.setdefault(addr, []).append(line)

    to_buffer = output_path is not None
    file_lines: list[str] = []

    def _emit(text: str) -> None:
        if to_buffer:
            file_lines.append(text)
        else:
            c.print(text)

    def _emit_table(table: Table) -> None:
        if to_buffer:
            with c.capture() as cap:
                c.print(table)
            file_lines.append(cap.get().rstrip("\n"))
        else:
            c.print(table)

    if sbf_tac_file.path:
        _emit(f"# sbf: {sbf_tac_file.path}")
    if tac_file.path:
        _emit(f"# tac: {tac_file.path}")
    for w in sbf_warnings:
        _emit(f"# input warning: sbf: {w}")
    for w in tac_warnings:
        _emit(f"# input warning: tac: {w}")
    for w in filter_warnings:
        _emit(f"# {w}")
    _emit("# note: tac cmds without sbf addresses are not shown — see ctac pp <tac> for the full TAC view")
    if flt.any_active():
        _emit(
            f"# filter: {len(filtered_sbf.blocks)} of {len(sbf_tac_file.program.blocks)} sbf block(s)"
        )

    # SBF traces commonly contain repeated bytecode addresses — the
    # same instruction can appear under several inlined call paths.
    # Don't consume the tac_index entry on first match; each SBF
    # occurrence gets the full TAC join, which is what makes the
    # lowering visible at every callsite.
    for b in filtered_sbf.ordered_blocks():
        table = Table.grid(expand=False, padding=(0, 2))
        table.add_column(no_wrap=True, overflow="ellipsis")  # address
        table.add_column()  # sbf instruction
        table.add_column(justify="left")  # tac command

        rows = 0
        for cmd in b.commands:
            sbf_line = sbf_printer.print_cmd(cmd)
            if sbf_line is None or sbf_line == "":
                continue
            sbf_line = _compact_sbf_line(sbf_line)
            addr = bytecode_addr_for_cmd(cmd, sbf_tac_file.metas)
            if addr_rng is not None and (
                addr is None or not (addr_rng[0] <= addr <= addr_rng[1])
            ):
                continue
            addr_text = f"0x{addr:x}" if addr is not None else ""
            tac_lines = tac_index.get(addr, []) if addr is not None else []

            sbf_cell = highlight_tac_line(sbf_line) if not plain else Text(sbf_line)
            if not tac_lines:
                table.add_row(Text(addr_text), sbf_cell, Text(""))
            else:
                first_tac = (
                    highlight_tac_line(tac_lines[0]) if not plain else Text(tac_lines[0])
                )
                table.add_row(Text(addr_text), sbf_cell, first_tac)
                for tac_line in tac_lines[1:]:
                    cont = highlight_tac_line(tac_line) if not plain else Text(tac_line)
                    table.add_row(Text(""), Text(""), cont)
            rows += 1

        # Skip blocks that lost every row to the address filter — printing
        # a header for an empty block is just visual noise.
        if rows:
            _emit(f"{b.id}:")
            _emit_table(table)
            _emit("")

    if to_buffer:
        text = "\n".join(file_lines) + ("\n" if file_lines else "")
        written, _info = ingest_or_write_text(
            explicit_output=output_path,
            project=None,
            text=text,
            command="sbf-tac",
            kind="txt",
            advance_head=False,
        )
        assert written is not None
        if plain:
            c.print(f"# wrote {written}", markup=False)
        else:
            c.print(f"[cyan]wrote[/cyan]: [bold]{written}[/bold]")
