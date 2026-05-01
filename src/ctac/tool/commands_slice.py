"""``ctac slice`` — backward static slicer presenter.

This module exposes the CLI; the slicing algorithm itself lives in
:mod:`ctac.analysis.slice` so other tooling can call it directly.
The CLI is responsible for:

- parsing user-friendly criterion strings (``SYM`` / ``SYM@BLK`` /
  ``BLK:assert`` / ``BLK``) into :class:`SliceCriterion` values;
- pre-scoping the program with the shared ``CfgFilterOptions``
  (``--from``/``--to``/etc.) before computing the slice;
- walking blocks itself to render output, since the slicer's result
  is per-:class:`ProgramPoint` and the existing ``pretty_lines``
  helper sees only ``TacCmd`` (no block/index context).
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Annotated, Optional

import typer

from ctac.analysis import (
    SliceConfig,
    SliceCriterion,
    SliceCriterionError,
    compute_slice,
    extract_def_use,
)
from ctac.analysis.model import ProgramPoint
from ctac.ast.pretty import configured_printer
from ctac.ast.run_format import pp_terminator_line
from ctac.graph import Cfg
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
from ctac.tool.filters import CfgFilterOptions, apply_cfg_filters
from ctac.tool.input_resolution import resolve_tac_input_path, resolve_user_path


_CRITERION_HELP = (
    "Slicing criterion. Repeat to seed multiple. Forms:\n"
    "  SYM            every def of the canonical symbol\n"
    "                 (in DSA, usually a single point;\n"
    "                  for dynamic registers, all sibling defs)\n"
    "  SYM@BLK        the def(s) of SYM in block BLK\n"
    "                 (disambiguates dynamic registers)\n"
    "  BLK:assert     the last AssertCmd in BLK\n"
    "  BLK            every command in BLK as a seed"
)

_SHOW_HELP = (
    "Output mode: pp (default, sliced TAC as htac), points "
    "(block:cmd-index pairs, machine-friendly), stats (counts only), "
    "json (full SliceResult as JSON)."
)

_MARK_HELP = (
    "How to render non-selected commands: drop (default — clean "
    "reading), elide (collapse runs into '...'), gray (show all "
    "commands; non-selected are dimmed in rich mode and prefixed with "
    "'# ' under --plain so the output stays grep-friendly)."
)


_SLICE_EPILOG = (
    "[bold green]What it does[/bold green]  Backward static slice "
    "through data and control dependences. The slicer follows uses "
    "to their reaching defs (data) and pulls in controlling JumpiCmds "
    "via post-dominance (control). Bytemap chains "
    "([cyan]Select(M, k)[/cyan] -> defining [cyan]Store(M', k', v')[/cyan] "
    "-> earlier stores) fall out automatically.\n\n"
    "[bold green]Criterion forms[/bold green]\n"
    "  [cyan]SYM[/cyan]            every def of canonical SYM\n"
    "  [cyan]SYM@BLK[/cyan]        def(s) of SYM in block BLK\n"
    "  [cyan]BLK:assert[/cyan]     the last AssertCmd in BLK\n"
    "  [cyan]BLK[/cyan]            every cmd in BLK as a seed\n\n"
    "[bold green]Examples[/bold green]\n\n"
    "[cyan]ctac slice f.tac -c B1054 --plain[/cyan]"
    "  [dim]# data + control slice rooted at B1054[/dim]\n\n"
    "[cyan]ctac slice f.tac -c B1054 --no-control --plain[/cyan]"
    "  [dim]# data-only chain, drops branch context[/dim]\n\n"
    "[cyan]ctac slice f.tac -c 19_1_0_0_0_0:assert --plain[/cyan]"
    "  [dim]# slice from the assert in this block[/dim]\n\n"
    "[cyan]ctac slice f.tac -c R10@5_2_0 -c R11@7_0_1 --plain[/cyan]"
    "  [dim]# multiple seeds, each disambiguated by block[/dim]\n\n"
    "[cyan]ctac slice f.tac -c M1031 --show stats --plain[/cyan]"
    "  [dim]# how many cmds touch this bytemap[/dim]"
)


def _looks_like_block_id(token: str, by_id: dict) -> bool:
    return token in by_id


def parse_criterion(
    spec: str,
    *,
    program,
    def_use,
) -> SliceCriterion:
    """Parse one user-supplied criterion string.

    Block ids in TAC use digits/underscores; canonical symbols are
    alphanumeric without ``:`` or ``@``. We rely on these character
    classes plus a lookup against the program (block ids) and def-use
    (symbols) to disambiguate bare tokens.
    """
    s = spec.strip()
    if not s:
        raise typer.BadParameter("empty criterion", param_hint="--criterion")
    by_id = program.block_by_id()

    # Form: SYM@BLK
    if "@" in s:
        sym, _, bid = s.partition("@")
        sym = sym.strip()
        bid = bid.strip()
        if not sym or not bid:
            raise typer.BadParameter(
                f"malformed SYM@BLK criterion: {spec!r}",
                param_hint="--criterion",
            )
        if bid not in by_id:
            raise typer.BadParameter(
                f"unknown block in criterion {spec!r}: {bid!r}",
                param_hint="--criterion",
            )
        return SliceCriterion(symbol_in_block=(sym, bid))

    # Form: BLK:assert (the only ":" form we accept; cmd indices are
    # too brittle for users because annotations occupy slots).
    if ":" in s:
        bid, _, tail = s.partition(":")
        bid = bid.strip()
        tail = tail.strip().lower()
        if tail != "assert":
            raise typer.BadParameter(
                f"unsupported criterion form {spec!r}; only "
                "'BLK:assert' uses ':' (cmd indices are not exposed)",
                param_hint="--criterion",
            )
        if bid not in by_id:
            raise typer.BadParameter(
                f"unknown block in criterion {spec!r}: {bid!r}",
                param_hint="--criterion",
            )
        return SliceCriterion(last_assert_in_block=bid)

    # Bare token: disambiguate block-id vs symbol vs whole-block.
    # If the token is a known block id AND a known symbol, the block
    # form wins (more specific) and we warn.
    is_block = _looks_like_block_id(s, by_id)
    is_symbol = s in def_use.definitions_by_symbol
    if is_block:
        return SliceCriterion(whole_block=s)
    if is_symbol:
        return SliceCriterion(symbol=s)
    raise typer.BadParameter(
        f"criterion {spec!r} matches neither a known block id nor a "
        "defined symbol. Tip: use SYM@BLK to disambiguate, or check "
        "that you're targeting the canonical (suffix-stripped) name.",
        param_hint="--criterion",
    )


def _criterion_summary(crit: SliceCriterion) -> str:
    if crit.symbol is not None:
        return f"symbol={crit.symbol!r}"
    if crit.symbol_in_block is not None:
        sym, bid = crit.symbol_in_block
        return f"symbol={sym!r}@block={bid!r}"
    if crit.last_assert_in_block is not None:
        return f"block={crit.last_assert_in_block!r}:assert"
    if crit.whole_block is not None:
        return f"block={crit.whole_block!r} (whole)"
    if crit.point is not None:
        return f"point={crit.point.block_id}:{crit.point.cmd_index}"
    return "<empty>"


def _serialize_seed(pt: ProgramPoint) -> str:
    return f"{pt.block_id}:{pt.cmd_index}"


def _render_slice_pp(
    *,
    program,
    selected: frozenset[ProgramPoint],
    pp_backend,
    mark: str,
    plain: bool,
    strip_var_suffixes: bool,
    output_path: Optional[Path],
    c,
    preamble: list[str],
) -> None:
    """Walk blocks and emit a sliced htac-style pretty-print."""
    to_file = output_path is not None
    file_lines: list[str] = []

    def _emit(text: str) -> None:
        if to_file:
            file_lines.append(text)
        else:
            c.print(text)

    for line in preamble:
        _emit(line)

    cfg_model = Cfg(program)
    for b in cfg_model.ordered_blocks():
        body: list[str] = []
        last_was_elision = False
        for idx, cmd in enumerate(b.commands):
            line = pp_backend.print_cmd(cmd)
            if line is None or line == "":
                continue
            pt = ProgramPoint(b.id, idx)
            if pt in selected:
                body.append(f"  {line}")
                last_was_elision = False
            else:
                if mark == "drop":
                    continue
                if mark == "elide":
                    if not last_was_elision:
                        body.append("  ...")
                        last_was_elision = True
                    continue
                # mark == "gray"
                if plain:
                    body.append(f"  # {line}")
                else:
                    body.append(f"  [dim]{line}[/dim]")
                last_was_elision = False

        # Block participation: if no command in this block was selected,
        # we still want to keep the header when control-relevant blocks
        # are referenced as targets — but the simplest rule that keeps
        # output valid htac is: drop the block entirely if nothing is
        # selected and we're in "drop" mode.
        block_has_selected = any(
            ProgramPoint(b.id, i) in selected for i in range(len(b.commands))
        )
        if mark == "drop" and not block_has_selected:
            continue

        _emit(f"{b.id}:")
        for ln in body:
            _emit(ln)
        term_line = pp_terminator_line(b, strip_var_suffixes=strip_var_suffixes)
        if term_line is not None:
            _emit(f"  {term_line}")
        elif b.successors:
            _emit(f"  goto {', '.join(b.successors)}")
        else:
            _emit("  stop")
        _emit("")

    if to_file:
        assert output_path is not None
        output_path.write_text(
            "\n".join(file_lines) + ("\n" if file_lines else ""),
            encoding="utf-8",
        )
        if plain:
            c.print(f"# wrote {output_path}", markup=False)
        else:
            c.print(f"[cyan]wrote[/cyan]: [bold]{output_path}[/bold]")


def _render_slice_points(
    selected: frozenset[ProgramPoint],
    *,
    c,
    preamble: list[str],
) -> None:
    for line in preamble:
        c.print(line)
    for pt in sorted(selected, key=lambda p: (p.block_id, p.cmd_index)):
        c.print(f"{pt.block_id}:{pt.cmd_index}")


def _render_slice_stats(
    *,
    program,
    selected: frozenset[ProgramPoint],
    seeds: tuple[ProgramPoint, ...],
    rounds: int,
    c,
    preamble: list[str],
) -> None:
    for line in preamble:
        c.print(line)
    total_cmds = sum(len(b.commands) for b in program.blocks)
    blocks_with_selection = {pt.block_id for pt in selected}
    c.print(f"selected_cmds: {len(selected)}")
    c.print(f"total_cmds: {total_cmds}")
    c.print(f"selected_blocks: {len(blocks_with_selection)}")
    c.print(f"total_blocks: {len(program.blocks)}")
    c.print(f"seeds: {len(seeds)}")
    c.print(f"rounds: {rounds}")


def _render_slice_json(
    *,
    program,
    selected: frozenset[ProgramPoint],
    seeds: tuple[ProgramPoint, ...],
    rounds: int,
    warnings: tuple[str, ...],
    c,
) -> None:
    payload = {
        "selected": sorted(
            ({"block_id": pt.block_id, "cmd_index": pt.cmd_index} for pt in selected),
            key=lambda d: (d["block_id"], d["cmd_index"]),
        ),
        "seeds": [
            {"block_id": pt.block_id, "cmd_index": pt.cmd_index} for pt in seeds
        ],
        "rounds": rounds,
        "warnings": list(warnings),
        "total_cmds": sum(len(b.commands) for b in program.blocks),
        "total_blocks": len(program.blocks),
    }
    c.print(json.dumps(payload, indent=2))


@app.command("slice", rich_help_panel=INSPECT_PANEL, epilog=_SLICE_EPILOG)
def slice_cmd(
    path: Optional[Path] = typer.Argument(
        None,
        help="Path to .tac / .sbf.json file, or a Certora output directory.",
    ),
    criterion: Annotated[
        list[str],
        typer.Option(
            "-c",
            "--criterion",
            metavar="SPEC",
            help=_CRITERION_HELP,
        ),
    ] = [],
    plain: bool = typer.Option(False, "--plain", help=PLAIN_HELP),
    agent: bool = agent_option(),
    follow_data: bool = typer.Option(
        True,
        "--data/--no-data",
        help="Follow data dependences (reaching defs). Default on.",
    ),
    follow_control: bool = typer.Option(
        True,
        "--control/--no-control",
        help="Follow control dependences (post-dominance). Default on.",
    ),
    include_weak: bool = typer.Option(
        False,
        "--include-weak/--no-weak",
        help="Include AnnotationCmd weak refs as data dependences. Default off.",
    ),
    depth: Annotated[
        Optional[int],
        typer.Option(
            "--depth",
            min=0,
            help="Bound on slicing rounds. 0 = just the seeds. Default unlimited.",
        ),
    ] = None,
    show: Annotated[
        str,
        typer.Option(
            "--show",
            help=_SHOW_HELP,
            autocompletion=complete_choices(["pp", "points", "stats", "json"]),
        ),
    ] = "pp",
    mark: Annotated[
        str,
        typer.Option(
            "--mark",
            help=_MARK_HELP,
            autocompletion=complete_choices(["drop", "elide", "gray"]),
        ),
    ] = "drop",
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
        help="Strip TAC var meta suffixes (e.g. ':1') in printed symbols.",
    ),
    human: bool = typer.Option(
        True,
        "--human/--no-human",
        help="Enable human-oriented pattern rewrites in pretty output.",
    ),
    output_path: Annotated[
        Optional[Path],
        typer.Option(
            "-o", "--output", help="Write sliced output to this file (plain text)."
        ),
    ] = None,
    to_block: Annotated[
        Optional[str], typer.Option("--to", metavar="NBID", help=FILTER_TO_HELP)
    ] = None,
    from_block: Annotated[
        Optional[str], typer.Option("--from", metavar="NBID", help=FILTER_FROM_HELP)
    ] = None,
    only: Annotated[
        Optional[str], typer.Option("--only", help=FILTER_ONLY_HELP)
    ] = None,
    id_contains: Annotated[
        Optional[str],
        typer.Option("--id-contains", help=FILTER_ID_CONTAINS_HELP),
    ] = None,
    id_regex: Annotated[
        Optional[str], typer.Option("--id-regex", help=FILTER_ID_REGEX_HELP)
    ] = None,
    cmd_contains: Annotated[
        Optional[str],
        typer.Option("--cmd-contains", help=FILTER_CMD_CONTAINS_HELP),
    ] = None,
    exclude: Annotated[
        Optional[str], typer.Option("--exclude", help=FILTER_EXCLUDE_HELP)
    ] = None,
    weak_is_strong: bool = typer.Option(
        False,
        "--weak-is-strong",
        help="Parse snippet weak refs as strong refs.",
    ),
) -> None:
    """Backward static slice through data and control dependences."""
    _ = agent
    plain = plain_requested(plain)
    c = console(plain)

    if not criterion:
        if plain:
            c.print("error: --criterion / -c is required (at least one)")
        else:
            c.print(
                "[red]error:[/red] [cyan]--criterion[/cyan] / [cyan]-c[/cyan] "
                "is required (at least one)"
            )
        raise typer.Exit(2)

    show_norm = show.strip().lower()
    if show_norm not in ("pp", "points", "stats", "json"):
        raise typer.BadParameter(
            f"unknown --show {show!r}; choose pp, points, stats, or json",
            param_hint="--show",
        )
    mark_norm = mark.strip().lower()
    if mark_norm not in ("drop", "elide", "gray"):
        raise typer.BadParameter(
            f"unknown --mark {mark!r}; choose drop, elide, or gray",
            param_hint="--mark",
        )

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

    cfg_opts = CfgFilterOptions(
        to_block=to_block,
        from_block=from_block,
        only=only,
        id_contains=id_contains,
        id_regex=id_regex,
        cmd_contains=cmd_contains,
        exclude=exclude,
    )
    try:
        program, filter_warnings = apply_cfg_filters(tac.program, cfg_opts)
    except ValueError as e:
        if plain:
            c.print(f"slice filter error: {e}")
        else:
            c.print(f"[red]slice filter error:[/red] {e}")
        raise typer.Exit(2) from e

    if not program.blocks:
        if plain:
            c.print("# no blocks after pre-slice filtering")
        else:
            c.print("[yellow]# no blocks after pre-slice filtering[/yellow]")
        raise typer.Exit(0)

    du = extract_def_use(program, strip_var_suffixes=strip_var_suffixes)

    try:
        crits = [
            parse_criterion(spec, program=program, def_use=du)
            for spec in criterion
        ]
    except typer.BadParameter:
        raise

    cfg = SliceConfig(
        follow_data=follow_data,
        follow_control=follow_control,
        include_weak_uses=include_weak,
        max_depth=depth,
        strip_var_suffixes=strip_var_suffixes,
    )
    try:
        result = compute_slice(program, crits, cfg, def_use=du)
    except SliceCriterionError as e:
        if plain:
            c.print(f"criterion error: {e}")
        else:
            c.print(f"[red]criterion error:[/red] {e}")
        raise typer.Exit(2) from e

    preamble: list[str] = []
    if tac.path:
        preamble.append(f"# path: {tac.path}")
    for w in user_warnings + input_warnings:
        preamble.append(f"# input warning: {w}")
    for w in filter_warnings:
        preamble.append(f"# {w}")
    for w in result.warnings:
        preamble.append(f"# slice warning: {w}")
    if cfg_opts.any_active():
        preamble.append(
            f"# pre-slice filter: {len(program.blocks)} of "
            f"{len(tac.program.blocks)} block(s)"
        )
    preamble.append(
        "# slice: "
        f"{len(criterion)} criterion(s) -> "
        f"{len(result.selected)} cmd(s) in "
        f"{len({pt.block_id for pt in result.selected})} block(s); "
        f"rounds={result.rounds}"
    )
    for crit, spec in zip(crits, criterion):
        preamble.append(f"#   criterion {spec!r}: {_criterion_summary(crit)}")
    preamble.append(
        "# seeds: "
        + (", ".join(_serialize_seed(pt) for pt in result.seeds) or "(none)")
    )
    preamble.append(f"# data={follow_data} control={follow_control} mark={mark_norm}")

    if show_norm == "pp":
        pp_backend = configured_printer(
            printer,
            strip_var_suffixes=strip_var_suffixes,
            human_patterns=human,
        )
        _render_slice_pp(
            program=program,
            selected=result.selected,
            pp_backend=pp_backend,
            mark=mark_norm,
            plain=plain,
            strip_var_suffixes=strip_var_suffixes,
            output_path=output_path,
            c=c,
            preamble=preamble,
        )
    elif show_norm == "points":
        _render_slice_points(result.selected, c=c, preamble=preamble)
    elif show_norm == "stats":
        _render_slice_stats(
            program=program,
            selected=result.selected,
            seeds=result.seeds,
            rounds=result.rounds,
            c=c,
            preamble=preamble,
        )
    else:
        _render_slice_json(
            program=program,
            selected=result.selected,
            seeds=result.seeds,
            rounds=result.rounds,
            warnings=result.warnings,
            c=c,
        )
