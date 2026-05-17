"""`ctac smtlib` — inspect and transform SMT-LIB v2 files.

Subcommands:
  ctac smtlib stats     <FILE>           # statement-kind counts, sizes, chains
  ctac smtlib pp        <FILE>           # pretty-print via the Doc algebra
  ctac smtlib roundtrip <FILE>           # parse + emit; check byte-identical
  ctac smtlib slice     <FILE>           # filter by --kinds / --range
"""
from __future__ import annotations

import re
from collections import Counter
from pathlib import Path
from typing import Optional

import typer

from ctac.solver.smt2 import (
    Assert,
    DeclareConst,
    DefineFun,
    PpPolicy,
    SetLogic,
    SetOption,
    Smt2Statement,
    emit,
    parse,
    pp,
    pp_statement,
    scan_uf_arguments,
)
from ctac.solver.smt2.doc import render as doc_render
from ctac.solver.smt2.sexpr import Atom, List_
from ctac.tool.cli_runtime import (
    INSPECT_PANEL,
    PLAIN_HELP,
    agent_option,
    app,
    console,
    plain_requested,
)


_SMTLIB_EPILOG = (
    "[bold green]First look[/bold green]  "
    "[cyan]ctac smtlib stats f.smt2 --plain[/cyan]  "
    "command-kind counts + bytemap chains.\n\n"
    "[bold green]Pretty-print[/bold green]  "
    "[cyan]ctac smtlib pp f.smt2 -w 100 -o out.smt2[/cyan]  "
    "policy-driven re-emit.\n\n"
    "[bold green]Sanity check[/bold green]  "
    "[cyan]ctac smtlib roundtrip f.smt2[/cyan]  "
    "parse + emit; verify byte-identical."
)


# A sub-app so subcommands look like `ctac smtlib stats <file>`
smtlib_app = typer.Typer(
    no_args_is_help=True,
    help='Inspect / pretty-print / transform SMT-LIB v2 files.',
    rich_markup_mode='rich',
    epilog=_SMTLIB_EPILOG,
)
app.add_typer(smtlib_app, name='smtlib', rich_help_panel=INSPECT_PANEL,
                help='Inspect SMT-LIB v2 files (stats / pp / roundtrip).')


@smtlib_app.callback(invoke_without_command=True)
def _smtlib_callback(
    ctx: typer.Context,
    agent: bool = agent_option(),
) -> None:
    # Mirrors the top-level `ctac --agent` callback so users can run
    # `ctac smtlib --agent` and get the group-level agent guide instead
    # of typer's "missing subcommand" error.
    _ = (ctx, agent)


# ---- stats -----------------------------------------------------------------


_M_PATTERN = re.compile(r'^M\w+$')


def _chain_depth(file, m_name: str) -> int:
    """Walk a `(define-fun M_n ((idx Int)) Int (ite (= idx K) V (M_{n-1} idx)))`
    chain starting at `m_name`, returning the depth."""
    by_name = {}
    for s in file.statements:
        if isinstance(s, DefineFun) and s.name == m_name:
            by_name[s.name] = s
            break
    if not by_name:
        return 0
    # Build name → next-link from all chain define-funs
    chain_map: dict[str, str | None] = {}
    for s in file.statements:
        if not isinstance(s, DefineFun):
            continue
        if len(s.params) != 1:
            continue
        # body shape: (ite (= idx K) V (M_prev idx)) — look for trailing UF app
        b = s.body
        if not isinstance(b, List_):
            continue
        nxt = _find_chain_next(b, s.params[0].name)
        chain_map[s.name] = nxt
    depth = 0
    cur: str | None = m_name
    seen = set()
    while cur and cur in chain_map and cur not in seen:
        seen.add(cur)
        depth += 1
        cur = chain_map.get(cur)
    return depth


def _find_chain_next(body: List_, param_name: str) -> str | None:
    """Inside a chain-link body, return the name of the next M referenced
    as `(M_prev idx)`. None if no such reference."""
    if not body.children:
        return None
    h = body.children[0]
    # (ite cond then else) — recurse into branches
    if isinstance(h, Atom) and h.text == 'ite' and len(body.children) == 4:
        for child in body.children[1:]:
            if isinstance(child, List_):
                r = _find_chain_next(child, param_name)
                if r is not None:
                    return r
        return None
    # (M_n idx) shape
    if (isinstance(h, Atom) and _M_PATTERN.match(h.text) and
        len(body.children) == 2 and
        isinstance(body.children[1], Atom) and
        body.children[1].text == param_name):
        return h.text
    # Otherwise walk children
    for c in body.children:
        if isinstance(c, List_):
            r = _find_chain_next(c, param_name)
            if r is not None:
                return r
    return None


@smtlib_app.command('stats', help='Show command counts and key structural stats.')
def cmd_stats(
    smt2: Path = typer.Argument(..., exists=True, dir_okay=False,
                                  help='SMT2 input file.'),
    plain: bool = typer.Option(False, '--plain', help=PLAIN_HELP),
    agent: bool = agent_option(),
) -> None:
    _ = agent
    cons = console(plain_requested(plain))
    f = parse(smt2)
    src_bytes = len(f.source)
    n_lines = f.source.count('\n')
    n = len(f.statements)

    # Statement kind counts
    kinds = Counter(type(s).__name__ for s in f.statements)
    # Specific drill-downs
    n_assert = kinds.get('Assert', 0)
    named_asserts = sum(1 for s in f.statements
                         if isinstance(s, Assert) and s.named is not None)

    # Declare-const sort distribution
    sort_dist: Counter[str] = Counter()
    for s in f.statements:
        if isinstance(s, DeclareConst):
            sort_dist[_sort_str(s.sort_node)] += 1

    # Define-fun chain stats
    chain_links = [s for s in f.statements
                    if isinstance(s, DefineFun) and _is_int_to_int(s)
                    and _M_PATTERN.match(s.name)]
    chain_depths: list[int] = []
    for s in chain_links:
        chain_depths.append(_chain_depth(f, s.name))

    # UF args (alias-cover T)
    T = scan_uf_arguments(f, _M_PATTERN)
    n_t_vars = len({arg for args in T.values() for arg in args})

    # Set-option keys
    options = [s.key for s in f.statements if isinstance(s, SetOption)]
    logic = next((s.logic for s in f.statements if isinstance(s, SetLogic)),
                  None)

    if plain_requested(plain):
        cons.print(f'overview.path: {smt2}')
        cons.print(f'overview.bytes: {src_bytes}')
        cons.print(f'overview.lines: {n_lines}')
        cons.print(f'overview.statements: {n}')
        if logic:
            cons.print(f'overview.logic: {logic}')
        if options:
            cons.print(f'overview.set_options: {len(options)}')
        cons.print('command_kinds:')
        for k, v in kinds.most_common():
            cons.print(f'  {k}: {v}')
        if named_asserts:
            cons.print(f'asserts.named: {named_asserts} / {n_assert}')
        if sort_dist:
            cons.print('declare_const.sorts:')
            for k, v in sort_dist.most_common():
                cons.print(f'  {k}: {v}')
        if chain_links:
            cons.print(f'bytemap_chains.links: {len(chain_links)}')
            cons.print(f'bytemap_chains.depth.min: {min(chain_depths)}')
            cons.print(f'bytemap_chains.depth.median: {sorted(chain_depths)[len(chain_depths)//2]}')
            cons.print(f'bytemap_chains.depth.max: {max(chain_depths)}')
            cons.print(f'uf_args.unique_t_vars: {n_t_vars}')
    else:
        from rich.table import Table
        tbl = Table(title=f'ctac smtlib stats — {smt2.name}',
                     show_lines=False)
        tbl.add_column('key')
        tbl.add_column('value', justify='right')
        tbl.add_row('path', str(smt2))
        tbl.add_row('bytes', f'{src_bytes:,}')
        tbl.add_row('lines', f'{n_lines:,}')
        tbl.add_row('statements', f'{n:,}')
        if logic:
            tbl.add_row('logic', logic)
        if options:
            tbl.add_row('set-options', str(len(options)))
        cons.print(tbl)

        cmd_tbl = Table(title='Command kinds', show_lines=False)
        cmd_tbl.add_column('kind')
        cmd_tbl.add_column('count', justify='right')
        for k, v in kinds.most_common():
            cmd_tbl.add_row(k, str(v))
        cons.print(cmd_tbl)

        if named_asserts:
            cons.print(f'[bold]named asserts:[/bold] {named_asserts} / {n_assert}')

        if sort_dist:
            sort_tbl = Table(title='declare-const sorts', show_lines=False)
            sort_tbl.add_column('sort')
            sort_tbl.add_column('count', justify='right')
            for k, v in sort_dist.most_common():
                sort_tbl.add_row(k, str(v))
            cons.print(sort_tbl)

        if chain_links:
            chain_tbl = Table(title='Bytemap chains (define-fun M_n Int→Int)',
                                show_lines=False)
            chain_tbl.add_column('metric')
            chain_tbl.add_column('value', justify='right')
            chain_tbl.add_row('total chain-link define-funs',
                                str(len(chain_links)))
            chain_tbl.add_row('chain depth min', str(min(chain_depths)))
            chain_tbl.add_row('chain depth median',
                                str(sorted(chain_depths)[len(chain_depths)//2]))
            chain_tbl.add_row('chain depth max', str(max(chain_depths)))
            chain_tbl.add_row('UF-arg declared-symbol variables',
                                str(n_t_vars))
            cons.print(chain_tbl)


def _is_int_to_int(stmt: DefineFun) -> bool:
    if len(stmt.params) != 1:
        return False
    p = stmt.params[0]
    if not (isinstance(p.sort_node, Atom) and p.sort_node.text == 'Int'):
        return False
    if not (isinstance(stmt.ret_sort_node, Atom)
             and stmt.ret_sort_node.text == 'Int'):
        return False
    return True


def _sort_str(node) -> str:
    if isinstance(node, Atom):
        return node.text
    if isinstance(node, List_):
        # compound sort like (Array Int Int)
        from ctac.solver.smt2.doc import render
        from ctac.solver.smt2.pp import pp_sexpr
        return render(pp_sexpr(node, PpPolicy(width=10**9)), width=10**9)
    return str(node)


# ---- pp --------------------------------------------------------------------


@smtlib_app.command('pp', help='Pretty-print the file via the Doc algebra.')
def cmd_pp(
    smt2: Path = typer.Argument(..., exists=True, dir_okay=False,
                                  help='SMT2 input file.'),
    width: int = typer.Option(100, '--width', '-w',
                                help='Soft target line width.'),
    no_comments: bool = typer.Option(False, '--no-comments',
                                       help='Drop comments from output.'),
    output: Optional[Path] = typer.Option(None, '-o', '--output',
                                            help='Write to PATH instead of stdout.'),
    plain: bool = typer.Option(False, '--plain', help=PLAIN_HELP),
    agent: bool = agent_option(),
) -> None:
    _ = agent
    cons = console(plain_requested(plain))
    f = parse(smt2)
    policy = PpPolicy(width=width, show_comments=not no_comments)
    text_out = pp(f, policy)
    if output:
        output.write_text(text_out)
        cons.print(f'wrote {output} ({len(text_out)} bytes)')
    else:
        # Print raw; avoid rich's word-wrapping
        import sys
        sys.stdout.write(text_out)


# ---- slice -----------------------------------------------------------------


# All concrete Smt2Statement names. Keep in sync with parser.py — used
# to validate `--kinds` input.
_KNOWN_KINDS = frozenset({
    'SetOption', 'SetLogic',
    'DeclareConst', 'DeclareFun', 'DefineFun',
    'Assert',
    'CheckSat', 'CheckSatUsing', 'Apply',
    'GetModel', 'GetInfo', 'GetValue', 'GetUnsatCore',
    'Push', 'Pop', 'Exit',
    'Comment', 'Raw',
})


def _parse_range(spec: str, n: int) -> tuple[int, int]:
    """`--range I-J` (0-based, inclusive) → clamped (lo, hi). `J` may
    exceed `n-1`; we clamp."""
    if '-' not in spec:
        raise typer.BadParameter(f'range must be `I-J`, got {spec!r}')
    lo_s, hi_s = spec.split('-', 1)
    lo = int(lo_s)
    hi = int(hi_s)
    if lo < 0 or hi < lo:
        raise typer.BadParameter(f'range {spec!r}: need 0 <= I <= J')
    return lo, min(hi, n - 1)


@smtlib_app.command('slice',
                     help='Filter statements by --kinds / --range and pretty-print.')
def cmd_slice(
    smt2: Path = typer.Argument(..., exists=True, dir_okay=False,
                                  help='SMT2 input file.'),
    kinds_spec: Optional[str] = typer.Option(
        None, '--kinds',
        help='Comma-separated statement kinds to keep '
              '(Assert, DeclareConst, DefineFun, SetOption, Comment, ...). '
              'Unknown names are rejected. Defaults to all.'),
    range_spec: Optional[str] = typer.Option(
        None, '--range',
        help='Statement index range I-J (0-based, inclusive on both ends).'),
    width: int = typer.Option(100, '--width', '-w',
                                help='Soft target line width.'),
    no_comments: bool = typer.Option(False, '--no-comments',
                                       help='Drop `;` comment blocks from output.'),
    output: Optional[Path] = typer.Option(
        None, '-o', '--output',
        help='Write to PATH instead of stdout.'),
    plain: bool = typer.Option(False, '--plain', help=PLAIN_HELP),
    agent: bool = agent_option(),
) -> None:
    _ = agent
    cons = console(plain_requested(plain))
    f = parse(smt2)
    n = len(f.statements)

    # Validate --kinds
    keep_kinds: Optional[frozenset[str]] = None
    if kinds_spec is not None:
        names = [s.strip() for s in kinds_spec.split(',') if s.strip()]
        unknown = [s for s in names if s not in _KNOWN_KINDS]
        if unknown:
            raise typer.BadParameter(
                f'unknown --kinds: {", ".join(unknown)}. '
                f'Known: {", ".join(sorted(_KNOWN_KINDS))}')
        keep_kinds = frozenset(names)

    # Validate --range
    lo, hi = (0, n - 1) if range_spec is None else _parse_range(range_spec, n)

    policy = PpPolicy(width=width, show_comments=not no_comments)

    # Filter: index in [lo, hi] AND kind in keep_kinds (if set)
    selected: list[tuple[int, Smt2Statement]] = []
    for i, stmt in enumerate(f.statements):
        if i < lo or i > hi:
            continue
        if keep_kinds is not None and type(stmt).__name__ not in keep_kinds:
            continue
        selected.append((i, stmt))

    # Render. One blank line between statements (mirrors emit / pp).
    parts: list[str] = []
    for _, stmt in selected:
        parts.append(doc_render(pp_statement(stmt, policy), width=width))
    text_out = '\n'.join(parts)
    if text_out and not text_out.endswith('\n'):
        text_out += '\n'

    if output:
        output.write_text(text_out)
        cons.print(f'wrote {output} ({len(selected)} / {n} statements, '
                    f'{len(text_out)} bytes)')
        return

    import sys
    sys.stdout.write(text_out)


# ---- roundtrip -------------------------------------------------------------


@smtlib_app.command('roundtrip',
                     help='Parse then emit; report whether result is '
                          'byte-identical to the input.')
def cmd_roundtrip(
    smt2: Path = typer.Argument(..., exists=True, dir_okay=False,
                                  help='SMT2 input file.'),
    plain: bool = typer.Option(False, '--plain', help=PLAIN_HELP),
    agent: bool = agent_option(),
) -> None:
    _ = agent
    cons = console(plain_requested(plain))
    src = smt2.read_text()
    f = parse(smt2)
    out = emit(f)
    if out == src:
        cons.print(f'[bold green]OK[/bold green]  byte-identical '
                    f'({len(src):,} bytes, {len(f.statements):,} statements)')
        return
    # First difference for diagnostics
    for i, (a, b) in enumerate(zip(src, out)):
        if a != b:
            cons.print(f'[red]DIFF[/red] at offset {i}:')
            ctx_start = max(0, i - 20)
            cons.print(f'  src: {src[ctx_start:i+20]!r}')
            cons.print(f'  out: {out[ctx_start:i+20]!r}')
            break
    if len(src) != len(out):
        cons.print(f'length mismatch: src={len(src)} out={len(out)}')
    raise typer.Exit(1)
