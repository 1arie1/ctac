"""Uniform handling of TAC output files for ``-o PATH`` flags.

Every CLI command that writes a TAC program to disk follows the same
extension-based convention:

- ``-o FILE.tac`` (or any non-``.htac`` suffix) writes raw,
  round-trippable TAC — what other ``ctac`` commands consume.
- ``-o FILE.htac`` writes pretty-printed (human-readable) TAC.
  ``.htac`` files are NOT round-trippable; treat them as a viewing
  format, like the default of ``ctac pp``.

Centralizing the dispatch here so every emitting command (``rw``,
``ua``, ``rw-eq``, ``splitcrit``, ``df`` when its ``--style`` isn't
explicit) makes the same choice. Adding a new emitting command? Use
:func:`write_program_to_path`.
"""

from __future__ import annotations

from pathlib import Path
from typing import Literal

from ctac.analysis import extract_def_use
from ctac.ast.pretty import configured_printer
from ctac.ast.run_format import pp_terminator_line
from ctac.graph import Cfg
from ctac.ir.models import TacProgram
from ctac.parse import render_tac_file


def filter_live_extra_symbols(
    extra_symbols: "tuple[tuple[str, str], ...]",
    program: TacProgram,
) -> "tuple[tuple[str, str], ...]":
    """Drop entries from ``extra_symbols`` whose name doesn't appear
    anywhere in ``program``'s def-use.

    Background: rewriter rules (CSE, R4a, R6, ITE_PURIFY, PURIFY_*)
    queue fresh-variable declarations into ``RewriteResult.extra_symbols``
    each time they emit a new symbol. ``extra_symbols`` is append-only;
    when a downstream pass (DCE, copy-prop) removes the corresponding
    ``AssignExpCmd``, the symbol-table declaration sticks around as
    an orphan. This helper prunes those.

    Liveness here is "appears in def-use", which covers:

    - **Strong uses**: any ``SymbolRef`` reading the name in a command's
      RHS / condition / predicate.
    - **Defs**: ``AssignExpCmd`` / ``AssignHavocCmd`` lhs.
    - **Weak uses**: annotation references (``AnnotationCmd.weak_refs``).
      Symbols mentioned only in annotations have no behavioral role in
      the program but their declarations are kept here for traceability
      — debug-info annotations would otherwise become dangling.

    Used as a final-pass filter at the boundary between
    ``RewriteResult`` and ``render_tac_file``.
    """
    if not extra_symbols:
        return ()
    du = extract_def_use(program)
    live = set(du.symbol_to_id)
    return tuple((name, sort) for (name, sort) in extra_symbols if name in live)


def output_kind_for_path(path: Path) -> Literal["tac", "pp"]:
    """Classify ``path`` as raw-TAC or pretty-printed by suffix.

    ``.htac`` (case-insensitive) → ``"pp"``; everything else → ``"tac"``.
    Use this when a command takes ``-o PATH`` and needs to pick a
    renderer.
    """
    return "pp" if path.suffix.lower() == ".htac" else "tac"


def render_pp_lines(
    program: TacProgram, *, strip_var_suffixes: bool = True
) -> list[str]:
    """Render ``program`` as pretty-printed TAC text, line per output
    line, using the ``"human"`` printer with humanized patterns.

    Used by ``-o FILE.htac`` writers and by stdout-pp paths in
    commands like ``ctac rw``.
    """
    pp = configured_printer(
        "human", strip_var_suffixes=strip_var_suffixes, human_patterns=True
    )
    out: list[str] = []
    for b in Cfg(program).ordered_blocks():
        out.append(f"{b.id}:")
        for cmd in b.commands:
            line = pp.print_cmd(cmd)
            if line is not None and line != "":
                out.append(f"  {line}")
        term = pp_terminator_line(b, strip_var_suffixes=strip_var_suffixes)
        if term is not None:
            out.append(f"  {term}")
        elif b.successors:
            out.append(f"  goto {', '.join(b.successors)}")
        else:
            out.append("  stop")
        out.append("")
    return out


def write_program_to_path(
    *,
    output_path: Path,
    tac,
    program: TacProgram,
    extra_symbols: "tuple[tuple[str, str], ...]" = (),
) -> Literal["tac", "pp"]:
    """Write ``program`` to ``output_path`` honoring the extension
    convention. Returns the kind that was written so callers can log it.

    - ``.htac`` → pretty-printed, not round-trippable.
    - everything else → raw TAC (round-trippable, embeds
      ``tac``'s symbol table envelope plus ``extra_symbols``).
    """
    kind = output_kind_for_path(output_path)
    if kind == "pp":
        lines = render_pp_lines(program)
        text = "\n".join(lines) + ("\n" if lines else "")
    else:
        text = render_tac_file(tac, program=program, extra_symbols=extra_symbols)
    output_path.write_text(text, encoding="utf-8")
    return kind


__all__ = [
    "filter_live_extra_symbols",
    "output_kind_for_path",
    "render_pp_lines",
    "write_program_to_path",
]
