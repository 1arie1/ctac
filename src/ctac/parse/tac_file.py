from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any

from ctac.analysis.symbols import parse_symbol_sorts
from ctac.ast import parse_command_line
from ctac.ir.models import NBId, TacBlock, TacFile, TacProgram

_BLOCK_HEADER = re.compile(
    r"^Block\s+(?P<id>\S+)\s+Succ\s+\[(?P<succ>[^\]]*)\]\s*\{\s*$"
)


class ParseError(ValueError):
    """Invalid or unsupported `.tac` layout."""


def render_program(program: TacProgram) -> str:
    """Serialize a `TacProgram` back into TAC Program-section text."""
    lines: list[str] = ["Program {"]
    for block in program.blocks:
        succ = ", ".join(block.successors)
        lines.append(f"\tBlock {block.id} Succ [{succ}] {{")
        for cmd in block.commands:
            lines.append(f"\t\t{cmd.raw}")
        lines.append("\t}")
    lines.append("}")
    return "\n".join(lines)


def render_tac_file(
    tac: TacFile,
    *,
    program: TacProgram | None = None,
    extra_symbols: "tuple[tuple[str, str], ...] | list[tuple[str, str]]" = (),
) -> str:
    """Serialize a `TacFile`, optionally replacing only the Program section.

    ``extra_symbols`` injects ``name:sort`` lines into ``TACSymbolTable { ... }``
    before its closing ``}`` — used by rewrite passes that introduce fresh
    variables (e.g. ``ctac rw`` purification rules).
    """
    prog_text = render_program(program if program is not None else tac.program)
    sym_text = tac.symbol_table_text.rstrip("\n")
    if extra_symbols:
        sym_text = _inject_symbol_entries(sym_text, extra_symbols)
    axioms_text = tac.axioms_text.rstrip("\n")
    metas_text = "Metas " + json.dumps(tac.metas, indent=2, sort_keys=True)
    return "\n".join([sym_text, prog_text, axioms_text, metas_text]) + "\n"


def _inject_symbol_entries(
    sym_text: str,
    extras: "tuple[tuple[str, str], ...] | list[tuple[str, str]]",
) -> str:
    """Insert ``name:sort`` lines before the closing ``}`` of the symbol table."""
    lines = sym_text.split("\n")
    close_idx = -1
    for i in range(len(lines) - 1, -1, -1):
        if lines[i].strip() == "}":
            close_idx = i
            break
    if close_idx < 0:
        # No closing brace found — append at the end as a fallback.
        return sym_text + "\n" + "\n".join(f"\t{n}:{s}" for n, s in extras)
    extra_lines = [f"\t{name}:{sort}" for name, sort in extras]
    return "\n".join(lines[:close_idx] + extra_lines + lines[close_idx:])


def parse_path(
    path: str | Path, *, encoding: str = "utf-8", weak_is_strong: bool = False
) -> TacFile:
    """Parse a TAC-like input file (`.tac` or `.sbf.json`) from disk."""
    p = Path(path)
    text = p.read_text(encoding=encoding)
    return parse_string(text, path=str(p), weak_is_strong=weak_is_strong)


def parse_string(text: str, path: str | None = None, *, weak_is_strong: bool = False) -> TacFile:
    """Parse TAC-like content. Normalizes ``\\r\\n`` to ``\\n``."""
    if "\r\n" in text:
        text = text.replace("\r\n", "\n")
    if _should_parse_as_sbf_json(text, path=path):
        from ctac.parse.sbf_file import parse_sbf_string

        return parse_sbf_string(text, path=path)
    lines = text.split("\n")
    return _parse_lines(lines, path=path, weak_is_strong=weak_is_strong)


def _should_parse_as_sbf_json(text: str, *, path: str | None) -> bool:
    if path is not None and path.endswith(".sbf.json"):
        return True
    stripped = text.lstrip()
    if not stripped.startswith("{"):
        return False
    # Lightweight shape check to avoid accidental TAC mis-detection.
    return all(tok in text for tok in ('"blocks"', '"instructions"', '"entry"', '"exit"'))


def _parse_lines(lines: list[str], *, path: str | None, weak_is_strong: bool) -> TacFile:
    try:
        p_idx = _find_line(lines, "Program {")
    except ParseError as e:
        raise ParseError(f"{e} (file: {path!r})") from e

    if p_idx == 0:
        raise ParseError("Missing TACSymbolTable before Program")
    if lines[p_idx - 1].strip() != "}":
        raise ParseError("Expected closing '}' of TACSymbolTable before 'Program {'")

    symbol_table_text = "\n".join(lines[:p_idx])

    try:
        a_idx = _find_line_from(lines, p_idx + 1, "Axioms {")
    except ParseError as e:
        raise ParseError(f"{e} (file: {path!r})") from e

    if lines[a_idx - 1].strip() != "}":
        raise ParseError("Expected closing '}' of Program before 'Axioms {'")

    program_lines = lines[p_idx:a_idx]
    program = _parse_program_section(program_lines, weak_is_strong=weak_is_strong)

    try:
        m_idx = _find_line_from(lines, a_idx, "Metas")
    except ParseError as e:
        raise ParseError(f"{e} (file: {path!r})") from e

    axioms_lines = lines[a_idx:m_idx]
    axioms_text = "\n".join(axioms_lines)

    metas_tail = "\n".join(lines[m_idx:])
    metas = _parse_metas_section(metas_tail)
    return TacFile(
        symbol_table_text=symbol_table_text,
        program=program,
        axioms_text=axioms_text,
        metas=metas,
        path=path,
        symbol_sorts=parse_symbol_sorts(symbol_table_text),
    )


def _find_line(lines: list[str], wanted: str) -> int:
    for i, ln in enumerate(lines):
        if ln.strip() == wanted:
            return i
    raise ParseError(f"Missing line {wanted!r}")


def _find_line_from(lines: list[str], start: int, prefix: str) -> int:
    for i in range(start, len(lines)):
        if lines[i].lstrip().startswith(prefix):
            return i
    raise ParseError(f"Missing line starting with {prefix!r}")


def _parse_program_section(program_lines: list[str], *, weak_is_strong: bool) -> TacProgram:
    if not program_lines or program_lines[0].strip() != "Program {":
        raise ParseError("Program section must start with 'Program {'")

    blocks: list[TacBlock] = []
    i = 1
    while i < len(program_lines):
        line = program_lines[i]
        stripped = line.strip()
        m = _BLOCK_HEADER.match(stripped)
        if m:
            bid = m.group("id")
            succ_raw = m.group("succ").strip()
            successors = _parse_succ_list(succ_raw)
            i += 1
            cmds = []
            while i < len(program_lines):
                inner = program_lines[i]
                t = inner.rstrip("\n")
                if t.startswith("\t") and t.strip() == "}":
                    i += 1
                    break
                if t.startswith("\t\t"):
                    cmds.append(parse_command_line(t[2:].rstrip(), weak_is_strong=weak_is_strong))
                elif t.strip() == "}":
                    raise ParseError(
                        "Unexpected program-level '}' inside block (missing indented block close?)"
                    )
                else:
                    cmds.append(parse_command_line(t.lstrip().rstrip(), weak_is_strong=weak_is_strong))
                i += 1
            blocks.append(TacBlock(id=bid, successors=successors, commands=cmds))
            continue
        if stripped == "}":
            break
        i += 1

    return TacProgram(blocks=blocks)


def _parse_succ_list(inner: str) -> list[NBId]:
    if not inner:
        return []
    parts = [p.strip() for p in inner.split(",")]
    return [p for p in parts if p]


def _parse_metas_section(text_from_metas_line: str) -> dict[str, Any]:
    """Decode the single JSON object in the Metas section (after the ``Metas`` header)."""
    brace_pos = text_from_metas_line.find("{")
    if brace_pos == -1:
        raise ParseError("Metas section: no JSON object found")
    decoder = json.JSONDecoder()
    try:
        obj, _end = decoder.raw_decode(text_from_metas_line, brace_pos)
    except json.JSONDecodeError as e:
        raise ParseError(f"Metas JSON: {e}") from e
    if not isinstance(obj, dict):
        raise ParseError("Metas JSON must be an object at top level")
    return obj
