"""Register numbering and Lean-identifier naming for the Lean emitters.

The deep embedding numbers int and bool registers in *separate*
namespaces (first-definition order) and refers to blocks by their index
in program order. The shallow embedding reuses the source names,
sanitized against Lean keywords and collisions.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path

from ctac.ttac import ast
from ctac.ttac.analysis.defuse import cmd_defs
from ctac.ttac.ast import Ty


@dataclass(frozen=True)
class Numbering:
    int_regs: dict[str, int]
    bool_regs: dict[str, int]
    block_index: dict[str, int]
    entry_index: int


def build_numbering(program: ast.Program, types: dict[str, Ty]) -> Numbering:
    int_regs: dict[str, int] = {}
    bool_regs: dict[str, int] = {}
    for block in program.blocks:
        for cmd in block.commands:
            for target in cmd_defs(cmd):
                regs = int_regs if types[target.name] is Ty.INT else bool_regs
                if target.name not in regs:
                    regs[target.name] = len(regs)
    block_index = {b.label: i for i, b in enumerate(program.blocks)}
    assert program.entry is not None
    return Numbering(
        int_regs=int_regs,
        bool_regs=bool_regs,
        block_index=block_index,
        entry_index=block_index[program.entry],
    )


# Lean keywords plus core names a shadowing binder would break. ttac
# identifiers are [A-Za-z_][A-Za-z0-9_]*, so mangling only ever appends.
_LEAN_RESERVED = frozenset({
    "_", "at", "axiom", "abbrev", "and", "break", "by", "calc", "catch",
    "class", "continue", "def", "deriving", "do", "else", "end", "example",
    "exists", "finally", "for", "from", "fun", "have", "if", "import", "in",
    "inductive", "instance", "let", "macro", "match", "mutual", "namespace",
    "not", "open", "or", "return", "section", "show", "sorry", "structure",
    "then", "theorem", "try", "universe", "variable", "where", "while",
    "with", "true", "false",
    "Bool", "Int", "Nat", "Prop", "True", "False", "Ttac",
})


def lean_ident(name: str, taken: set[str]) -> str:
    """Pick a Lean-safe identifier for ``name``, record it in ``taken``."""
    cand = name
    if cand in _LEAN_RESERVED:
        cand = cand + "_"
    if cand in taken:
        i = 2
        while f"{cand}_{i}" in taken:
            i += 1
        cand = f"{cand}_{i}"
    taken.add(cand)
    return cand


@dataclass(frozen=True)
class ShallowNames:
    block_defs: dict[str, str]  # block label -> ok_* def name
    regs: dict[str, str]  # ttac register name -> Lean binder name


def build_shallow_names(program: ast.Program, numbering: Numbering) -> ShallowNames:
    # Block-def names are claimed first so a register can never shadow a
    # def it appears next to; registers follow in numbering order.
    taken: set[str] = set()
    block_defs = {
        b.label: lean_ident(f"ok_{b.label}", taken) for b in program.blocks
    }
    regs: dict[str, str] = {}
    for name in (*numbering.int_regs, *numbering.bool_regs):
        regs[name] = lean_ident(name, taken)
    return ShallowNames(block_defs=block_defs, regs=regs)


def module_name_for(file: str) -> str:
    """Derive a Lean module name from the input path (stdin -> ``Prog``)."""
    if file == "-":
        return "Prog"
    parts = [p for p in re.split(r"[^0-9A-Za-z]+", Path(file).stem) if p]
    name = "".join(p[:1].upper() + p[1:] for p in parts)
    if not name:
        return "Prog"
    if name[0].isdigit():
        name = "P" + name
    return name
