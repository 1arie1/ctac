"""Semantic-ish TAC diff helpers: variable normalization and assert slicing."""

from __future__ import annotations

import difflib
import re
from dataclasses import dataclass

from ctac.ir.models import TacFile
from ctac.ast.nodes import (
    AnnotationCmd,
    ApplyExpr,
    AssertCmd,
    AssignExpCmd,
    AssignHavocCmd,
    AssumeExpCmd,
    ConstExpr,
    JumpCmd,
    JumpiCmd,
    LabelCmd,
    RawCmd,
    SymExpr,
    TacCmd,
    TacExpr,
)
from ctac.ast.pretty import configured_printer

_META_SUFFIX_RE = re.compile(r":\d+$")


@dataclass
class CmdRecord:
    block_id: str
    cmd: TacCmd
    rendered: str
    ordered_symbols: list[str]
    defs: set[str]
    uses: set[str]
    source: str | None
    ordinal: int


def _strip_meta_suffix(name: str) -> str:
    return _META_SUFFIX_RE.sub("", name.strip())


def _trim_path_left(path: str, max_chars: int) -> str:
    if len(path) <= max_chars:
        return path
    if max_chars <= 2:
        return "…"
    tail = path[-(max_chars - 2) :]
    slash = tail.find("/")
    if slash > 0:
        tail = tail[slash + 1 :]
    return "…/" + tail


def _source_for_meta(cmd: TacCmd, metas: dict[str, object], *, max_path_chars: int = 52) -> str | None:
    if cmd.meta_index is None:
        return None
    bucket = metas.get(str(cmd.meta_index))
    if not isinstance(bucket, list):
        return None
    for entry in bucket:
        if not isinstance(entry, dict):
            continue
        key = entry.get("key")
        val = entry.get("value")
        if not isinstance(key, dict) or not isinstance(val, dict):
            continue
        if key.get("name") == "cvl.range":
            sf = val.get("specFile")
            st = val.get("start")
            if isinstance(sf, str) and isinstance(st, dict) and isinstance(st.get("line"), int):
                return f"{_trim_path_left(sf, max_path_chars)}:{st['line']}"
    return None


def _expr_symbols(expr: TacExpr) -> list[str]:
    if isinstance(expr, SymExpr):
        return [_strip_meta_suffix(expr.name)]
    if isinstance(expr, ConstExpr):
        return []
    if isinstance(expr, ApplyExpr):
        out: list[str] = []
        for a in expr.args:
            out.extend(_expr_symbols(a))
        return out
    return []


def _cmd_defs_uses(cmd: TacCmd) -> tuple[set[str], set[str], list[str]]:
    defs: set[str] = set()
    uses: set[str] = set()
    ordered: list[str] = []

    def _add(xs: list[str]) -> None:
        for s in xs:
            if s not in ordered:
                ordered.append(s)

    if isinstance(cmd, AssignExpCmd):
        d = _strip_meta_suffix(cmd.lhs)
        defs.add(d)
        ordered.append(d)
        xs = _expr_symbols(cmd.rhs)
        uses.update(xs)
        _add(xs)
    elif isinstance(cmd, AssignHavocCmd):
        d = _strip_meta_suffix(cmd.lhs)
        defs.add(d)
        ordered.append(d)
    elif isinstance(cmd, AssumeExpCmd):
        xs = _expr_symbols(cmd.condition)
        uses.update(xs)
        _add(xs)
    elif isinstance(cmd, AssertCmd):
        p = _strip_meta_suffix(cmd.predicate)
        uses.add(p)
        ordered.append(p)
    elif isinstance(cmd, JumpiCmd):
        c = _strip_meta_suffix(cmd.condition)
        uses.add(c)
        ordered.append(c)
    elif isinstance(cmd, (AnnotationCmd, LabelCmd, JumpCmd, RawCmd)):
        pass

    return defs, uses, ordered


def _new_symbol_alias(sym: str, next_id: dict[str, int]) -> str:
    p = "v"
    if sym.startswith("B"):
        p = "b"
    elif sym.startswith("I"):
        p = "i"
    n = next_id[p]
    next_id[p] += 1
    return f"{p}{n}"


def _normalize_rendered(rendered: str, ordered_symbols: list[str], alias: dict[str, str], next_id: dict[str, int]) -> str:
    out = rendered
    for s in ordered_symbols:
        if s not in alias:
            alias[s] = _new_symbol_alias(s, next_id)
        a = alias[s]
        out = re.sub(rf"(?<![A-Za-z0-9_]){re.escape(s)}(?![A-Za-z0-9_])", a, out)
    return out


def collect_records(tac: TacFile) -> list[CmdRecord]:
    pp = configured_printer("human", strip_var_suffixes=True)
    out: list[CmdRecord] = []
    ordinal = 0

    for b in tac.program.blocks:
        for cmd in b.commands:
            rendered = pp.print_cmd(cmd)
            if rendered is None:
                rendered = ""
            defs, uses, ordered = _cmd_defs_uses(cmd)
            out.append(
                CmdRecord(
                    block_id=b.id,
                    cmd=cmd,
                    rendered=rendered,
                    ordered_symbols=ordered,
                    defs=defs,
                    uses=uses,
                    source=_source_for_meta(cmd, tac.metas),
                    ordinal=ordinal,
                )
            )
            ordinal += 1
    return out


def slice_records_to_assert_dependencies(records: list[CmdRecord]) -> list[CmdRecord]:
    anchors = [i for i, r in enumerate(records) if isinstance(r.cmd, AssertCmd)]
    if not anchors:
        return records

    keep = set(anchors)
    needed: set[str] = set()
    for i in anchors:
        needed |= records[i].uses

    changed = True
    while changed:
        changed = False
        for i, r in enumerate(records):
            if i in keep:
                continue
            if r.defs & needed:
                keep.add(i)
                needed = (needed - r.defs) | r.uses
                changed = True
                continue
            # Assumes contribute path constraints for symbols in the slice.
            if isinstance(r.cmd, AssumeExpCmd) and (r.uses & needed):
                keep.add(i)
                needed |= r.uses
                changed = True

    return [r for i, r in enumerate(records) if i in keep]


def render_records(
    records: list[CmdRecord],
    *,
    include_source: bool = True,
    normalize_vars: bool = True,
    include_block_id: bool = False,
) -> list[str]:
    out: list[str] = []
    alias: dict[str, str] = {}
    next_id = {"v": 0, "b": 0, "i": 0}
    for r in records:
        if include_source and r.source:
            out.append(f"[{r.source}]")
        rendered = r.rendered
        if normalize_vars and rendered:
            rendered = _normalize_rendered(rendered, r.ordered_symbols, alias, next_id)
        if include_block_id:
            line = f"{r.block_id}: {rendered}" if rendered else f"{r.block_id}: <empty>"
        else:
            line = rendered if rendered else "<empty>"
        out.append(line)
    return out


def unified_semantic_diff(a_lines: list[str], b_lines: list[str], *, a_name: str = "a", b_name: str = "b") -> list[str]:
    return list(
        difflib.unified_diff(
            a_lines,
            b_lines,
            fromfile=a_name,
            tofile=b_name,
            lineterm="",
            n=2,
        )
    )

