"""Control-flow graph model and filtering/rendering utilities."""

from __future__ import annotations

import json
import re
from collections.abc import Iterator
from dataclasses import dataclass
from typing import Any, Literal

import networkx as nx

from ctac.ast.models import TacBlock, TacProgram
from ctac.tac_ast.nodes import AnnotationCmd, AssertCmd, TacCmd

CfgStyle = Literal["goto", "edges", "dot"]

_FILL_ASSERT = "#ffcdd2"  # light red
_FILL_CLOG = "#b3e5fc"  # pastel blue
_FILL_DEFAULT = "#ffffff"
_CLOG_CLASS_SUFFIXES = (
    ".ScopeStart",
    ".ScopeEnd",
    ".CexPrintValues",
    ".CexPrint128BitsValue",
    ".CexPrintTag",
)


def parse_csv_ids(value: str | None) -> frozenset[str] | None:
    if value is None or not value.strip():
        return None
    return frozenset(p.strip() for p in value.split(',') if p.strip())


def _trim_path_left(path: str, max_chars: int) -> str:
    if len(path) <= max_chars:
        return path
    tail_budget = max_chars - 2
    tail = path[-tail_budget:]
    slash = tail.find("/")
    if slash > 0:
        tail = tail[slash + 1 :]
    if len(tail) + 2 > max_chars:
        tail = tail[-(max_chars - 2) :]
    return "…/" + tail


def _dot_quote_attr(s: str) -> str:
    return (
        '"'
        + s.replace("\\", "\\\\")
        .replace('"', '\\"')
        .replace("\n", "\\n")
        .replace("\r", "")
        + '"'
    )


def _dot_node_id(block_id: str) -> str:
    if re.match(r"^[A-Za-z_][A-Za-z0-9_]*$", block_id):
        return block_id
    return _dot_quote_attr(block_id)


def _cmd_is_clog(cmd: TacCmd) -> bool:
    if isinstance(cmd, AnnotationCmd):
        pl = cmd.payload.strip()
        if pl.startswith("JSON"):
            try:
                obj = json.loads(pl[4:])
            except json.JSONDecodeError:
                return False
            if not isinstance(obj, dict):
                return False
            key = obj.get("key")
            val = obj.get("value")
            if not isinstance(key, dict) or not isinstance(val, dict):
                return False
            if key.get("name") != "snippet.cmd":
                return False
            klass = val.get("#class")
            if isinstance(klass, str) and klass.endswith(_CLOG_CLASS_SUFFIXES):
                return True
        return False
    return "clog" in cmd.raw.lower()


def _meta_entry_source_lines(ent: dict[str, Any], *, max_path_chars: int) -> list[str]:
    out: list[str] = []
    key = ent.get("key")
    val = ent.get("value")
    if not isinstance(key, dict):
        return out
    name = key.get("name")

    def _add_from_range(spec_file: Any, pos: Any) -> None:
        if not isinstance(spec_file, str) or not isinstance(pos, dict):
            return
        line = pos.get("line")
        if not isinstance(line, int):
            return
        out.append(f"{_trim_path_left(spec_file, max_path_chars)}:{line}")

    if name == "cvl.range" and isinstance(val, dict):
        _add_from_range(val.get("specFile"), val.get("start"))
        end = val.get("end")
        if isinstance(end, dict):
            _add_from_range(val.get("specFile"), end)
    elif name == "sbf.source.segment" and isinstance(val, dict):
        rng = val.get("range")
        if isinstance(rng, dict):
            _add_from_range(rng.get("specFile"), rng.get("start"))
            _add_from_range(rng.get("specFile"), rng.get("end"))
    return out


def _cmd_source_lines(cmd: TacCmd, metas: dict[str, Any], *, max_path_chars: int = 72) -> list[str]:
    mi = cmd.meta_index
    if mi is None:
        return []
    bucket = metas.get(str(mi))
    if not isinstance(bucket, list):
        return []
    lines: list[str] = []
    for ent in bucket:
        if isinstance(ent, dict):
            lines.extend(_meta_entry_source_lines(ent, max_path_chars=max_path_chars))
    return lines


def _block_source_tooltip(block: TacBlock, metas: dict[str, Any]) -> str | None:
    seen: set[str] = set()
    ordered: list[str] = []
    for cmd in block.commands:
        for ln in _cmd_source_lines(cmd, metas):
            if ln not in seen:
                seen.add(ln)
                ordered.append(ln)
    if not ordered:
        return None
    return "\n".join(ordered)


def _block_has_assert(block: TacBlock) -> bool:
    return any(isinstance(c, AssertCmd) for c in block.commands)


def _block_has_clog(block: TacBlock) -> bool:
    return any(_cmd_is_clog(c) for c in block.commands)


@dataclass(frozen=True)
class CfgFilter:
    """Library-level CFG filter spec (intersection semantics)."""

    to_id: str | None = None
    from_id: str | None = None
    only_ids: frozenset[str] | None = None
    id_contains: str | None = None
    id_regex: str | None = None
    cmd_contains: str | None = None
    exclude_ids: frozenset[str] | None = None

    def any_active(self) -> bool:
        return any(
            (
                self.to_id,
                self.from_id,
                self.only_ids,
                self.id_contains,
                self.id_regex,
                self.cmd_contains,
                self.exclude_ids,
            )
        )


@dataclass
class Cfg:
    """CFG wrapper around a `TacProgram` with graph/filter/render helpers."""

    program: TacProgram

    @property
    def blocks(self) -> list[TacBlock]:
        return self.program.blocks

    @staticmethod
    def parse_csv_ids(value: str | None) -> frozenset[str] | None:
        return parse_csv_ids(value)

    def to_digraph(self) -> nx.DiGraph:
        g = nx.DiGraph()
        for b in self.program.blocks:
            g.add_node(b.id)
        for b in self.program.blocks:
            for s in b.successors:
                g.add_edge(b.id, s)
        return g

    def ordered_blocks(self) -> list[TacBlock]:
        """Return blocks in topological/SCC order with file-order stability."""
        if not self.program.blocks:
            return []

        by_id = {b.id: b for b in self.program.blocks}
        file_pos = {b.id: i for i, b in enumerate(self.program.blocks)}
        g = self.to_digraph()
        g.remove_edges_from([(u, v) for u, v in g.edges() if v not in by_id])

        # Fast path for DAGs.
        if nx.is_directed_acyclic_graph(g):
            ids = list(nx.lexicographical_topological_sort(g, key=lambda n: file_pos.get(n, 10**9)))
            return [by_id[i] for i in ids if i in by_id]

        # Cyclic case: order SCC DAG topologically, keep file order inside each SCC.
        cg = nx.condensation(g)
        blocks_by_comp: dict[int, list[str]] = {}
        for nid, comp in cg.nodes(data=True):
            members = comp.get("members", set())
            if isinstance(members, set):
                mids = sorted((m for m in members if m in by_id), key=lambda x: file_pos.get(x, 10**9))
                blocks_by_comp[nid] = mids
            else:
                blocks_by_comp[nid] = []
        ordered_ids: list[str] = []
        for cid in nx.lexicographical_topological_sort(cg):
            ordered_ids.extend(blocks_by_comp.get(cid, []))
        return [by_id[i] for i in ordered_ids if i in by_id]

    def resolve_keep_ids(self, flt: CfgFilter) -> tuple[set[str], list[str]]:
        warnings: list[str] = []
        known = {b.id for b in self.program.blocks}
        g = self.to_digraph()

        if flt.to_id is not None and flt.to_id not in known:
            raise ValueError(f"unknown block for --to: {flt.to_id!r}")
        if flt.from_id is not None and flt.from_id not in known:
            raise ValueError(f"unknown block for --from: {flt.from_id!r}")

        structural: list[set[str]] = []
        if flt.only_ids is not None:
            unknown = sorted(flt.only_ids - known)
            if unknown:
                warnings.append(f"--only ignores unknown block id(s): {', '.join(unknown)}")
            structural.append(set(flt.only_ids) & known)
        if flt.to_id is not None:
            structural.append({flt.to_id} | nx.ancestors(g, flt.to_id))
        if flt.from_id is not None:
            structural.append({flt.from_id} | nx.descendants(g, flt.from_id))

        keep = set.intersection(*structural) if structural else set(known)

        if flt.id_contains is not None:
            keep = {i for i in keep if flt.id_contains in i}

        if flt.id_regex is not None:
            try:
                rx = re.compile(flt.id_regex)
            except re.error as e:
                raise ValueError(f"invalid --id-regex: {e}") from e
            keep = {i for i in keep if rx.search(i) is not None}

        if flt.cmd_contains is not None:
            by = self.program.block_by_id()
            keep = {i for i in keep if any(flt.cmd_contains in c.raw for c in by[i].commands)}

        if flt.exclude_ids is not None:
            unknown_ex = sorted(flt.exclude_ids - known)
            if unknown_ex:
                warnings.append(f"--exclude ignores unknown block id(s): {', '.join(unknown_ex)}")
            keep -= set(flt.exclude_ids)

        return keep, warnings

    def filtered(self, flt: CfgFilter) -> tuple["Cfg", list[str]]:
        if not flt.any_active():
            return Cfg(self.program), []
        keep, warnings = self.resolve_keep_ids(flt)
        blocks: list[TacBlock] = []
        for b in self.program.blocks:
            if b.id not in keep:
                continue
            succ = [s for s in b.successors if s in keep]
            blocks.append(TacBlock(id=b.id, successors=succ, commands=list(b.commands)))
        return Cfg(TacProgram(blocks=blocks)), warnings

    def iter_dot(
        self,
        metas: dict[str, Any] | None,
        *,
        max_blocks: int | None = None,
        check_refs: bool = True,
    ) -> Iterator[str]:
        """Emit Graphviz ``digraph`` lines (node label = block id only)."""
        m = metas if metas is not None else {}
        if not self.program.blocks:
            yield "// (no basic blocks to show)"
            yield "digraph cfg { }"
            return

        known = {b.id for b in self.program.blocks}
        by_id = self.program.block_by_id()
        ordered = self.ordered_blocks()
        blocks_slice: list[TacBlock] = []
        for b in ordered:
            if max_blocks is not None and len(blocks_slice) >= max_blocks:
                break
            blocks_slice.append(b)

        node_ids: set[str] = {b.id for b in blocks_slice}
        for b in blocks_slice:
            for s in b.successors:
                if s in known:
                    node_ids.add(s)

        dangling = 0
        for b in blocks_slice:
            for s in b.successors:
                if s not in known:
                    dangling += 1

        yield "digraph cfg {"
        yield "  graph [rankdir=TB];"
        yield '  node [shape=oval, fontname="Helvetica"];'

        first = self.program.blocks[0].id
        yield f"  // entry (heuristic: first block in file order): {first}"

        for nid in sorted(node_ids):
            blk = by_id.get(nid)
            fillcolor = _FILL_DEFAULT
            if blk is not None:
                if _block_has_assert(blk):
                    fillcolor = _FILL_ASSERT
                elif _block_has_clog(blk):
                    fillcolor = _FILL_CLOG
            attrs: list[str] = [f"label={_dot_quote_attr(nid)}", f'fillcolor="{fillcolor}"', "style=filled"]
            if blk is not None:
                tip = _block_source_tooltip(blk, m)
                if tip:
                    attrs.append(f"tooltip={_dot_quote_attr(tip)}")
            yield f"  {_dot_node_id(nid)} [{', '.join(attrs)}];"

        for b in blocks_slice:
            for s in b.successors:
                if s not in node_ids:
                    continue
                yield f"  {_dot_node_id(b.id)} -> {_dot_node_id(s)};"

        if max_blocks is not None and len(blocks_slice) < len(ordered):
            rest = len(ordered) - len(blocks_slice)
            yield f"  // truncated: {rest} more block(s) not shown (--max-blocks {max_blocks})"

        if check_refs and dangling:
            yield f"  // warning: {dangling} edge(s) target block id(s) not present in this program"

        yield "}"

    def iter_lines(
        self,
        *,
        style: Literal["goto", "edges"] = "goto",
        max_blocks: int | None = None,
        check_refs: bool = True,
    ) -> Iterator[str]:
        if not self.program.blocks:
            yield '# (no basic blocks to show)'
            return

        known = {b.id for b in self.program.blocks}
        dangling = 0

        yield f"# entry (heuristic: first block in file order): {self.program.blocks[0].id}"
        yield ''

        shown = 0
        for b in self.ordered_blocks():
            if max_blocks is not None and shown >= max_blocks:
                rest = len(self.program.blocks) - shown
                yield f"# ... truncated: {rest} more block(s) not listed (--max-blocks {max_blocks})"
                break

            for s in b.successors:
                if s not in known:
                    dangling += 1

            if style == 'goto':
                yield f"{b.id}:"
                if b.successors:
                    yield f"  goto {', '.join(b.successors)}"
                else:
                    yield '  stop'
                yield ''
            elif style == 'edges':
                if not b.successors:
                    yield f"# {b.id} (no successors)"
                else:
                    for s in b.successors:
                        yield f"{b.id} -> {s}"
            else:
                raise ValueError(f"unknown CFG style: {style!r}")
            shown += 1

        if check_refs and dangling:
            yield f"# warning: {dangling} edge(s) target block id(s) not present in this program"


# Compatibility wrappers for existing callers/tests

def program_digraph(program: TacProgram) -> nx.DiGraph:
    return Cfg(program).to_digraph()


def resolve_cfg_keep_ids(
    program: TacProgram,
    *,
    to_id: str | None = None,
    from_id: str | None = None,
    only_ids: frozenset[str] | None = None,
    id_contains: str | None = None,
    id_regex: str | None = None,
    cmd_contains: str | None = None,
    exclude_ids: frozenset[str] | None = None,
) -> tuple[set[str], list[str]]:
    return Cfg(program).resolve_keep_ids(
        CfgFilter(
            to_id=to_id,
            from_id=from_id,
            only_ids=only_ids,
            id_contains=id_contains,
            id_regex=id_regex,
            cmd_contains=cmd_contains,
            exclude_ids=exclude_ids,
        )
    )


def filtered_program(program: TacProgram, keep: set[str]) -> TacProgram:
    blocks: list[TacBlock] = []
    for b in program.blocks:
        if b.id not in keep:
            continue
        succ = [s for s in b.successors if s in keep]
        blocks.append(TacBlock(id=b.id, successors=succ, commands=list(b.commands)))
    return TacProgram(blocks=blocks)


def iter_cfg_lines(
    program: TacProgram,
    *,
    style: Literal["goto", "edges"] = "goto",
    max_blocks: int | None = None,
    check_refs: bool = True,
) -> Iterator[str]:
    yield from Cfg(program).iter_lines(style=style, max_blocks=max_blocks, check_refs=check_refs)


def iter_cfg_dot(
    program: TacProgram,
    metas: dict[str, Any] | None,
    *,
    max_blocks: int | None = None,
    check_refs: bool = True,
) -> Iterator[str]:
    yield from Cfg(program).iter_dot(metas, max_blocks=max_blocks, check_refs=check_refs)
