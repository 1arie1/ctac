"""Manifest write / read / summarize for ``ctac pin``.

When ``--split`` is present, pin emits multiple ``.tac`` files plus a
``manifest.json`` capturing the source, plan, per-case kept-pred
choices, and a block-short-name table. The manifest is the
authoritative record; filenames are convenient but only meaningful
relative to it.
"""

from __future__ import annotations

import json
from collections.abc import Mapping
from dataclasses import dataclass, field
from pathlib import Path
from typing import Literal

from ctac.ast.nodes import (
    AssertCmd,
    AssignExpCmd,
    AssignHavocCmd,
    AssumeExpCmd,
    JumpCmd,
    JumpiCmd,
)
from ctac.ir.models import TacFile
from ctac.parse.tac_file import render_tac_file
from ctac.transform.pin import BlockId, Case, CaseSet
from ctac.transform.pin_naming import (
    BlockNameTable,
    shorten_block_names,
)


SCHEMA_VERSION = 1
MANIFEST_FILENAME = "manifest.json"
NameStyle = Literal["descriptive", "index"]


# -------------------------------------------------------- typed manifest


@dataclass(frozen=True)
class SplitRecord:
    block: str  # short name
    block_full: BlockId  # original id
    predecessors: tuple[str, ...]  # short names
    predecessors_full: tuple[BlockId, ...]


@dataclass(frozen=True)
class CaseRecord:
    filename: str
    kept: dict[str, str] = field(default_factory=dict)  # short -> short
    kept_full: dict[BlockId, BlockId] = field(default_factory=dict)
    blocks: int = 0
    cmds: int = 0
    dead_blocks: int = 0


@dataclass(frozen=True)
class Manifest:
    """Typed view of a pin output directory's manifest.json."""

    schema_version: int
    source: str | None
    command: str | None
    drops: tuple[str, ...]
    binds: dict[str, str]  # var name -> "true" / "false" (or other const text)
    splits: tuple[SplitRecord, ...]
    cases: tuple[CaseRecord, ...]
    block_short_names: dict[BlockId, str]
    pruned_count: int = 0

    def to_json_dict(self) -> dict:
        return {
            "schema_version": self.schema_version,
            "source": self.source,
            "command": self.command,
            "drops": list(self.drops),
            "binds": dict(self.binds),
            "splits": [
                {
                    "block": s.block,
                    "block_full": s.block_full,
                    "predecessors": list(s.predecessors),
                    "predecessors_full": list(s.predecessors_full),
                }
                for s in self.splits
            ],
            "cases": [
                {
                    "filename": c.filename,
                    "kept": dict(c.kept),
                    "kept_full": dict(c.kept_full),
                    "blocks": c.blocks,
                    "cmds": c.cmds,
                    "dead_blocks": c.dead_blocks,
                }
                for c in self.cases
            ],
            "block_short_names": dict(self.block_short_names),
            "pruned_count": self.pruned_count,
        }

    @classmethod
    def from_json_dict(cls, d: dict) -> Manifest:
        return cls(
            schema_version=int(d.get("schema_version", 0)),
            source=d.get("source"),
            command=d.get("command"),
            drops=tuple(d.get("drops", ())),
            binds=dict(d.get("binds", {})),
            splits=tuple(
                SplitRecord(
                    block=s["block"],
                    block_full=s["block_full"],
                    predecessors=tuple(s["predecessors"]),
                    predecessors_full=tuple(s["predecessors_full"]),
                )
                for s in d.get("splits", [])
            ),
            cases=tuple(
                CaseRecord(
                    filename=c["filename"],
                    kept=dict(c.get("kept", {})),
                    kept_full=dict(c.get("kept_full", {})),
                    blocks=int(c.get("blocks", 0)),
                    cmds=int(c.get("cmds", 0)),
                    dead_blocks=int(c.get("dead_blocks", 0)),
                )
                for c in d.get("cases", [])
            ),
            block_short_names=dict(d.get("block_short_names", {})),
            pruned_count=int(d.get("pruned_count", 0)),
        )


# ---------------------------------------------------------------- write


_FILENAME_MAX_LEN = 100


def _case_short_name(
    case: Case,
    name_style: NameStyle,
    case_idx: int,
    name_table: BlockNameTable,
) -> str:
    if name_style == "index":
        return f"case_{case_idx + 1:03d}"
    parts = [
        f"{name_table.short(split)}={name_table.short(kept)}"
        for split, kept in case.kept_predecessors
    ]
    desc = "__".join(parts) if parts else "case"
    if len(desc) > _FILENAME_MAX_LEN:
        return f"case_{case_idx + 1:03d}"
    return desc


def _block_count_and_cmds(program) -> tuple[int, int]:
    n_blocks = len(program.blocks)
    n_cmds = sum(len(b.commands) for b in program.blocks)
    return n_blocks, n_cmds


def write_manifest(
    case_set: CaseSet,
    out_dir: Path | str,
    *,
    source_tac: TacFile | None = None,
    source_path: str | None = None,
    command: str | None = None,
    name_style: NameStyle = "descriptive",
) -> Manifest:
    """Write each case's ``.tac`` plus ``manifest.json`` to ``out_dir``.

    ``source_tac`` (if provided) is used as the template for the
    symbol table and metas of each case file via :func:`render_tac_file`.
    Without it, the function emits programs only; downstream tools
    that require the full TAC structure will need ``source_tac``.
    """
    out_dir = Path(out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)

    # Build a single corpus of block ids spanning source + every case.
    corpus: set[BlockId] = set()
    for b in case_set.source_program.blocks:
        corpus.add(b.id)
    for c in case_set.cases:
        for split, kept in c.kept_predecessors:
            corpus.add(split)
            corpus.add(kept)
    name_table = shorten_block_names(corpus)

    # SplitRecords (short-name renderings).
    splits_records: list[SplitRecord] = []
    for split_block in case_set.plan.splits:
        # Find the predecessors as recorded in any case (they're the
        # union of "kept" over cases for this split block).
        preds: list[BlockId] = []
        seen: set[BlockId] = set()
        for c in case_set.cases:
            for s, kept in c.kept_predecessors:
                if s == split_block and kept not in seen:
                    preds.append(kept)
                    seen.add(kept)
        splits_records.append(SplitRecord(
            block=name_table.short(split_block),
            block_full=split_block,
            predecessors=tuple(name_table.short(p) for p in preds),
            predecessors_full=tuple(preds),
        ))

    # CaseRecords + per-case file emission.
    cases_records: list[CaseRecord] = []
    for idx, c in enumerate(case_set.cases):
        short = _case_short_name(c, name_style, idx, name_table)
        filename = f"{short}.tac"
        n_blocks, n_cmds = _block_count_and_cmds(c.program)
        cases_records.append(CaseRecord(
            filename=filename,
            kept={
                name_table.short(split): name_table.short(kept)
                for split, kept in c.kept_predecessors
            },
            kept_full={split: kept for split, kept in c.kept_predecessors},
            blocks=n_blocks,
            cmds=n_cmds,
            dead_blocks=len(c.dead_blocks),
        ))
        # Emit the file.
        case_path = out_dir / filename
        if source_tac is not None:
            text = render_tac_file(source_tac, program=c.program)
        else:
            from ctac.parse.tac_file import render_program
            text = render_program(c.program) + "\n"
        case_path.write_text(text)

    manifest = Manifest(
        schema_version=SCHEMA_VERSION,
        source=source_path,
        command=command,
        drops=tuple(case_set.plan.drops),
        binds={var: val.value for var, val in case_set.plan.binds},
        splits=tuple(splits_records),
        cases=tuple(cases_records),
        block_short_names={bid: name_table.short(bid) for bid in corpus},
        pruned_count=len(case_set.pruned_vacuous),
    )

    (out_dir / MANIFEST_FILENAME).write_text(
        json.dumps(manifest.to_json_dict(), indent=2, sort_keys=True) + "\n"
    )

    return manifest


# ----------------------------------------------------------------- read


def read_manifest(dir_path: Path | str) -> Manifest:
    """Parse a ``manifest.json`` in ``dir_path``. Raises ``FileNotFoundError``
    if missing, ``ValueError`` if the schema version is unsupported."""
    dir_path = Path(dir_path)
    p = dir_path / MANIFEST_FILENAME
    if not p.is_file():
        raise FileNotFoundError(f"manifest.json not found in {dir_path}")
    data = json.loads(p.read_text())
    sv = int(data.get("schema_version", 0))
    if sv != SCHEMA_VERSION:
        raise ValueError(
            f"unsupported manifest schema_version {sv} "
            f"(expected {SCHEMA_VERSION})"
        )
    return Manifest.from_json_dict(data)


# ------------------------------------------------------------- summarize


def _expand_path(path: str | None, base: Path | None) -> tuple[str, bool]:
    """Return (display_path, exists) for a source-path string."""
    if not path:
        return ("(unspecified)", True)
    p = Path(path)
    if not p.is_absolute() and base is not None:
        p2 = (base / p).resolve()
        return (str(p), p2.exists())
    return (str(p), p.exists())


def summarize_manifest(
    m: Manifest,
    *,
    plain: bool = False,
    manifest_dir: Path | str | None = None,
) -> str:
    """Render a human-readable summary of a manifest. ``plain`` strips
    decorative borders for grep-friendly output."""
    base = Path(manifest_dir) if manifest_dir is not None else None
    src_display, src_exists = _expand_path(m.source, base)
    src_marker = "" if src_exists else " (missing)"

    lines: list[str] = []
    if not plain:
        lines.append("# pin manifest")
    lines.append(f"Source:    {src_display}{src_marker}")
    if m.command:
        lines.append(f"Command:   {m.command}")
    lines.append("")
    lines.append("Operations")
    lines.append(
        "  drops:   " + (", ".join(m.drops) if m.drops else "(none)")
    )
    if m.binds:
        bind_str = ", ".join(f"{k} = {v}" for k, v in m.binds.items())
    else:
        bind_str = "(none)"
    lines.append(f"  binds:   {bind_str}")
    lines.append(f"  splits:  {len(m.splits)}")
    if m.pruned_count:
        lines.append(f"  pruned:  {m.pruned_count}")
    lines.append("")

    if m.splits:
        lines.append("Splits")
        for s in m.splits:
            lines.append(
                f"  {s.block}     ({len(s.predecessors)} preds: "
                + ", ".join(s.predecessors) + ")"
            )
        lines.append("")

    if m.cases:
        lines.append(f"Cases ({len(m.cases)} total)")
        # Compact table — filename, kept, blocks/cmds.
        widths = (
            max((len(c.filename) for c in m.cases), default=10),
            max(
                (len(_kept_str(c)) for c in m.cases),
                default=4,
            ),
        )
        header = (
            f"  {'filename':<{widths[0]}}  {'kept':<{widths[1]}}  "
            f"{'blocks':>7}  {'cmds':>7}"
        )
        if not plain:
            lines.append(header)
        for c in m.cases:
            kstr = _kept_str(c)
            lines.append(
                f"  {c.filename:<{widths[0]}}  {kstr:<{widths[1]}}  "
                f"{c.blocks:>7}  {c.cmds:>7}"
            )

    return "\n".join(lines) + "\n"


def _kept_str(c: CaseRecord) -> str:
    if not c.kept:
        return "(no splits)"
    parts = [f"{k}: {v}" for k, v in c.kept.items()]
    return "{" + ", ".join(parts) + "}"


# ------------------------------------------------------- AST module unused
# Keep imports around for editor convenience even when not directly
# referenced — these node types are part of the TAC vocabulary
# the manifest documents, even if the writer doesn't currently
# inspect them at this layer.
_ = (
    AssertCmd,
    AssignExpCmd,
    AssignHavocCmd,
    AssumeExpCmd,
    JumpCmd,
    JumpiCmd,
    Mapping,  # Re-export for type clarity in callers' eyes.
)
