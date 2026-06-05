"""Strip client-specific metadata from a TAC file.

Client TAC dumps carry identifying metadata: spec file paths, verbatim
source snippets (``sbf.source.segment.content``), mangled crate/function
names, call-trace display messages. ``strip_tac`` removes those so dumps
can be published as open benchmarks, keeping only metadata that is
generic and useful for solver work. Unknown metadata keys are dropped
(default-deny) and surfaced in the report.
"""

from __future__ import annotations

import dataclasses
import json
import re
from collections import Counter
from dataclasses import dataclass, field
from typing import Any

from ctac.ast.nodes import AnnotationCmd, AssertCmd
from ctac.ir.models import TacBlock, TacFile, TacProgram

# Metas-section entries kept by key name. Everything else — including
# keys never seen before — is dropped; default-deny is the privacy
# posture for benchmark publication.
KEEP_META_KEYS = frozenset(
    {
        "sbf.bytecode.address",
        "tac.is-temp-var",
        "tac.was.replaced.with.bool",
        "tac.non.zero.var",
        "tac.non.non_neg_var",
        "tac.is.reserved.memory.slot.var",
        "Tac.symbol.keyword",
        "overflow.rewrite",
    }
)

# Inline AnnotationCmd keys kept unconditionally (runtime intrinsics
# like __rust_alloc / CVT_alloc_slice; ctac's own DSA markers).
KEEP_ANNOTATION_KEYS = frozenset({"debug.sbf.external_call"})
KEEP_ANNOTATION_PREFIXES = ("dsa.",)

# function_start/end annotations come in two forms: a string form
# ("memcpy(dst=Stack{...})", generic) and a struct form
# (sbf.tac.SbfInlinedFunc*, carries crate/function names). Only the
# string form survives.
_STRING_FORM_KEYS = frozenset({"debug.sbf.function_start", "debug.sbf.function_end"})

# Keys we have classified as client-specific by design. Dropped keys
# outside this set are "unknown" — also dropped, but reported so the
# policy can be reviewed when new Prover versions add metadata.
KNOWN_STRIP_KEYS = frozenset(
    {
        "cvl.range",
        "sbf.source.segment",
        "sbf.rule.location",
        "tac.assert.id",
        "snippet.cmd",
        "sbf.inline.start",
        "sbf.inline.nop",
        "sbf.inline.end",
        "debug.sbf.function_start",
        "debug.sbf.function_end",
    }
)

_META_SUFFIX_RE = re.compile(r"^([A-Za-z][A-Za-z0-9_]*Cmd):\d+")
_TRAILING_MSG_RE = re.compile(r'\s+"((?:[^"\\]|\\.)*)"\s*$')


@dataclass
class StripReport:
    kept_meta: Counter = field(default_factory=Counter)
    dropped_meta: Counter = field(default_factory=Counter)
    kept_annotations: Counter = field(default_factory=Counter)
    dropped_annotations: Counter = field(default_factory=Counter)
    unknown_keys: set[str] = field(default_factory=set)
    assert_messages_replaced: int = 0
    meta_suffixes_removed: int = 0


@dataclass(frozen=True)
class StripResult:
    program: TacProgram
    metas: dict[str, Any]
    report: StripReport


def strip_tac(tac: TacFile, *, strip_all: bool = False) -> StripResult:
    """Strip client-specific metadata; return the cleaned program + metas."""
    report = StripReport()
    metas = _filter_metas(tac.metas, strip_all=strip_all, report=report)
    blocks: list[TacBlock] = []
    assert_counter = 0
    for block in tac.program.blocks:
        cmds = []
        for cmd in block.commands:
            if isinstance(cmd, AnnotationCmd):
                keep, name = _keep_annotation(cmd.payload, strip_all=strip_all)
                if not keep:
                    report.dropped_annotations[name] += 1
                    if name not in KNOWN_STRIP_KEYS and not name.startswith("<"):
                        report.unknown_keys.add(name)
                    continue
                report.kept_annotations[name] += 1
            elif isinstance(cmd, AssertCmd):
                assert_counter += 1
                if cmd.message is not None:
                    generic = f"assert {assert_counter}"
                    cmd = dataclasses.replace(
                        cmd,
                        raw=_TRAILING_MSG_RE.sub(f' "{generic}"', cmd.raw),
                        message=generic,
                    )
                    report.assert_messages_replaced += 1
            if cmd.meta_index is not None and str(cmd.meta_index) not in metas:
                cmd = dataclasses.replace(
                    cmd, raw=_META_SUFFIX_RE.sub(r"\1", cmd.raw), meta_index=None
                )
                report.meta_suffixes_removed += 1
            cmds.append(cmd)
        blocks.append(TacBlock(id=block.id, successors=list(block.successors), commands=cmds))
    return StripResult(program=TacProgram(blocks=blocks), metas=metas, report=report)


def _filter_metas(
    metas: dict[str, Any], *, strip_all: bool, report: StripReport
) -> dict[str, Any]:
    out: dict[str, Any] = {}
    for idx, entries in metas.items():
        if not isinstance(entries, list):
            # Non-.tac meta shape (e.g. sbf.json-derived) — default-deny.
            report.dropped_meta["<malformed>"] += 1
            continue
        kept = []
        for ent in entries:
            name = "<malformed>"
            if isinstance(ent, dict):
                key = ent.get("key")
                if isinstance(key, dict):
                    name = str(key.get("name", "<unnamed>"))
            if not strip_all and name in KEEP_META_KEYS:
                kept.append(ent)
                report.kept_meta[name] += 1
            else:
                report.dropped_meta[name] += 1
                if name not in KNOWN_STRIP_KEYS and name not in KEEP_META_KEYS and not name.startswith("<"):
                    report.unknown_keys.add(name)
        if kept:
            out[idx] = kept
    return out


def _keep_annotation(payload: str, *, strip_all: bool) -> tuple[bool, str]:
    """Decide an inline AnnotationCmd's fate; return ``(keep, key_name)``."""
    s = payload.strip()
    if not s.startswith("JSON"):
        return False, "<non-json>"
    try:
        obj = json.loads(s[len("JSON"):])
    except json.JSONDecodeError:
        return False, "<non-json>"
    key = obj.get("key") if isinstance(obj, dict) else None
    if not isinstance(key, dict):
        return False, "<malformed>"
    name = str(key.get("name", "<unnamed>"))
    if strip_all:
        return False, name
    if name in KEEP_ANNOTATION_KEYS:
        return True, name
    if name.startswith(KEEP_ANNOTATION_PREFIXES):
        return True, name
    if name in _STRING_FORM_KEYS and key.get("type") == "java.lang.String":
        return True, name
    return False, name
