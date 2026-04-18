"""CFG-first fuzzy block matching for TAC programs."""

from __future__ import annotations

import difflib
import json
from collections import Counter
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

from ctac.ir.models import TacFile, TacProgram
from ctac.diff.semantic import collect_records, render_records, unified_semantic_diff
from ctac.ast.nodes import (
    AnnotationCmd,
    ApplyExpr,
    AssignExpCmd,
    AssumeExpCmd,
    ConstExpr,
    TacCmd,
    TacExpr,
)


@dataclass
class BlockFeatures:
    block_id: str
    indegree: int
    outdegree: int
    cmd_count: int
    op_hist: Counter[str] = field(default_factory=Counter)
    const_hist: Counter[str] = field(default_factory=Counter)
    source_locs: set[str] = field(default_factory=set)
    function_names: set[str] = field(default_factory=set)
    print_tags: set[str] = field(default_factory=set)
    scope_names: set[str] = field(default_factory=set)
    bytecode_addrs: list[int] = field(default_factory=list)


@dataclass
class BlockMatch:
    left_id: str
    right_id: str
    score: float
    components: dict[str, float]


@dataclass
class MatchResult:
    matches: list[BlockMatch]
    unmatched_left: list[str]
    unmatched_right: list[str]


@dataclass
class BlockComparison:
    left_id: str
    right_id: str
    match_score: float
    similarity: float
    changed: bool
    left_lines: list[str]
    right_lines: list[str]
    diff_lines: list[str]


def _bucket_for_cmd(metas: dict[str, Any], cmd: TacCmd) -> list[dict[str, Any]]:
    if cmd.meta_index is None:
        return []
    bucket = metas.get(str(cmd.meta_index))
    if not isinstance(bucket, list):
        return []
    return [x for x in bucket if isinstance(x, dict)]


def _extract_from_meta_entry(ent: dict[str, Any], feat: BlockFeatures) -> None:
    key = ent.get("key")
    val = ent.get("value")
    if not isinstance(key, dict):
        return
    name = key.get("name")
    if name == "cvl.range" and isinstance(val, dict):
        sf = val.get("specFile")
        st = val.get("start")
        if isinstance(sf, str) and isinstance(st, dict) and isinstance(st.get("line"), int):
            feat.source_locs.add(f"{Path(sf).name}:{st['line']}")
    elif name == "sbf.bytecode.address" and isinstance(val, int):
        feat.bytecode_addrs.append(val)


def _expr_constants(expr: TacExpr) -> list[str]:
    if isinstance(expr, ConstExpr):
        t = expr.value.strip().lower()
        return [t] if t else []
    if isinstance(expr, ApplyExpr):
        out: list[str] = []
        for a in expr.args:
            out.extend(_expr_constants(a))
        return out
    return []


def _extract_cmd_constants(cmd: TacCmd) -> list[str]:
    if isinstance(cmd, AssignExpCmd):
        return _expr_constants(cmd.rhs)
    if isinstance(cmd, AssumeExpCmd):
        return _expr_constants(cmd.condition)
    return []


def _snippet_info(val: dict[str, Any], feat: BlockFeatures) -> None:
    klass = val.get("#class")
    if not isinstance(klass, str):
        return
    if klass.endswith(".ScopeStart") or klass.endswith(".ScopeEnd"):
        scope = val.get("scopeName")
        if isinstance(scope, str):
            feat.scope_names.add(scope)
    if klass.endswith(".CexPrintTag"):
        msg = val.get("displayMessage")
        if isinstance(msg, str):
            feat.print_tags.add(msg)
    if klass.endswith(".CexPrintValues") or klass.endswith(".CexPrint128BitsValue"):
        msg = val.get("displayMessage")
        if isinstance(msg, str):
            feat.print_tags.add(msg)


def _extract_from_annotation_payload(payload: str, feat: BlockFeatures) -> None:
    s = payload.strip()
    if not s.startswith("JSON"):
        return
    try:
        obj = json.loads(s[4:])
    except json.JSONDecodeError:
        return
    if not isinstance(obj, dict):
        return
    key = obj.get("key")
    val = obj.get("value")
    if not isinstance(key, dict):
        return
    name = key.get("name")
    if name == "snippet.cmd" and isinstance(val, dict):
        _snippet_info(val, feat)
    elif name in ("debug.sbf.function_start", "debug.sbf.function_end"):
        if isinstance(val, str):
            feat.function_names.add(val)
        elif isinstance(val, dict):
            fn = val.get("name")
            if isinstance(fn, str):
                feat.function_names.add(fn)
    elif name == "cvl.range" and isinstance(val, dict):
        sf = val.get("specFile")
        st = val.get("start")
        if isinstance(sf, str) and isinstance(st, dict) and isinstance(st.get("line"), int):
            feat.source_locs.add(f"{Path(sf).name}:{st['line']}")


def extract_block_features(tac: TacFile) -> dict[str, BlockFeatures]:
    pred_count: Counter[str] = Counter()
    for b in tac.program.blocks:
        for s in b.successors:
            pred_count[s] += 1

    out: dict[str, BlockFeatures] = {}
    for b in tac.program.blocks:
        f = BlockFeatures(
            block_id=b.id,
            indegree=pred_count.get(b.id, 0),
            outdegree=len(b.successors),
            cmd_count=len(b.commands),
        )
        for cmd in b.commands:
            f.op_hist[type(cmd).__name__] += 1
            for c in _extract_cmd_constants(cmd):
                f.const_hist[c] += 1
            for ent in _bucket_for_cmd(tac.metas, cmd):
                _extract_from_meta_entry(ent, f)
            if isinstance(cmd, AnnotationCmd):
                _extract_from_annotation_payload(cmd.payload, f)
        out[b.id] = f
    return out


def _jaccard(a: set[str], b: set[str]) -> float:
    if not a and not b:
        return 1.0
    if not a or not b:
        return 0.0
    i = len(a & b)
    u = len(a | b)
    return i / u if u else 0.0


def _counter_overlap(a: Counter[str], b: Counter[str]) -> float:
    keys = set(a) | set(b)
    if not keys:
        return 1.0
    num = 0
    den = 0
    for k in keys:
        av = a.get(k, 0)
        bv = b.get(k, 0)
        num += min(av, bv)
        den += max(av, bv)
    return num / den if den else 0.0


def _degree_score(a: BlockFeatures, b: BlockFeatures) -> float:
    diff = abs(a.indegree - b.indegree) + abs(a.outdegree - b.outdegree)
    den = max(1, a.indegree + a.outdegree + b.indegree + b.outdegree)
    return max(0.0, 1.0 - diff / den)


def _count_score(a: int, b: int) -> float:
    den = max(1, a, b)
    return max(0.0, 1.0 - abs(a - b) / den)


def _addr_score(a: list[int], b: list[int]) -> float:
    if not a or not b:
        return 0.0
    ma = sum(a) / len(a)
    mb = sum(b) / len(b)
    d = abs(ma - mb)
    # weak signal: tolerate moderate drift between compilations
    return max(0.0, 1.0 - d / 8192.0)


def score_block_pair(
    left: BlockFeatures,
    right: BlockFeatures,
    *,
    const_weight: float = 0.20,
) -> tuple[float, dict[str, float]]:
    comps: dict[str, float] = {
        "degree": _degree_score(left, right),
        "ops": _counter_overlap(left.op_hist, right.op_hist),
        "count": _count_score(left.cmd_count, right.cmd_count),
    }

    opt: dict[str, tuple[float, float]] = {}
    if left.source_locs or right.source_locs:
        opt["source"] = (0.35, _jaccard(left.source_locs, right.source_locs))
    if left.function_names or right.function_names:
        opt["function"] = (0.22, _jaccard(left.function_names, right.function_names))
    if left.print_tags or right.print_tags:
        opt["print"] = (0.12, _jaccard(left.print_tags, right.print_tags))
    if left.scope_names or right.scope_names:
        opt["scope"] = (0.08, _jaccard(left.scope_names, right.scope_names))
    if left.const_hist or right.const_hist:
        # Strong disambiguator for near-identical CFG clones with different literal payloads.
        opt["const"] = (max(0.0, const_weight), _counter_overlap(left.const_hist, right.const_hist))
    if left.bytecode_addrs and right.bytecode_addrs:
        opt["addr"] = (0.03, _addr_score(left.bytecode_addrs, right.bytecode_addrs))

    # base structural weights always active
    weights: dict[str, float] = {"degree": 0.25, "ops": 0.25, "count": 0.10}
    for k, (w, v) in opt.items():
        weights[k] = w
        comps[k] = v

    wsum = sum(weights.values())
    if wsum <= 0:
        return 0.0, comps
    score = sum(weights[k] * comps[k] for k in weights) / wsum
    return score, comps


def match_cfg_blocks(
    left: TacFile,
    right: TacFile,
    *,
    min_score: float = 0.45,
    const_weight: float = 0.20,
) -> MatchResult:
    lf = extract_block_features(left)
    rf = extract_block_features(right)
    candidates: list[BlockMatch] = []
    for li, lbf in lf.items():
        for ri, rbf in rf.items():
            s, comps = score_block_pair(lbf, rbf, const_weight=const_weight)
            if s >= min_score:
                candidates.append(BlockMatch(left_id=li, right_id=ri, score=s, components=comps))

    const_tie_weight = max(0.0, const_weight)
    candidates.sort(
        key=lambda m: (
            m.score,
            m.components.get("source", 0.0),
            (m.components.get("const", 0.0) if const_tie_weight > 0 else 0.0),
            m.components.get("function", 0.0),
        ),
        reverse=True,
    )
    taken_l: set[str] = set()
    taken_r: set[str] = set()
    matches: list[BlockMatch] = []
    for m in candidates:
        if m.left_id in taken_l or m.right_id in taken_r:
            continue
        taken_l.add(m.left_id)
        taken_r.add(m.right_id)
        matches.append(m)

    left_ids = {b.id for b in left.program.blocks}
    right_ids = {b.id for b in right.program.blocks}
    return MatchResult(
        matches=sorted(matches, key=lambda m: m.left_id),
        unmatched_left=sorted(left_ids - taken_l),
        unmatched_right=sorted(right_ids - taken_r),
    )


def compare_matched_blocks(
    left: TacFile,
    right: TacFile,
    *,
    match_result: MatchResult,
    normalize_vars: bool = True,
    include_source: bool = False,
    drop_empty_lines: bool = True,
) -> list[BlockComparison]:
    left_records = collect_records(left)
    right_records = collect_records(right)
    left_by_block: dict[str, list] = {}
    right_by_block: dict[str, list] = {}

    for r in left_records:
        left_by_block.setdefault(r.block_id, []).append(r)
    for r in right_records:
        right_by_block.setdefault(r.block_id, []).append(r)

    out: list[BlockComparison] = []
    for m in match_result.matches:
        lrec = left_by_block.get(m.left_id, [])
        rrec = right_by_block.get(m.right_id, [])
        llines = render_records(
            lrec,
            include_source=include_source,
            normalize_vars=normalize_vars,
            include_block_id=False,
        )
        rlines = render_records(
            rrec,
            include_source=include_source,
            normalize_vars=normalize_vars,
            include_block_id=False,
        )
        if drop_empty_lines:
            llines = [ln for ln in llines if ln != "<empty>"]
            rlines = [ln for ln in rlines if ln != "<empty>"]
        diff_lines = unified_semantic_diff(
            llines,
            rlines,
            a_name=f"{m.left_id}",
            b_name=f"{m.right_id}",
        )
        similarity = difflib.SequenceMatcher(a=llines, b=rlines).ratio()
        out.append(
            BlockComparison(
                left_id=m.left_id,
                right_id=m.right_id,
                match_score=m.score,
                similarity=similarity,
                changed=bool(diff_lines),
                left_lines=llines,
                right_lines=rlines,
                diff_lines=diff_lines,
            )
        )

    out.sort(key=lambda x: (x.changed, 1.0 - x.similarity, 1.0 - x.match_score), reverse=True)
    return out

