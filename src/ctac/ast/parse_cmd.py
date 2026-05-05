"""Parse one serialized TAC command line into a ``TacCmd`` AST node."""

from __future__ import annotations

import json
import re

from ctac.ast.nodes import (
    AnnotationCmd,
    ApplyExpr,
    AssertCmd,
    AssignExpCmd,
    AssignHavocCmd,
    AssumeExpCmd,
    JumpCmd,
    JumpiCmd,
    LabelCmd,
    RawCmd,
    SymbolRef,
    SymbolWeakRef,
    TacCmd,
)
from ctac.ast.parse_expr import parse_expr, parse_expr_safe

_CMD_HEAD = re.compile(
    r"^(?P<base>[A-Za-z][A-Za-z0-9_]*Cmd)(?::(?P<meta>\d+))?\s*(?P<rest>.*)$"
)
_LABEL = re.compile(r'^LabelCmd\s+"(.*)"\s*$', re.DOTALL)
_QUOTED_MSG = re.compile(r'^(".*")\s*$', re.DOTALL)
# Matches a trailing `"..."` message after whitespace at the end of a line.
# Used to split an AssertCmd's expression-typed predicate from its optional
# human-readable message (TAC has no `"` tokens in ordinary expressions).
_TRAILING_MSG = re.compile(r'\s+"((?:[^"\\]|\\.)*)"\s*$')
_SYMBOL_TOKEN_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*(?::\d+)?$")


def _extract_annotation_symbol_refs(
    payload: str, *, weak_is_strong: bool
) -> tuple[tuple[SymbolRef, ...], tuple[SymbolWeakRef, ...]]:
    s = payload.strip()
    if not s.startswith("JSON"):
        return (), ()
    try:
        obj = json.loads(s[4:])
    except json.JSONDecodeError:
        return (), ()
    if not isinstance(obj, dict):
        return (), ()
    key = obj.get("key")
    val = obj.get("value")
    if not isinstance(key, dict) or not isinstance(val, dict):
        return (), ()
    if key.get("name") != "snippet.cmd":
        return (), ()

    names: list[str] = []
    seen: set[str] = set()
    # Fields known to carry metadata/text; skip them to avoid false symbol matches.
    skip_keys = {"#class", "displayMessage", "scopeName", "name", "namePrefixType"}

    def _visit(v: object, parent_key: str | None = None) -> None:
        if isinstance(v, dict):
            for k, subv in v.items():
                _visit(subv, parent_key=str(k))
            return
        if isinstance(v, list):
            for ent in v:
                _visit(ent, parent_key=parent_key)
            return
        if not isinstance(v, str):
            return
        if parent_key in skip_keys:
            return
        tok = v.strip()
        if not _SYMBOL_TOKEN_RE.fullmatch(tok):
            return
        if tok in {"true", "false"}:
            return
        if tok not in seen:
            seen.add(tok)
            names.append(tok)

    _visit(val)
    if weak_is_strong:
        return tuple(SymbolRef(n) for n in names), ()
    return (), tuple(SymbolWeakRef(n) for n in names)


def parse_command_line(line: str, *, weak_is_strong: bool = False) -> TacCmd:
    raw = line.rstrip("\n")
    stripped = raw.strip()
    if not stripped:
        return RawCmd(raw=raw, head="", tail="", meta_index=None)

    m = _CMD_HEAD.match(stripped)
    if not m:
        return RawCmd(raw=raw, head=stripped.split()[0] if stripped.split() else "", tail=stripped, meta_index=None)

    base = m.group("base")
    meta = int(m["meta"]) if m.group("meta") else None
    rest = m.group("rest").strip()

    if base == "AssignExpCmd":
        parts = rest.split(None, 1)
        if len(parts) != 2:
            return RawCmd(raw=raw, head=base, tail=rest, meta_index=meta)
        lhs, rhs_s = parts[0], parts[1]
        try:
            rhs = parse_expr(rhs_s)
        except ValueError:
            rhs = parse_expr_safe(rhs_s)
        return AssignExpCmd(raw=raw, meta_index=meta, lhs=lhs, rhs=rhs)

    if base == "AssumeExpCmd":
        try:
            cond = parse_expr(rest)
        except ValueError:
            cond = parse_expr_safe(rest)
        return AssumeExpCmd(raw=raw, meta_index=meta, condition=cond)

    # Bareword forms: `AssumeCmd <sym> "msg"` and `AssumeNotCmd <sym> "msg"`
    # name a single boolean symbol (optionally followed by a quoted
    # human-readable message). We canonicalize to AssumeExpCmd at parse
    # time so downstream passes (encoder, rewriter, pretty printer) only
    # have one assume shape to handle. cmd.raw is preserved verbatim, so
    # the on-disk shape round-trips through render_program unchanged.
    if base in ("AssumeCmd", "AssumeNotCmd"):
        pred_text = rest
        tm = _TRAILING_MSG.search(pred_text)
        if tm is not None:
            pred_text = pred_text[: tm.start()].rstrip()
        toks = pred_text.split()
        if not toks:
            return RawCmd(raw=raw, head=base, tail=rest, meta_index=meta)
        sym_ref = SymbolRef(toks[0])
        cond = ApplyExpr("LNot", (sym_ref,)) if base == "AssumeNotCmd" else sym_ref
        return AssumeExpCmd(raw=raw, meta_index=meta, condition=cond)

    if base == "AssignHavocCmd":
        toks = rest.split()
        if not toks:
            return RawCmd(raw=raw, head=base, tail=rest, meta_index=meta)
        return AssignHavocCmd(raw=raw, meta_index=meta, lhs=toks[0])

    if base == "AnnotationCmd":
        strong_refs, weak_refs = _extract_annotation_symbol_refs(rest, weak_is_strong=weak_is_strong)
        return AnnotationCmd(
            raw=raw,
            meta_index=meta,
            payload=rest,
            strong_refs=strong_refs,
            weak_refs=weak_refs,
        )

    if base == "LabelCmd":
        lm = _LABEL.match(stripped)
        if lm:
            return LabelCmd(raw=raw, meta_index=meta, text=lm.group(1))
        return LabelCmd(raw=raw, meta_index=meta, text=rest)

    if base == "JumpCmd":
        if not rest:
            return RawCmd(raw=raw, head=base, tail=rest, meta_index=meta)
        return JumpCmd(raw=raw, meta_index=meta, target=rest.split()[0])

    if base == "JumpiCmd":
        toks = rest.split()
        if len(toks) != 3:
            return RawCmd(raw=raw, head=base, tail=rest, meta_index=meta)
        return JumpiCmd(
            raw=raw,
            meta_index=meta,
            then_target=toks[0],
            else_target=toks[1],
            condition=toks[2],
        )

    if base == "AssertCmd":
        # Split off the trailing `"message"` (if any), then parse what remains
        # as the predicate expression. TAC expressions never contain `"`, so
        # the trailing-quoted-string regex is unambiguous.
        msg: str | None = None
        pred_text = rest.strip()
        tm = _TRAILING_MSG.search(pred_text)
        if tm is not None:
            msg = tm.group(1)
            pred_text = pred_text[: tm.start()].rstrip()
        pred_expr = parse_expr_safe(pred_text) if pred_text else SymbolRef("")
        return AssertCmd(raw=raw, meta_index=meta, predicate=pred_expr, message=msg)

    return RawCmd(raw=raw, head=base, tail=rest, meta_index=meta)
