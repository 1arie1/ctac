"""Parse one serialized TAC command line into a ``TacCmd`` AST node."""

from __future__ import annotations

import re

from ctac.tac_ast.nodes import (
    AnnotationCmd,
    AssertCmd,
    AssignExpCmd,
    AssignHavocCmd,
    AssumeExpCmd,
    JumpCmd,
    JumpiCmd,
    LabelCmd,
    RawCmd,
    TacCmd,
)
from ctac.tac_ast.parse_expr import parse_expr, parse_expr_safe

_CMD_HEAD = re.compile(
    r"^(?P<base>[A-Za-z][A-Za-z0-9_]*Cmd)(?::(?P<meta>\d+))?\s*(?P<rest>.*)$"
)
_LABEL = re.compile(r'^LabelCmd\s+"(.*)"\s*$', re.DOTALL)
_QUOTED_MSG = re.compile(r'^(".*")\s*$', re.DOTALL)


def parse_command_line(line: str) -> TacCmd:
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

    if base == "AssignHavocCmd":
        toks = rest.split()
        if not toks:
            return RawCmd(raw=raw, head=base, tail=rest, meta_index=meta)
        return AssignHavocCmd(raw=raw, meta_index=meta, lhs=toks[0])

    if base == "AnnotationCmd":
        return AnnotationCmd(raw=raw, meta_index=meta, payload=rest)

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
        parts = rest.split(None, 1)
        pred = parts[0] if parts else ""
        msg = parts[1].strip() if len(parts) > 1 else None
        if msg and msg.startswith('"'):
            qm = _QUOTED_MSG.match(parts[1].strip())
            if qm:
                msg = qm.group(1)[1:-1]
        return AssertCmd(raw=raw, meta_index=meta, predicate=pred, message=msg)

    return RawCmd(raw=raw, head=base, tail=rest, meta_index=meta)
