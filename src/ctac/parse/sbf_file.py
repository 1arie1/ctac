from __future__ import annotations

import json
import re
from pathlib import Path

from ctac.ast.nodes import (
    ApplyExpr,
    AssignExpCmd,
    AssignHavocCmd,
    AssertCmd,
    AssumeExpCmd,
    ConstExpr,
    JumpCmd,
    JumpiCmd,
    RawCmd,
    SymbolRef,
    TacCmd,
    TacExpr,
)
from ctac.ir.models import TacBlock, TacFile, TacProgram
from ctac.parse.tac_file import ParseError

_COMMENT_RE = re.compile(r"\s*/\*.*?\*/")
_ASSIGN_RE = re.compile(r"^(?P<lhs>\S+)\s*=\s*(?P<rhs>.+)$")
_IF_GOTO_RE = re.compile(
    r"^if\s*\((?P<cond>.+)\)\s*then\s*goto\s+(?P<t>\S+)(?:\s+else\s+goto\s+(?P<f>\S+))?$"
)
_GOTO_RE = re.compile(r"^goto\s+(?P<dst>\S+)$")
_ASSUME_RE = re.compile(r"^assume\((?P<cond>.+)\)$")
_ASSERT_RE = re.compile(r"^assert\((?P<cond>.+)\)$")
_CALL_RE = re.compile(r"^call\s+(?P<name>\S+)$")
_CALLX_RE = re.compile(r"^callx\s+(?P<reg>\S+)$")
_UNARY_RE = re.compile(r"^(?P<op>be16|be32|be64|le16|le32|le64|neg)\((?P<arg>.+)\)$")
_SELECT_RE = re.compile(r"^select\((?P<cond>.+),\s*(?P<t>[^,]+),\s*(?P<f>[^,]+)\)$")
_BIN_RE = re.compile(
    r"^(?P<a>\S+)\s+(?P<op>\+|-|\*|/|%|or|and|xor|lsh|lrsh|arsh)\s+(?P<b>.+)$"
)
_COND_RE = re.compile(
    r"^(?P<a>\S+)\s+(?P<op>==|!=|ult|ule|ugt|uge|slt|sle|sgt|sge)\s+(?P<b>.+)$"
)
_INT_RE = re.compile(r"^-?\d+$")
_HEX_RE = re.compile(r"^-?0[xX][0-9a-fA-F]+$")
_REG_TYPED_RE = re.compile(r"^(r\d+):.+$")

_BIN_OPS: dict[str, str] = {
    "+": "Add",
    "-": "Sub",
    "*": "Mul",
    "/": "Div",
    "%": "Mod",
    "or": "BWOr",
    "and": "BWAnd",
    "xor": "BWXOr",
    "lsh": "ShiftLeft",
    "lrsh": "ShiftRightLogical",
    "arsh": "ShiftRightArithmetical",
}
_COND_OPS: dict[str, str] = {
    "==": "Eq",
    "ult": "Lt",
    "ule": "Le",
    "ugt": "Gt",
    "uge": "Ge",
    "slt": "Slt",
    "sle": "Sle",
    "sgt": "Sgt",
    "sge": "Sge",
}


def parse_sbf_path(path: str | Path, *, encoding: str = "utf-8") -> TacFile:
    p = Path(path)
    text = p.read_text(encoding=encoding)
    return parse_sbf_string(text, path=str(p))


def parse_sbf_string(text: str, path: str | None = None) -> TacFile:
    try:
        root = json.loads(text)
    except json.JSONDecodeError as e:
        raise ParseError(f"invalid SBF JSON: {e}") from e
    if not isinstance(root, dict):
        raise ParseError("SBF JSON must be an object")

    blocks_val = root.get("blocks")
    if not isinstance(blocks_val, list):
        raise ParseError("SBF JSON missing 'blocks' array")

    blocks: list[TacBlock] = []
    for bidx, block_obj in enumerate(blocks_val):
        if not isinstance(block_obj, dict):
            raise ParseError(f"block[{bidx}] must be an object")
        label = block_obj.get("label")
        if not isinstance(label, str) or not label:
            raise ParseError(f"block[{bidx}] missing non-empty string 'label'")
        succ_raw = block_obj.get("successors")
        if not isinstance(succ_raw, list) or any(not isinstance(x, str) for x in succ_raw):
            raise ParseError(f"block[{bidx}] has invalid 'successors' list")
        insts_raw = block_obj.get("instructions")
        if not isinstance(insts_raw, list):
            raise ParseError(f"block[{bidx}] has invalid 'instructions' list")

        commands: list[TacCmd] = []
        for iidx, inst_obj in enumerate(insts_raw):
            if not isinstance(inst_obj, dict):
                raise ParseError(f"block[{bidx}].instructions[{iidx}] must be object")
            inst_text = inst_obj.get("inst")
            if not isinstance(inst_text, str):
                raise ParseError(f"block[{bidx}].instructions[{iidx}] missing string 'inst'")
            meta_index = inst_obj.get("meta")
            commands.append(_parse_inst_line(inst_text, meta_index=meta_index))

        blocks.append(TacBlock(id=label, successors=list(succ_raw), commands=commands))

    entry = root.get("entry")
    if isinstance(entry, str) and blocks and blocks[0].id != entry:
        by_id = {b.id: b for b in blocks}
        first = by_id.get(entry)
        if first is not None:
            reordered = [first]
            reordered.extend(b for b in blocks if b.id != entry)
            blocks = reordered

    metas = root.get("meta")
    if metas is None:
        metas = root.get("metas")
    if not isinstance(metas, dict):
        metas = {}

    return TacFile(
        symbol_table_text="",
        program=TacProgram(blocks=blocks),
        axioms_text="",
        metas=metas,
        path=path,
    )


def _parse_inst_line(raw: str, *, meta_index: object) -> TacCmd:
    mi = meta_index if isinstance(meta_index, int) else None
    core = _strip_inline_comments(raw).strip()
    if not core:
        return RawCmd(raw=raw, meta_index=mi, head="", tail="")

    # Terminators/guards
    m = _IF_GOTO_RE.match(core)
    if m:
        tdst = m.group("t")
        fdst = m.group("f")
        cond_text = _strip_types_in_text(m.group("cond"))
        return JumpiCmd(raw=raw, meta_index=mi, then_target=tdst, else_target=(fdst or ""), condition=cond_text)

    m = _GOTO_RE.match(core)
    if m:
        return JumpCmd(raw=raw, meta_index=mi, target=m.group("dst"))

    m = _ASSUME_RE.match(core)
    if m:
        return AssumeExpCmd(raw=raw, meta_index=mi, condition=_parse_condition_expr(m.group("cond")))

    m = _ASSERT_RE.match(core)
    if m:
        return AssertCmd(
            raw=raw,
            meta_index=mi,
            predicate=_parse_condition_expr(m.group("cond")),
            message=None,
        )

    # Calls/exits are currently text-only
    if core == "exit":
        return RawCmd(raw=raw, meta_index=mi, head="ExitCmd", tail=core)
    m = _CALL_RE.match(core)
    if m:
        return RawCmd(raw=raw, meta_index=mi, head="CallCmd", tail=m.group("name"))
    m = _CALLX_RE.match(core)
    if m:
        return RawCmd(raw=raw, meta_index=mi, head="CallxCmd", tail=_strip_type_suffix(m.group("reg")))

    # Assignments
    m = _ASSIGN_RE.match(core)
    if not m:
        return RawCmd(raw=raw, meta_index=mi, head=core.split()[0], tail=core)

    lhs_raw = m.group("lhs")
    rhs_raw = m.group("rhs").strip()
    lhs = _strip_type_suffix(lhs_raw)
    if rhs_raw == "havoc()":
        return AssignHavocCmd(raw=raw, meta_index=mi, lhs=lhs)

    # select(cond, t, f)
    sel = _SELECT_RE.match(rhs_raw)
    if sel:
        cond = _parse_condition_expr(sel.group("cond"))
        t_expr = _parse_value_expr(sel.group("t"))
        f_expr = _parse_value_expr(sel.group("f"))
        rhs = ApplyExpr("Ite", (cond, t_expr, f_expr))
        return AssignExpCmd(raw=raw, meta_index=mi, lhs=lhs, rhs=rhs)

    # unary op
    un = _UNARY_RE.match(rhs_raw)
    if un:
        op = un.group("op")
        arg = _parse_value_expr(un.group("arg"))
        return AssignExpCmd(raw=raw, meta_index=mi, lhs=lhs, rhs=ApplyExpr(op.capitalize(), (arg,)))

    # bin op
    b = _BIN_RE.match(rhs_raw)
    if b:
        op = _BIN_OPS.get(b.group("op"))
        if op is not None:
            a_expr = _parse_value_expr(b.group("a"))
            b_expr = _parse_value_expr(b.group("b"))
            return AssignExpCmd(raw=raw, meta_index=mi, lhs=lhs, rhs=ApplyExpr(op, (a_expr, b_expr)))

    # move-like assignment
    rhs_expr = _parse_value_expr(rhs_raw)
    return AssignExpCmd(raw=raw, meta_index=mi, lhs=lhs, rhs=rhs_expr)


def _strip_inline_comments(inst: str) -> str:
    return _COMMENT_RE.sub("", inst)


def _strip_type_suffix(tok: str) -> str:
    t = tok.strip()
    m = _REG_TYPED_RE.match(t)
    if m:
        return m.group(1)
    return t


def _parse_value_expr(tok: str) -> TacExpr:
    t = _strip_type_suffix(tok.strip())
    if t in {"true", "false"} or _INT_RE.fullmatch(t) or _HEX_RE.fullmatch(t):
        return ConstExpr(t)
    return SymbolRef(t)


def _strip_types_in_text(text: str) -> str:
    return _REG_TYPED_RE.sub(r"\1", text)


def _parse_condition_expr(text: str) -> TacExpr:
    t = text.strip()
    m = _COND_RE.match(t)
    if not m:
        return _parse_value_expr(t)
    lhs = _parse_value_expr(m.group("a"))
    rhs = _parse_value_expr(m.group("b"))
    op = m.group("op")
    if op == "!=":
        return ApplyExpr("LNot", (ApplyExpr("Eq", (lhs, rhs)),))
    smt_op = _COND_OPS.get(op)
    if smt_op is None:
        return _parse_value_expr(t)
    return ApplyExpr(smt_op, (lhs, rhs))
