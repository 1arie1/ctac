"""Parsers for runtime models consumed by `ctac run`."""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from pathlib import Path

from ctac.eval.constants import MOD_256
from ctac.eval.types import Value


@dataclass(frozen=True)
class MemoryModel:
    """Model value for a bytemap/ghostmap symbol.

    ``entries`` maps index -> stored value. Reads at indices not in
    ``entries`` return ``default``. Bytemap values are integer words (the
    encoder and SMT solver both represent bytemaps as ``Int -> Int``);
    callers that want a ``bv256`` read apply ``% MOD_256`` themselves.
    """

    entries: dict[int, int]
    default: int = 0


@dataclass(frozen=True)
class TacModel:
    values: dict[str, Value]
    source_format: str = "unknown"
    status: str | None = None
    warnings: list[str] = field(default_factory=list)
    memory: dict[str, MemoryModel] = field(default_factory=dict)


# Backward-compatible alias used across existing code/tests.
ModelParseResult = TacModel


def _parse_bool_token(token: str) -> bool | None:
    t = token.strip().lower()
    if t in ("true", "1"):
        return True
    if t in ("false", "0"):
        return False
    return None


def _parse_number_token(token: str) -> int:
    t = token.strip().replace("_", "")
    if t.startswith(("0x", "0X", "-0x", "-0X")):
        return int(t, 16)
    # Support common report-style short forms like: 2^34 + 4
    t_nospace = "".join(t.split())
    if "^" in t_nospace:
        if t_nospace.startswith("2^"):
            rhs = t_nospace[2:]
            base, op, delta = _split_pow_expr(rhs)
            v = 1 << int(base, 10)
            if op == "+":
                v += int(delta, 10)
            elif op == "-":
                v -= int(delta, 10)
            return v
        if t_nospace.startswith("10^"):
            rhs = t_nospace[3:]
            base, op, delta = _split_pow_expr(rhs)
            v = 10 ** int(base, 10)
            if op == "+":
                v += int(delta, 10)
            elif op == "-":
                v -= int(delta, 10)
            return v
    return int(t, 10)


def _parse_bv_token(token: str) -> int | None:
    t = token.strip().replace("_", "")
    if t.startswith("#x"):
        return int(t[2:], 16)
    if t.startswith("#b"):
        return int(t[2:], 2)
    if t.startswith(("0x", "0X", "-0x", "-0X")):
        return int(t, 16)
    if re.fullmatch(r"-?[0-9]+", t):
        return int(t, 10)
    return None


def _split_pow_expr(rhs: str) -> tuple[str, str | None, str]:
    plus = rhs.find("+")
    minus = rhs.find("-")
    if plus >= 0 and (minus < 0 or plus < minus):
        return rhs[:plus], "+", rhs[plus + 1 :]
    if minus >= 0:
        return rhs[:minus], "-", rhs[minus + 1 :]
    return rhs, None, ""


def _kind_from_type_token(type_token: str) -> str | None:
    t = type_token.strip().lower()
    if "bool" in t:
        return "bool"
    if "bv" in t:
        return "bv"
    if "int" in t:
        return "int"
    return None


def _parse_model_line(line: str) -> tuple[str, Value] | None:
    if "-->" not in line:
        return None
    left, right = line.split("-->", 1)
    lhs = left.strip()
    rhs = right.strip()
    if not lhs or not rhs or ":" not in lhs:
        return None
    name, type_token = lhs.rsplit(":", 1)
    symbol = name.strip()
    kind = _kind_from_type_token(type_token)
    if not symbol or kind is None:
        return None

    if kind == "bool":
        b = _parse_bool_token(rhs)
        if b is None:
            return None
        return symbol, Value("bool", b)

    try:
        n = _parse_number_token(rhs)
    except ValueError:
        return None

    if kind == "int":
        return symbol, Value("int", n)
    return symbol, Value("bv", n % MOD_256)


def _parse_memory_line(line: str) -> tuple[str, object, int] | None:
    """Parse a bytemap/ghostmap entry line.

    Format: ``<name>:bytemap --> <index-or-"default"> <value>``.

    Returns ``(name, index_or_default_marker, value)`` where the index
    marker is the string ``"default"`` for default-case entries and an
    ``int`` otherwise.
    """
    if "-->" not in line:
        return None
    left, right = line.split("-->", 1)
    lhs = left.strip()
    rhs = right.strip()
    if not lhs or not rhs or ":" not in lhs:
        return None
    name, type_token = lhs.rsplit(":", 1)
    symbol = name.strip()
    kind = type_token.strip().lower()
    if not symbol or kind not in ("bytemap", "ghostmap"):
        return None
    parts = rhs.split()
    if len(parts) != 2:
        return None
    idx_tok, val_tok = parts
    try:
        val = _parse_number_token(val_tok)
    except ValueError:
        return None
    if idx_tok == "default":
        return symbol, "default", val
    try:
        return symbol, _parse_number_token(idx_tok), val
    except ValueError:
        return None


def _extract_tac_model_section(text: str) -> str:
    begin_mark = "TAC model begin"
    end_mark = "TAC model end"
    begin = text.find(begin_mark)
    if begin < 0:
        raise ValueError("missing 'TAC model begin' marker")
    end = text.find(end_mark, begin)
    if end < 0:
        raise ValueError("missing 'TAC model end' marker")
    return text[begin:end]


def parse_tac_model_text(text: str) -> TacModel:
    body = _extract_tac_model_section(text)
    values: dict[str, Value] = {}
    warnings: list[str] = []
    mem_acc: dict[str, dict[object, int]] = {}
    for idx, line in enumerate(body.splitlines(), start=1):
        mem = _parse_memory_line(line)
        if mem is not None:
            sym, idx_tok, val = mem
            mem_acc.setdefault(sym, {})[idx_tok] = val
            continue
        parsed = _parse_model_line(line)
        if parsed is None:
            continue
        symbol, value = parsed
        if symbol in values and values[symbol] != value:
            warnings.append(f"line {idx}: duplicate symbol {symbol!r}; keeping last value")
        values[symbol] = value

    memory: dict[str, MemoryModel] = {}
    for sym, slots in mem_acc.items():
        default = slots.pop("default", 0) if isinstance(slots.get("default"), int) else 0
        # After popping the default marker, every remaining key is an int.
        entries = {k: v for k, v in slots.items() if isinstance(k, int)}
        memory[sym] = MemoryModel(entries=entries, default=default)

    return TacModel(values=values, source_format="tac", warnings=warnings, memory=memory)


_TOKEN_RE = re.compile(r"\(|\)|[^\s()]+")


def _tokenize(s: str) -> list[str]:
    return _TOKEN_RE.findall(s)


def _parse_sexpr(tokens: list[str], idx: int = 0) -> tuple[object, int]:
    if idx >= len(tokens):
        raise ValueError("unexpected end of S-expression")
    tok = tokens[idx]
    if tok == "(":
        out: list[object] = []
        i = idx + 1
        while i < len(tokens) and tokens[i] != ")":
            node, i = _parse_sexpr(tokens, i)
            out.append(node)
        if i >= len(tokens) or tokens[i] != ")":
            raise ValueError("missing closing paren")
        return out, i + 1
    if tok == ")":
        raise ValueError("unexpected closing paren")
    return tok, idx + 1


def _parse_model_root(model_text: str) -> list[object]:
    tokens = _tokenize(model_text)
    if not tokens:
        return []
    node, i = _parse_sexpr(tokens, 0)
    if i != len(tokens):
        raise ValueError("trailing tokens after model")
    if not isinstance(node, list):
        raise ValueError("model root must be a list")
    return node


def _maybe_strip_solver_status_prefix(text: str) -> tuple[str | None, str]:
    lines = text.splitlines()
    idx = 0
    while idx < len(lines) and not lines[idx].strip():
        idx += 1
    if idx >= len(lines):
        return None, ""
    first = lines[idx].strip().lower()
    if first in {"sat", "unsat", "unknown", "timeout"}:
        return first, "\n".join(lines[idx + 1 :]).strip()
    return None, text.strip()


def _sort_token_to_str(sort_tok: object) -> str:
    if isinstance(sort_tok, str):
        return sort_tok
    if (
        isinstance(sort_tok, list)
        and len(sort_tok) == 3
        and sort_tok[0] == "_"
        and sort_tok[1] == "BitVec"
        and isinstance(sort_tok[2], str)
    ):
        return f"bv{sort_tok[2]}"
    return str(sort_tok)


def _eval_int_term(term: object, env: dict[str, int]) -> int:
    if isinstance(term, str):
        n = _parse_bv_token(term)
        if n is not None:
            return n
        if term in env:
            return env[term]
        raise ValueError(f"unsupported Int atom {term!r}")
    if not isinstance(term, list) or not term:
        raise ValueError("unsupported Int term")
    op = term[0]
    args = term[1:]
    if op == "-" and len(args) == 1:
        return -_eval_int_term(args[0], env)
    if op == "+":
        return sum(_eval_int_term(a, env) for a in args)
    if op == "-" and len(args) == 2:
        return _eval_int_term(args[0], env) - _eval_int_term(args[1], env)
    if op == "*" and len(args) >= 2:
        v = 1
        for a in args:
            v *= _eval_int_term(a, env)
        return v
    if op == "mod" and len(args) == 2:
        return _eval_int_term(args[0], env) % _eval_int_term(args[1], env)
    if op == "_" and len(args) == 2 and isinstance(args[0], str) and args[0].startswith("bv"):
        return int(args[0][2:], 10)
    raise ValueError(f"unsupported Int term op {op!r}")


def _eval_bool_term(term: object) -> bool:
    if term == "true":
        return True
    if term == "false":
        return False
    raise ValueError(f"unsupported Bool term {term!r}")


def parse_uf_body_as_memory(
    body: object, arg_name: str, env: dict[str, int]
) -> tuple[dict[int, int], int]:
    """Parse an ``(ite (= arg idx) val (ite ... default))`` chain.

    Returns ``(entries, default)``. Non-ite or unrecognized bodies fold
    into an empty ``entries`` with the body's constant value as the
    default (falling back to 0 when the term is unparseable).
    """
    entries: dict[int, int] = {}
    term = body
    while (
        isinstance(term, list)
        and len(term) == 4
        and term[0] == "ite"
        and isinstance(term[1], list)
        and len(term[1]) == 3
        and term[1][0] == "="
        and term[1][1] == arg_name
    ):
        cond_rhs = term[1][2]
        then_term = term[2]
        else_term = term[3]
        try:
            idx = _eval_int_term(cond_rhs, env)
            val = _eval_int_term(then_term, env)
        except ValueError:
            break
        entries[idx] = val
        term = else_term
    try:
        default = _eval_int_term(term, env)
    except ValueError:
        default = 0
    return entries, default


def parse_smt_model_text(text: str) -> TacModel:
    status, body = _maybe_strip_solver_status_prefix(text)
    if status in {"unsat", "unknown", "timeout"} and not body:
        return TacModel(values={}, source_format="smt", status=status, warnings=[])
    root = _parse_model_root(body)
    if not root:
        raise ValueError("empty SMT model")
    items = root[1:] if root and root[0] == "model" else root
    defs: dict[str, tuple[str, object]] = {}
    uf_defs: dict[str, tuple[str, object]] = {}  # name -> (arg_name, body)
    for item in items:
        if not isinstance(item, list) or len(item) != 5:
            continue
        if item[0] != "define-fun":
            continue
        name, args, sort_tok, val_term = item[1], item[2], item[3], item[4]
        if not isinstance(name, str) or not isinstance(args, list):
            continue
        sort_str = _sort_token_to_str(sort_tok)
        if not args:
            defs[name] = (sort_str, val_term)
            continue
        # Memory-shaped UF: single Int-domain argument returning Int.
        if (
            len(args) == 1
            and sort_str == "Int"
            and isinstance(args[0], list)
            and len(args[0]) == 2
            and isinstance(args[0][0], str)
            and _sort_token_to_str(args[0][1]) == "Int"
        ):
            uf_defs[name] = (args[0][0], val_term)

    env: dict[str, int] = {}
    for name, (sort, term) in defs.items():
        if sort != "Int":
            continue
        try:
            env[name] = _eval_int_term(term, env)
        except ValueError:
            continue

    values: dict[str, Value] = {}
    warnings: list[str] = []
    for name, (sort, term) in defs.items():
        sl = sort.lower()
        try:
            if sl == "bool":
                values[name] = Value("bool", _eval_bool_term(term))
            elif sl == "int":
                values[name] = Value("int", _eval_int_term(term, env))
            elif sl.startswith("bv"):
                values[name] = Value("bv", _eval_int_term(term, env) % MOD_256)
        except ValueError as e:
            warnings.append(f"skip {name}: {e}")

    memory: dict[str, MemoryModel] = {}
    for name, (arg_name, body_term) in uf_defs.items():
        try:
            entries, default = parse_uf_body_as_memory(body_term, arg_name, env)
        except ValueError as e:
            warnings.append(f"skip memory {name}: {e}")
            continue
        memory[name] = MemoryModel(entries=entries, default=default)

    return TacModel(
        values=values,
        source_format="smt",
        status=status,
        warnings=warnings,
        memory=memory,
    )


def parse_model_text(text: str) -> TacModel:
    if "TAC model begin" in text:
        return parse_tac_model_text(text)
    return parse_smt_model_text(text)


def parse_tac_model_path(path: Path) -> TacModel:
    return parse_tac_model_text(path.read_text(encoding="utf-8"))


def parse_model_path(path: Path) -> TacModel:
    return parse_model_text(path.read_text(encoding="utf-8"))

