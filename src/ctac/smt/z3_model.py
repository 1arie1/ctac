from __future__ import annotations

import re
from dataclasses import dataclass, field

from ctac.eval.constants import MOD_256

_TOKEN_RE = re.compile(r"\(|\)|[^\s()]+")
_NUM_RE = re.compile(r"^-?[0-9]+$")


@dataclass(frozen=True)
class Z3SatOutput:
    status: str
    model_text: str = ""
    diagnostics: list[str] = field(default_factory=list)


def parse_z3_sat_output(stdout: str) -> Z3SatOutput:
    lines = [ln.strip() for ln in stdout.splitlines() if ln.strip()]
    if not lines:
        return Z3SatOutput(status="unknown", diagnostics=["empty solver stdout"])
    status = lines[0].lower()
    model_text = "\n".join(lines[1:]) if len(lines) > 1 else ""
    return Z3SatOutput(status=status, model_text=model_text)


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


def _parse_model(model_text: str) -> list[object]:
    tokens = _tokenize(model_text)
    if not tokens:
        return []
    node, i = _parse_sexpr(tokens, 0)
    if i != len(tokens):
        raise ValueError("trailing tokens after model")
    if not isinstance(node, list):
        raise ValueError("model root must be a list")
    return node


def _eval_int(term: object, env: dict[str, int]) -> int:
    if isinstance(term, str):
        if _NUM_RE.fullmatch(term):
            return int(term, 10)
        if term in env:
            return env[term]
        raise ValueError(f"unsupported Int atom {term!r}")
    if not isinstance(term, list) or not term:
        raise ValueError("unsupported Int term")
    op = term[0]
    args = term[1:]
    if op == "-" and len(args) == 1:
        return -_eval_int(args[0], env)
    if op == "+":
        return sum(_eval_int(a, env) for a in args)
    if op == "-" and len(args) == 2:
        return _eval_int(args[0], env) - _eval_int(args[1], env)
    if op == "*" and len(args) >= 2:
        v = 1
        for a in args:
            v *= _eval_int(a, env)
        return v
    if op == "mod" and len(args) == 2:
        return _eval_int(args[0], env) % _eval_int(args[1], env)
    raise ValueError(f"unsupported Int term op {op!r}")


def _eval_bool(term: object) -> bool:
    if term == "true":
        return True
    if term == "false":
        return False
    raise ValueError(f"unsupported Bool term {term!r}")


def _sort_tag(sort: str) -> str:
    s = sort.strip().lower()
    if s == "bool":
        return "bool"
    if s == "int":
        return "int"
    if s.startswith("bv"):
        return sort
    return sort


def z3_model_to_tac_model_text(
    model_text: str,
    *,
    symbol_sort: dict[str, str],
) -> tuple[str, list[str]]:
    """
    Convert an SMT-LIB `(model ...)` into TAC model text accepted by `ctac run --model`.
    """
    warnings: list[str] = []
    root = _parse_model(model_text)
    if not root:
        raise ValueError("empty model output from solver")
    if root[0] == "model":
        items = root[1:]
    else:
        # Some z3 builds print a bare parenthesized list of define-fun entries
        # (without an outer `model` tag) for `(get-model)`.
        items = root

    defs: dict[str, tuple[str, object]] = {}
    for item in items:
        if not isinstance(item, list) or len(item) != 5:
            continue
        if item[0] != "define-fun":
            continue
        name, args, sort, body = item[1], item[2], item[3], item[4]
        if not isinstance(name, str) or not isinstance(args, list) or args:
            continue
        if not isinstance(sort, str):
            continue
        defs[name] = (sort, body)

    env: dict[str, int] = {}
    for name, (sort, body) in defs.items():
        if sort != "Int":
            continue
        try:
            env[name] = _eval_int(body, env)
        except ValueError:
            continue

    out_lines = ["TAC model begin"]
    for sym in sorted(symbol_sort):
        sort = symbol_sort[sym]
        sort_l = sort.lower()
        model_def = defs.get(sym)
        if model_def is None:
            continue
        _, body = model_def
        try:
            if sort_l == "bool":
                val = "true" if _eval_bool(body) else "false"
            elif sort_l.startswith("bv"):
                val = str(_eval_int(body, env) % MOD_256)
            else:
                val = str(_eval_int(body, env))
            out_lines.append(f"{sym}:{_sort_tag(sort)} --> {val}")
        except ValueError as e:
            warnings.append(f"skip {sym}: {e}")
    out_lines.append("TAC model end")
    return "\n".join(out_lines) + "\n", warnings
