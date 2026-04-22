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
    unsat_core_text: str = ""
    diagnostics: list[str] = field(default_factory=list)


def parse_z3_sat_output(stdout: str, *, unsat_core: bool = False) -> Z3SatOutput:
    lines = [ln.strip() for ln in stdout.splitlines() if ln.strip()]
    if not lines:
        return Z3SatOutput(status="unknown", diagnostics=["empty solver stdout"])
    status = lines[0].lower()
    rest = "\n".join(lines[1:]) if len(lines) > 1 else ""
    if unsat_core and status == "unsat":
        return Z3SatOutput(status=status, model_text="", unsat_core_text=rest)
    return Z3SatOutput(status=status, model_text=rest)


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


def _parse_memory_body(
    body: object, arg_name: str, env: dict[str, int]
) -> tuple[dict[int, int], int]:
    """Peel an ``(ite (= arg idx) val ...)`` chain into entries + default.

    Mirrors :func:`ctac.eval.model.parse_uf_body_as_memory` but lives here
    too so the SMT-side emitter doesn't pull the eval module in.
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
            idx = _eval_int(cond_rhs, env)
            val = _eval_int(then_term, env)
        except ValueError:
            break
        entries[idx] = val
        term = else_term
    try:
        default = _eval_int(term, env)
    except ValueError:
        default = 0
    return entries, default


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
    uf_defs: dict[str, tuple[str, object]] = {}  # name -> (arg_name, body)
    for item in items:
        if not isinstance(item, list) or len(item) != 5:
            continue
        if item[0] != "define-fun":
            continue
        name, args, sort, body = item[1], item[2], item[3], item[4]
        if not isinstance(name, str) or not isinstance(args, list):
            continue
        if not isinstance(sort, str):
            continue
        if not args:
            defs[name] = (sort, body)
            continue
        # Memory UF: single Int argument returning Int.
        if (
            len(args) == 1
            and sort == "Int"
            and isinstance(args[0], list)
            and len(args[0]) == 2
            and isinstance(args[0][0], str)
            and args[0][1] == "Int"
        ):
            uf_defs[name] = (args[0][0], body)

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
        if sort_l in ("bytemap", "ghostmap"):
            uf = uf_defs.get(sym)
            if uf is None:
                continue
            arg_name, body = uf
            try:
                entries, default = _parse_memory_body(body, arg_name, env)
            except ValueError as e:
                warnings.append(f"skip memory {sym}: {e}")
                continue
            tag = _sort_tag(sort)
            out_lines.append(f"{sym}:{tag} --> default {default}")
            for idx in sorted(entries):
                out_lines.append(f"{sym}:{tag} --> {idx} {entries[idx]}")
            continue
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
