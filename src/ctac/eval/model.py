"""Parser for TAC model sections embedded in Certora report files."""

from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path

from ctac.eval.constants import MOD_256
from ctac.eval.types import Value


@dataclass(frozen=True)
class ModelParseResult:
    values: dict[str, Value]
    warnings: list[str] = field(default_factory=list)


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


def parse_tac_model_text(text: str) -> ModelParseResult:
    body = _extract_tac_model_section(text)
    values: dict[str, Value] = {}
    warnings: list[str] = []
    for idx, line in enumerate(body.splitlines(), start=1):
        parsed = _parse_model_line(line)
        if parsed is None:
            continue
        symbol, value = parsed
        if symbol in values and values[symbol] != value:
            warnings.append(f"line {idx}: duplicate symbol {symbol!r}; keeping last value")
        values[symbol] = value
    return ModelParseResult(values=values, warnings=warnings)


def parse_tac_model_path(path: Path) -> ModelParseResult:
    return parse_tac_model_text(path.read_text(encoding="utf-8"))

