from __future__ import annotations

import re
from typing import Any

from rich.text import Text

from ctac.ast.nodes import JumpCmd, JumpiCmd
from ctac.eval import Value
from ctac.eval.value_format import format_value_plain

MODEL_HAVOC_FALLBACK_NUM = 12_345_678
MOD_256 = 1 << 256
SINGLE_REPR_SMALL_MAX = 15

_META_SUFFIX_RE = re.compile(r":\d+$")


def strip_meta_suffix(name: str) -> str:
    return _META_SUFFIX_RE.sub("", name)


def pp_terminator_line(block: Any, *, strip_var_suffixes: bool) -> str | None:
    """Render block terminator from TAC commands, preserving jump guards."""
    term: JumpCmd | JumpiCmd | None = None
    for cmd in reversed(getattr(block, "commands", [])):
        if isinstance(cmd, (JumpCmd, JumpiCmd)):
            term = cmd
            break
    if isinstance(term, JumpiCmd):
        cond = strip_meta_suffix(term.condition) if strip_var_suffixes else term.condition
        return f"if {cond} goto {term.then_target} else {term.else_target}"
    if isinstance(term, JumpCmd):
        return f"goto {term.target}"
    return None


def coerce_value_kind(v: Value, target_kind: str) -> Value:
    if v.kind == target_kind:
        return v
    if target_kind == "bool":
        return Value("bool", bool(v.data) if v.kind == "bool" else int(v.data) != 0)
    if target_kind == "int":
        if v.kind == "bool":
            return Value("int", 1 if bool(v.data) else 0)
        return Value("int", int(v.data))
    # target_kind == "bv"
    if v.kind == "bool":
        return Value("bv", 1 if bool(v.data) else 0)
    return Value("bv", int(v.data) % MOD_256)


def values_equal(lhs: Value, rhs: Value) -> bool:
    if lhs.kind == rhs.kind:
        if lhs.kind == "bool":
            return bool(lhs.data) == bool(rhs.data)
        if lhs.kind == "bv":
            return int(lhs.data) % MOD_256 == int(rhs.data) % MOD_256
        return int(lhs.data) == int(rhs.data)
    rhs_cast = coerce_value_kind(rhs, lhs.kind)
    return values_equal(lhs, rhs_cast)


def model_fallback_value(kind: str) -> Value:
    if kind == "bool":
        return Value("bool", True)
    if kind == "int":
        return Value("int", MODEL_HAVOC_FALLBACK_NUM)
    return Value("bv", MODEL_HAVOC_FALLBACK_NUM)


def trim_path_left(path: str, max_chars: int) -> str:
    if max_chars <= 0:
        return ""
    if len(path) <= max_chars:
        return path
    if max_chars <= 2:
        return "…"
    tail_budget = max_chars - 2  # reserve for "…/"
    tail = path[-tail_budget:]
    slash = tail.find("/")
    if slash > 0:
        tail = tail[slash + 1 :]
    if len(tail) + 2 > max_chars:
        tail = tail[-(max_chars - 2) :]
    return "…/" + tail


def source_prefix_for_cmd(cmd: Any, metas: dict[str, Any], *, max_path_chars: int = 56) -> str | None:
    meta_idx = getattr(cmd, "meta_index", None)
    if meta_idx is None:
        return None
    bucket = metas.get(str(meta_idx))
    if not isinstance(bucket, list):
        return None

    def _mk_prefix(spec_file: Any, line: Any) -> str | None:
        if not isinstance(spec_file, str):
            return None
        if not isinstance(line, int):
            return None
        return f"{trim_path_left(spec_file, max_path_chars)}:{line}"

    for ent in bucket:
        if not isinstance(ent, dict):
            continue
        key = ent.get("key")
        val = ent.get("value")
        if not isinstance(key, dict):
            continue

        name = key.get("name")
        if name == "cvl.range" and isinstance(val, dict):
            start = val.get("start")
            if isinstance(start, dict):
                p = _mk_prefix(val.get("specFile"), start.get("line"))
                if p is not None:
                    return p
        if name == "sbf.source.segment" and isinstance(val, dict):
            rng = val.get("range")
            if isinstance(rng, dict):
                start = rng.get("start")
                if isinstance(start, dict):
                    p = _mk_prefix(rng.get("specFile"), start.get("line"))
                    if p is not None:
                        return p
    return None


def format_dec_10k(n: int) -> str:
    """Group decimal digits by 10_000 chunks for readability."""
    sign = "-" if n < 0 else ""
    s = str(abs(n))
    if len(s) <= 4:
        return f"{sign}{s}"
    parts: list[str] = []
    while s:
        parts.append(s[-4:])
        s = s[:-4]
    parts.reverse()
    return sign + "_".join(parts)


def ilog2_pow2(n: int) -> int:
    return n.bit_length() - 1


def pow2_family_label(n: int) -> str | None:
    """
    Human-friendly label for powers of two and near-powers.

    Returns one of:
    - ``2^k``
    - ``2^k+1``
    - ``2^k-1``
    or ``None`` if not in this family.
    """
    if n <= 0:
        return None
    if n & (n - 1) == 0:
        return f"2^{ilog2_pow2(n)}"
    m = n - 1
    if m > 0 and (m & (m - 1) == 0):
        return f"2^{ilog2_pow2(m)}+1"
    p = n + 1
    if p > 0 and (p & (p - 1) == 0):
        return f"2^{ilog2_pow2(p)}-1"
    return None


def pow10_family_label(n: int, *, near_delta: int = 9) -> str | None:
    """
    Human-friendly label for powers of ten and near-powers.

    Examples:
    - ``10^8``
    - ``10^8+4``
    - ``10^8-3``
    """
    if n <= 0:
        return None

    p = 1
    k = 0
    while p < n:
        p *= 10
        k += 1
    # Now p >= n and p == 10^k.

    best_k = k
    best_p = p
    if k > 0:
        prev_p = p // 10
        if abs(n - prev_p) <= abs(n - p):
            best_k = k - 1
            best_p = prev_p

    d = n - best_p
    if d == 0:
        return f"10^{best_k}"
    if abs(d) <= near_delta:
        sign = "+" if d > 0 else "-"
        return f"10^{best_k}{sign}{abs(d)}"
    return None


def signed_from_width(u: int, width: int) -> int:
    low = u & ((1 << width) - 1)
    sign_bit = 1 << (width - 1)
    return low - (1 << width) if (low & sign_bit) else low


def is_zero_extended(u: int, width: int) -> bool:
    return (u >> width) == 0


def is_sign_extended(u: int, width: int) -> bool:
    low_mask = (1 << width) - 1
    low = u & low_mask
    sign_bit = 1 << (width - 1)
    if low & sign_bit:
        ext = low | (MOD_256 - (1 << width))
    else:
        ext = low
    return ext == u


def format_value_rich(v: Value) -> Text:
    if v.kind == "bool":
        b = bool(v.data)
        if b:
            return Text("true", style="bold bright_green")
        return Text("false", style="bold bright_red")

    if v.kind == "int":
        n = int(v.data)
        if -SINGLE_REPR_SMALL_MAX <= n <= SINGLE_REPR_SMALL_MAX:
            return Text(str(n), style="bold bright_green")
        p2 = pow2_family_label(abs(n)) if n >= 0 else None
        p10 = pow10_family_label(abs(n)) if n >= 0 else None
        t = Text(format_dec_10k(n), style="bold bright_green")
        if abs(n) >= 256:
            t.append(" ")
            t.append(f"({hex(n)})", style="yellow")
        if p2:
            t.append(" ")
            t.append(f"[{p2}]", style="bold magenta")
        if p10:
            t.append(" ")
            t.append(f"[{p10}]", style="bold bright_blue")
        return t

    # bv
    u = int(v.data) % MOD_256
    if is_zero_extended(u, 32) and u <= SINGLE_REPR_SMALL_MAX:
        return Text(str(u), style="bold bright_green")
    p2 = pow2_family_label(u)
    p10 = pow10_family_label(u)
    if is_zero_extended(u, 32):
        t = Text(format_dec_10k(u), style="bold bright_green")
        t.append(" ")
        t.append(f"({hex(u)})", style="yellow")
        if p2:
            t.append(" ")
            t.append(f"[{p2}]", style="bold magenta")
        if p10:
            t.append(" ")
            t.append(f"[{p10}]", style="bold bright_blue")
        return t

    for w in (8, 16, 32, 64):
        if is_sign_extended(u, w):
            s = signed_from_width(u, w)
            if s < 0:
                if -SINGLE_REPR_SMALL_MAX <= s <= SINGLE_REPR_SMALL_MAX:
                    return Text(str(s), style="bold bright_red")
                t = Text(format_dec_10k(s), style="bold bright_red")
                t.append(" ")
                t.append(f"({hex(u)})", style="yellow")
                if p2:
                    t.append(" ")
                    t.append(f"[{p2}]", style="bold magenta")
                if p10:
                    t.append(" ")
                    t.append(f"[{p10}]", style="bold bright_blue")
                return t
            break

    t = Text(hex(u), style="yellow")
    if p2:
        t.append(" ")
        t.append(f"[{p2}]", style="bold magenta")
    if p10:
        t.append(" ")
        t.append(f"[{p10}]", style="bold bright_blue")
    return t


def format_value_plain_local(v: Value) -> str:
    return format_value_plain(v)
