from __future__ import annotations

from typing import TYPE_CHECKING, Any

MOD_256 = 1 << 256

if TYPE_CHECKING:
    from ctac.eval.interpreter import Value


def _mk_value(kind: str, data: Any) -> "Value":
    # Late import avoids import cycle:
    # value_format -> interpreter -> tac_ast.pretty -> value_format.
    from ctac.eval.interpreter import Value

    return Value(kind, data)

SINGLE_REPR_SMALL_MAX = 15


def _typed_const_kind(tag: str) -> str:
    t = tag.lower()
    if t == "int":
        return "int"
    if t == "bool":
        return "bool"
    return "bv"


def parse_const_token(text: str) -> Value | None:
    t = text.strip()
    if t == "true":
        return _mk_value("bool", True)
    if t == "false":
        return _mk_value("bool", False)
    if t.endswith(")") and "(" in t:
        lp = t.rfind("(")
        rp = t.rfind(")")
        if rp == len(t) - 1 and lp > 0:
            base = t[:lp]
            tag = t[lp + 1 : rp]
            if base.startswith(("0x", "0X")):
                n = int(base, 16)
            else:
                n = int(base, 10)
            kind = _typed_const_kind(tag)
            if kind == "bv":
                return _mk_value("bv", n % MOD_256)
            if kind == "bool":
                return _mk_value("bool", bool(n))
            return _mk_value("int", n)
    if t.startswith(("0x", "0X")):
        return _mk_value("bv", int(t, 16) % MOD_256)
    try:
        return _mk_value("int", int(t, 10))
    except ValueError:
        return None


def _format_dec_10k(n: int) -> str:
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


def _ilog2_pow2(n: int) -> int:
    return n.bit_length() - 1


def _pow2_family_label(n: int) -> str | None:
    if n <= 0:
        return None
    if n & (n - 1) == 0:
        return f"2^{_ilog2_pow2(n)}"
    m = n - 1
    if m > 0 and (m & (m - 1) == 0):
        return f"2^{_ilog2_pow2(m)}+1"
    p = n + 1
    if p > 0 and (p & (p - 1) == 0):
        return f"2^{_ilog2_pow2(p)}-1"
    return None


def _pow10_family_label(n: int, *, near_delta: int = 9) -> str | None:
    if n <= 0:
        return None

    p = 1
    k = 0
    while p < n:
        p *= 10
        k += 1

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


def _signed_from_width(u: int, width: int) -> int:
    low = u & ((1 << width) - 1)
    sign_bit = 1 << (width - 1)
    return low - (1 << width) if (low & sign_bit) else low


def _is_zero_extended(u: int, width: int) -> bool:
    return (u >> width) == 0


def _is_sign_extended(u: int, width: int) -> bool:
    low_mask = (1 << width) - 1
    low = u & low_mask
    sign_bit = 1 << (width - 1)
    if low & sign_bit:
        ext = low | (MOD_256 - (1 << width))
    else:
        ext = low
    return ext == u


def format_value_plain(v: Value) -> str:
    if v.kind == "bool":
        return "true" if bool(v.data) else "false"
    if v.kind == "int":
        n = int(v.data)
        if -SINGLE_REPR_SMALL_MAX <= n <= SINGLE_REPR_SMALL_MAX:
            return str(n)
        p2 = _pow2_family_label(abs(n)) if n >= 0 else None
        p10 = _pow10_family_label(abs(n)) if n >= 0 else None
        dec = _format_dec_10k(n)
        if abs(n) >= 256:
            s = f"{dec} ({hex(n)})"
            if p2:
                s += f" [{p2}]"
            if p10:
                s += f" [{p10}]"
            return s
        s = dec
        if p2:
            s += f" [{p2}]"
        if p10:
            s += f" [{p10}]"
        return s

    u = int(v.data) % MOD_256
    if _is_zero_extended(u, 32) and u <= SINGLE_REPR_SMALL_MAX:
        return str(u)
    p2 = _pow2_family_label(u)
    p10 = _pow10_family_label(u)
    if _is_zero_extended(u, 32):
        s = f"{_format_dec_10k(u)} ({hex(u)})"
        if p2:
            s += f" [{p2}]"
        if p10:
            s += f" [{p10}]"
        return s
    for w in (8, 16, 32, 64):
        if _is_sign_extended(u, w):
            s = _signed_from_width(u, w)
            if s < 0:
                if -SINGLE_REPR_SMALL_MAX <= s <= SINGLE_REPR_SMALL_MAX:
                    return str(s)
                out = f"{_format_dec_10k(s)} ({hex(u)})"
                if p2:
                    out += f" [{p2}]"
                if p10:
                    out += f" [{p10}]"
                return out
            break
    out = hex(u)
    if p2:
        out += f" [{p2}]"
    if p10:
        out += f" [{p10}]"
    return out


def _is_exact_family_label(label: str | None) -> bool:
    if label is None:
        return False
    return "+" not in label and "-" not in label


def _pow2_near_label(n: int, *, max_delta: int = 16) -> str | None:
    """Return 2^k +/- d label when n is close to a power of two."""
    if n <= 0:
        return None
    if max_delta < 0:
        return None
    low_pow = 1 << (n.bit_length() - 1)
    high_pow = low_pow if low_pow == n else (low_pow << 1)
    best_label: str | None = None
    best_abs: int | None = None
    for p in (low_pow, high_pow):
        d = n - p
        ad = abs(d)
        if ad > max_delta:
            continue
        k = _ilog2_pow2(p)
        if d == 0:
            label = f"2^{k}"
        else:
            sign = "+" if d > 0 else "-"
            label = f"2^{k}{sign}{ad}"
        if best_abs is None or ad < best_abs:
            best_abs = ad
            best_label = label
    return best_label


def format_value_human_single(v: Value) -> str:
    """Single-representation formatter for human pretty-printing."""
    if v.kind == "bool":
        return "true" if bool(v.data) else "false"

    if v.kind == "int":
        n = int(v.data)
        if -SINGLE_REPR_SMALL_MAX <= n <= SINGLE_REPR_SMALL_MAX:
            return str(n)
        if n > 0:
            p2 = _pow2_near_label(n, max_delta=16)
            if p2:
                return f"[{p2}]"
            p10 = _pow10_family_label(n)
            if _is_exact_family_label(p10) and n >= 10_000:
                return f"[{p10}]"
        return _format_dec_10k(n)

    # bv
    u = int(v.data) % MOD_256
    if _is_zero_extended(u, 32) and u <= SINGLE_REPR_SMALL_MAX:
        return str(u)
    p2 = _pow2_near_label(u, max_delta=16)
    if p2:
        return f"[{p2}]"
    p10 = _pow10_family_label(u)
    if _is_exact_family_label(p10) and u >= 10_000:
        return f"[{p10}]"
    if _is_zero_extended(u, 64):
        return _format_dec_10k(u)
    return hex(u)


def format_const_token_human(token: str) -> str:
    parsed = parse_const_token(token)
    if parsed is None:
        return token
    return format_value_human_single(parsed)
