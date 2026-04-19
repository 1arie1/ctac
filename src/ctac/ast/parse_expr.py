"""Parse TAC dump S-expression-shaped expressions (space-separated args, no commas)."""

from __future__ import annotations

import re

from ctac.ast.nodes import ApplyExpr, ConstExpr, SymbolRef, TacExpr

_CONST_BOOL = frozenset({"true", "false"})
_TYPED_CONST = re.compile(
    r"^(?P<num>(?:-?[0-9]+|0[xX][0-9a-fA-F_]+))\((?P<tag>[A-Za-z0-9_]+)\)$"
)


def _is_const_token(tok: str) -> bool:
    t = tok.strip()
    if not t:
        return False
    if t in _CONST_BOOL:
        return True
    if re.fullmatch(r"-?[0-9]+", t):
        return True
    if re.fullmatch(r"0[xX][0-9a-fA-F_]+", t):
        return True
    if _TYPED_CONST.fullmatch(t):
        return True
    return False


def _split_top_level_args(inner: str) -> list[str]:
    """Split ``inner`` at depth-0 whitespace into argument substrings."""
    inner = inner.strip()
    if not inner:
        return []
    parts: list[str] = []
    depth = 0
    start = 0
    for i, ch in enumerate(inner):
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
        elif ch.isspace() and depth == 0:
            if start < i:
                parts.append(inner[start:i].strip())
            start = i + 1
    if start < len(inner):
        parts.append(inner[start:].strip())
    return [p for p in parts if p]


def parse_expr(s: str) -> TacExpr:
    """Parse a TAC expression from a substring (RHS, assume body, ...)."""
    s = s.strip()
    if not s:
        raise ValueError("empty expression")
    if _is_const_token(s):
        return ConstExpr(s)
    if s.startswith("("):
        raise ValueError("top-level expression should not start with '(' in TAC dumps")
    if "(" not in s:
        tok = s.split()[0] if s.split() else s
        if _is_const_token(tok) and len(s.split()) <= 1:
            return ConstExpr(s if len(s.split()) <= 1 else tok)
        return SymbolRef(s.strip())
    # Op(subexpr ...)
    open_paren = s.index("(")
    op = s[:open_paren].strip()
    if not op:
        raise ValueError(f"missing operator before '(': {s!r}")
    depth = 0
    end = -1
    for i in range(open_paren, len(s)):
        if s[i] == "(":
            depth += 1
        elif s[i] == ")":
            depth -= 1
            if depth == 0:
                end = i
                break
    if end < 0:
        raise ValueError(f"unbalanced parentheses in {s!r}")
    inner = s[open_paren + 1 : end].strip()
    trailing = s[end + 1 :].strip()
    if trailing:
        raise ValueError(f"trailing junk after application in {s!r}")
    arg_strs = _split_top_level_args(inner)
    args = tuple(parse_expr(a) for a in arg_strs)
    return ApplyExpr(op=op, args=args)


def parse_expr_safe(s: str) -> TacExpr:
    """Parse or wrap whole string as a single symbol (lossy fallback)."""
    try:
        return parse_expr(s)
    except ValueError:
        return SymbolRef(s.strip())
