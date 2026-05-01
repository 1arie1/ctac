"""Pure SMT-LIB text combinators.

Building-block helpers for emitting SMT-LIB Bool-valued terms with
constant-folding on the literal `true` / `false` cases. No encoder-
specific state; safe to reuse from any encoder or auxiliary module."""

from __future__ import annotations


def or_terms(terms: list[str]) -> str:
    uniq: list[str] = []
    seen: set[str] = set()
    for t in terms:
        if t in seen:
            continue
        seen.add(t)
        uniq.append(t)
    if not uniq:
        return "false"
    if "true" in uniq:
        return "true"
    uniq = [t for t in uniq if t != "false"]
    if not uniq:
        return "false"
    if len(uniq) == 1:
        return uniq[0]
    return f"(or {' '.join(uniq)})"


def and_terms(terms: list[str]) -> str:
    if not terms:
        return "true"
    out: list[str] = []
    seen: set[str] = set()
    for t in terms:
        if t in seen:
            continue
        seen.add(t)
        out.append(t)
    if "false" in out:
        return "false"
    out = [t for t in out if t != "true"]
    if not out:
        return "true"
    if len(out) == 1:
        return out[0]
    return f"(and {' '.join(out)})"


def implies(lhs: str, rhs: str) -> str:
    if lhs == "true":
        return rhs
    if lhs == "false":
        return "true"
    if rhs == "true":
        return "true"
    return f"(=> {lhs} {rhs})"


def not_term(term: str) -> str:
    if term == "true":
        return "false"
    if term == "false":
        return "true"
    return f"(not {term})"


def iff(lhs: str, rhs: str) -> str:
    if lhs == rhs:
        return "true"
    if lhs == "true":
        return rhs
    if rhs == "true":
        return lhs
    if lhs == "false":
        return not_term(rhs)
    if rhs == "false":
        return not_term(lhs)
    return f"(= {lhs} {rhs})"


def at_most_one_terms(terms: list[str]) -> list[str]:
    """Pairwise at-most-one over a list of Bool-valued terms.

    Returns a list of ``(or (not t_i) (not t_j))`` clauses, one per
    distinct pair. ``"false"`` literals and duplicates are filtered.
    Returns ``[]`` when fewer than two non-``false`` terms remain."""
    uniq: list[str] = []
    seen: set[str] = set()
    for t in terms:
        if t == "false" or t in seen:
            continue
        seen.add(t)
        uniq.append(t)
    if len(uniq) <= 1:
        return []
    out: list[str] = []
    for i in range(len(uniq)):
        for j in range(i + 1, len(uniq)):
            out.append(f"(or (not {uniq[i]}) (not {uniq[j]}))")
    return out
