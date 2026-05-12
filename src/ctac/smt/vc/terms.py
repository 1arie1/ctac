from __future__ import annotations

from dataclasses import dataclass, field
from typing import Iterable, Sequence


@dataclass(frozen=True)
class Sort:
    text: str

    def smt(self) -> str:
        return self.text


Bool = Sort("Bool")
Int = Sort("Int")


@dataclass(frozen=True)
class Term:
    text: str
    sort: Sort
    callsites: tuple[object, ...] = field(default_factory=tuple, compare=False)
    direct_callsite: object | None = field(default=None, compare=False)

    def smt(self) -> str:
        return self.text

    def __str__(self) -> str:
        return self.text


def term(text: str, sort: Sort) -> Term:
    return Term(text, sort)


def _callsites(args: Iterable[Term]) -> tuple[object, ...]:
    out: list[object] = []
    seen: set[int] = set()
    for arg in args:
        for call in arg.callsites:
            key = id(call)
            if key in seen:
                continue
            seen.add(key)
            out.append(call)
    return tuple(out)


def app(name: str, args: Sequence[Term], sort: Sort) -> Term:
    body = f"({name} {' '.join(a.smt() for a in args)})" if args else f"({name})"
    return Term(body, sort, callsites=_callsites(args))


def literal_int(value: int | str) -> Term:
    return Term(str(value), Int)


def true() -> Term:
    return Term("true", Bool)


def false() -> Term:
    return Term("false", Bool)


def eq(a: Term, b: Term) -> Term:
    return app("=", [a, b], Bool)


def add(a: Term, b: Term) -> Term:
    return app("+", [a, b], a.sort)


def sub(a: Term, b: Term) -> Term:
    return app("-", [a, b], a.sort)


def mul(a: Term, b: Term) -> Term:
    return app("*", [a, b], a.sort)


def div(a: Term, b: Term) -> Term:
    return app("div", [a, b], Int)


def mod(a: Term, b: Term) -> Term:
    return app("mod", [a, b], Int)


def le(a: Term, b: Term) -> Term:
    return app("<=", [a, b], Bool)


def lt(a: Term, b: Term) -> Term:
    return app("<", [a, b], Bool)


def ge(a: Term, b: Term) -> Term:
    return app(">=", [a, b], Bool)


def gt(a: Term, b: Term) -> Term:
    return app(">", [a, b], Bool)


def implies(a: Term, b: Term) -> Term:
    if a.text == "true":
        return b
    if a.text == "false" or b.text == "true":
        return true()
    return app("=>", [a, b], Bool)


def and_(*args: Term) -> Term:
    flat = [a for a in args if a.text != "true"]
    if any(a.text == "false" for a in flat):
        return false()
    if not flat:
        return true()
    if len(flat) == 1:
        return flat[0]
    return app("and", flat, Bool)


def or_(*args: Term) -> Term:
    flat = [a for a in args if a.text != "false"]
    if any(a.text == "true" for a in flat):
        return true()
    if not flat:
        return false()
    if len(flat) == 1:
        return flat[0]
    return app("or", flat, Bool)


def not_(a: Term) -> Term:
    if a.text == "true":
        return false()
    if a.text == "false":
        return true()
    return app("not", [a], Bool)
