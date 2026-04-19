from __future__ import annotations

from dataclasses import dataclass, field


@dataclass(frozen=True)
class SmtDeclaration:
    """One SMT-LIB constant declaration."""

    name: str
    sort: str


@dataclass(frozen=True)
class SmtScript:
    """Rendered SMT-LIB payload parts."""

    logic: str
    declarations: tuple[SmtDeclaration, ...] = field(default_factory=tuple)
    assertions: tuple[str, ...] = field(default_factory=tuple)
    comments: tuple[str, ...] = field(default_factory=tuple)
    check_sat: bool = True
    unsat_core: bool = False
