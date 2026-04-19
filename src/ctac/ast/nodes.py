"""TAC IR: expressions (S-expr-shaped) and commands."""

from __future__ import annotations

from abc import ABC
from dataclasses import dataclass, field
from typing import Union


class TacNode(ABC):
    """Root for IR nodes (expressions and commands)."""

    pass


# --- expressions (dump uses ``Op(arg ...)`` with space-separated args) ---


@dataclass(frozen=True)
class TacExpr(TacNode):
    """Expression in a TAC command RHS or assume."""

    pass


@dataclass(frozen=True)
class SymbolRef(TacExpr):
    """Strong variable/symbol reference token."""

    name: str


@dataclass(frozen=True)
class SymbolWeakRef(SymbolRef):
    """Weak variable/symbol reference token."""

    pass


# Backward-compatible alias used across existing code/tests.
SymExpr = SymbolRef


@dataclass(frozen=True)
class ConstExpr(TacExpr):
    """Numeric or keyword constant as printed in the dump (``0x1``, ``true``, ...)."""

    value: str


@dataclass(frozen=True)
class ApplyExpr(TacExpr):
    """``Op(e1 e2 ...)`` - operator name plus child expressions."""

    op: str
    args: tuple[TacExpr, ...] = field(default_factory=tuple)


# --- commands ---


@dataclass(frozen=True)
class TacCmd(TacNode):
    """One serialized TAC command line."""

    raw: str
    meta_index: int | None = field(default=None, kw_only=True)  # ``:475`` in dump


@dataclass(frozen=True)
class AssignExpCmd(TacCmd):
    lhs: str
    rhs: TacExpr


@dataclass(frozen=True)
class AssumeExpCmd(TacCmd):
    condition: TacExpr


@dataclass(frozen=True)
class AssignHavocCmd(TacCmd):
    lhs: str


@dataclass(frozen=True)
class AnnotationCmd(TacCmd):
    """Payload after ``AnnotationCmd`` (usually ``JSON{...}``)."""

    payload: str
    strong_refs: tuple[SymbolRef, ...] = field(default_factory=tuple)
    weak_refs: tuple[SymbolWeakRef, ...] = field(default_factory=tuple)


@dataclass(frozen=True)
class LabelCmd(TacCmd):
    text: str


@dataclass(frozen=True)
class JumpCmd(TacCmd):
    target: str


@dataclass(frozen=True)
class JumpiCmd(TacCmd):
    """Conditional edge: ``then_blk``, ``else_blk``, condition symbol."""

    then_target: str
    else_target: str
    condition: str


@dataclass(frozen=True)
class AssertCmd(TacCmd):
    predicate: str
    message: str | None


@dataclass(frozen=True)
class RawCmd(TacCmd):
    """Fallback when the line does not match a known command shape."""

    head: str
    tail: str


CmdUnion = Union[
    AssignExpCmd,
    AssumeExpCmd,
    AssignHavocCmd,
    AnnotationCmd,
    LabelCmd,
    JumpCmd,
    JumpiCmd,
    AssertCmd,
    RawCmd,
]
