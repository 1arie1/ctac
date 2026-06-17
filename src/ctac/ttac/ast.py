"""Tiny TAC (``ttac``) AST.

Frozen-dataclass node set for the source language described in
``doc/vc/``. ``ttac`` is a fragment of TAC with a different concrete
syntax (infix expressions, label-prefixed blocks, named terminators)
plus references and borrowing. This module defines only the AST; the
lexer/parser build it and the pretty-printer renders it back.
"""

from __future__ import annotations

from abc import ABC
from dataclasses import dataclass, field
from enum import Enum


class Ty(Enum):
    """The four ``ttac`` register types."""

    BOOL = "bool"
    INT = "int"
    BYTEMAP = "bytemap"
    REF = "ref"


@dataclass(frozen=True)
class Target:
    """An assignment target: a register name with an optional declared type.

    ``ty`` is ``None`` when the source omits the ``: τ`` annotation; a
    later type-inference pass fills it in.
    """

    name: str
    ty: Ty | None = None


# --- expressions ---


@dataclass(frozen=True)
class Expr(ABC):
    """Base for ``ttac`` expressions."""


@dataclass(frozen=True)
class Num(Expr):
    """Decimal integer literal."""

    value: int


@dataclass(frozen=True)
class BoolLit(Expr):
    """``true`` / ``false``."""

    value: bool


@dataclass(frozen=True)
class HavocExpr(Expr):
    """``havoc`` in expression position - an arbitrary value of the type.

    Appears nested (e.g. a ``ref`` record's ``promise`` field). The
    command form ``x := havoc`` is the dedicated :class:`Havoc` command,
    intercepted before expression parsing.
    """


@dataclass(frozen=True)
class Var(Expr):
    """Register reference (int, bool, bytemap, or ref register)."""

    name: str


@dataclass(frozen=True)
class Load(Expr):
    """``M[i]`` - read an integer from a bytemap at an index."""

    base: Expr
    index: Expr


@dataclass(frozen=True)
class Update(Expr):
    """``M[i := v]`` - bytemap value that agrees with ``base`` except at ``index``."""

    base: Expr
    index: Expr
    value: Expr


@dataclass(frozen=True)
class BinExpr(Expr):
    """Infix binary operator (``op`` is the surface token: ``+ - * / == <= < and or``)."""

    op: str
    lhs: Expr
    rhs: Expr


@dataclass(frozen=True)
class UnExpr(Expr):
    """Prefix unary operator (``op`` is ``not``)."""

    op: str
    operand: Expr


@dataclass(frozen=True)
class IfExpr(Expr):
    """Rust-style expression conditional ``if cond { then } else { els }``."""

    cond: Expr
    then: Expr
    els: Expr


@dataclass(frozen=True)
class Record(Expr):
    """``ref`` value literal ``{ addr: a, value: v, promise: p }`` (ref intro)."""

    addr: Expr
    value: Expr
    promise: Expr


@dataclass(frozen=True)
class Field(Expr):
    """Field projection ``e.addr`` / ``e.value`` / ``e.promise`` (ref elim)."""

    base: Expr
    name: str


# --- commands ---


@dataclass(frozen=True)
class Cmd(ABC):
    """Base for ``ttac`` commands (the non-terminator statements in a block)."""


@dataclass(frozen=True)
class Assign(Cmd):
    target: Target
    rhs: Expr


@dataclass(frozen=True)
class Havoc(Cmd):
    target: Target


@dataclass(frozen=True)
class PhiArm:
    """One ``B: x`` entry of a phi predecessor list."""

    label: str
    value: str


@dataclass(frozen=True)
class Phi(Cmd):
    target: Target
    arms: tuple[PhiArm, ...] = field(default_factory=tuple)


@dataclass(frozen=True)
class GetRef(Cmd):
    """``x := get_ref r`` - read the value observed through reference ``r``."""

    target: Target
    ref: str


@dataclass(frozen=True)
class Borrow(Cmd):
    """``r := borrow M[i]`` - constant borrow of a bytemap cell."""

    target: Target
    base: Expr
    index: Expr


@dataclass(frozen=True)
class BorrowMut(Cmd):
    """``r, M2 := borrow_mut M[i]`` - mutable borrow + continuation bytemap."""

    ref_target: Target
    map_target: Target
    base: Expr
    index: Expr


@dataclass(frozen=True)
class BorrowRef(Cmd):
    """``q := borrow_ref r`` - constant reborrow from an existing reference."""

    target: Target
    src: str


@dataclass(frozen=True)
class BorrowRefMut(Cmd):
    """``q, r2 := borrow_ref_mut r`` - mutable reborrow + continuation reference."""

    ref_target: Target
    cont_target: Target
    src: str


@dataclass(frozen=True)
class PutRef(Cmd):
    """``r2 := put_ref r, v`` - write through a mutable reference, fresh ref value."""

    target: Target
    ref: str
    value: Expr


@dataclass(frozen=True)
class Release(Cmd):
    """``release r`` - end a reference lifetime."""

    ref: str


@dataclass(frozen=True)
class Assume(Cmd):
    """``assume b`` - keep only executions where ``b`` holds."""

    cond: Expr


@dataclass(frozen=True)
class Assert(Cmd):
    """``assert c`` - fails when the named bool register ``c`` is false."""

    cond_name: str


# --- terminators ---


@dataclass(frozen=True)
class Terminator(ABC):
    """Base for block terminators."""


@dataclass(frozen=True)
class Halt(Terminator):
    """``halt`` - stop execution at the current block."""


@dataclass(frozen=True)
class Goto(Terminator):
    """``goto B`` - unconditional transfer."""

    target: str


@dataclass(frozen=True)
class IfGoto(Terminator):
    """``if c goto B1 else B2`` - branch on the named bool register ``c``."""

    cond: str
    then_target: str
    else_target: str


# --- containers ---


@dataclass(frozen=True)
class Block:
    label: str
    commands: tuple[Cmd, ...]
    terminator: Terminator


@dataclass(frozen=True)
class Program:
    blocks: tuple[Block, ...]
    entry: str | None
    exit: str | None
