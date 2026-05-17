"""Command-level dispatch on top of the S-expr layer.

Walks the top-level `SexprNode`s from `parse_sexprs` and classifies each
into a typed `Smt2Statement` variant. Bodies stay as raw `SexprNode`s
— we have no `let` / quantifiers in our corpus, so the S-expr tree IS
the expression representation.

Each statement carries its source span. Unchanged statements emit
byte-identical via `src[span[0]:span[1]]`; modified statements
re-render through the pretty-printer in `pp.py`.
"""
from __future__ import annotations

from abc import ABC
from dataclasses import dataclass, field
from pathlib import Path

from ctac.solver.smt2.lexer import TokenKind
from ctac.solver.smt2.sexpr import (
    Atom,
    CommentBlock,
    List_,
    SexprNode,
    Smt2ParseError,
    parse_sexprs,
)


# ---- Statement base + variants ---------------------------------------------


class Smt2Statement(ABC):
    """Abstract command. Concrete variants below.

    `span = (start, end)` byte offsets into the original source. `dirty`
    flag indicates the statement has been mutated since parse (drives
    emit-from-fields vs emit-from-source-slice in `emit.py`)."""
    span: tuple[int, int]
    dirty: bool


def _make_stmt():
    """dataclass field defaults for every Smt2Statement subclass."""
    return dict(span=(-1, -1), dirty=False)


@dataclass
class SetOption(Smt2Statement):
    """`(set-option :key value)`. value_node retains structure (could be
    a Bool, numeral, string, or `(... ...)` sub-form like a tactic)."""
    key: str
    value_node: SexprNode
    span: tuple[int, int] = (-1, -1)
    dirty: bool = False


@dataclass
class SetLogic(Smt2Statement):
    """`(set-logic LOGIC)`."""
    logic: str
    span: tuple[int, int] = (-1, -1)
    dirty: bool = False


@dataclass
class DeclareConst(Smt2Statement):
    """`(declare-const NAME SORT)`. `sort_node` is the raw S-expr for
    SORT — usually an Atom (Int/Bool/Real) but can be `(Array Int Int)`
    etc."""
    name: str
    sort_node: SexprNode
    span: tuple[int, int] = (-1, -1)
    dirty: bool = False


@dataclass
class DeclareFun(Smt2Statement):
    """`(declare-fun NAME (PARAM_SORT...) RET_SORT)`."""
    name: str
    param_sorts: list[SexprNode]
    ret_sort_node: SexprNode
    span: tuple[int, int] = (-1, -1)
    dirty: bool = False


@dataclass
class DefineFunParam:
    """One `(name sort)` pair in a define-fun signature."""
    name: str
    sort_node: SexprNode


@dataclass
class DefineFun(Smt2Statement):
    """`(define-fun NAME (PARAMS) RET_SORT BODY)`."""
    name: str
    params: list[DefineFunParam]
    ret_sort_node: SexprNode
    body: SexprNode
    span: tuple[int, int] = (-1, -1)
    dirty: bool = False


@dataclass
class Assert(Smt2Statement):
    """`(assert EXPR)` or `(assert (! EXPR :named NAME))`.

    `named` is the name string if the body is wrapped in `(! ... :named N)`;
    None otherwise. `body` is always the inner expression (the `(! ...)`
    annotation wrapper is stripped if present)."""
    body: SexprNode
    named: str | None = None
    span: tuple[int, int] = (-1, -1)
    dirty: bool = False


@dataclass
class CheckSat(Smt2Statement):
    span: tuple[int, int] = (-1, -1)
    dirty: bool = False


@dataclass
class CheckSatUsing(Smt2Statement):
    """`(check-sat-using TACTIC)`. tactic kept as raw S-expr."""
    tactic_node: SexprNode
    span: tuple[int, int] = (-1, -1)
    dirty: bool = False


@dataclass
class Apply(Smt2Statement):
    """`(apply TACTIC)`. tactic kept as raw S-expr."""
    tactic_node: SexprNode
    span: tuple[int, int] = (-1, -1)
    dirty: bool = False


@dataclass
class GetModel(Smt2Statement):
    span: tuple[int, int] = (-1, -1)
    dirty: bool = False


@dataclass
class GetInfo(Smt2Statement):
    """`(get-info :keyword)`."""
    info_keyword: str
    span: tuple[int, int] = (-1, -1)
    dirty: bool = False


@dataclass
class GetValue(Smt2Statement):
    """`(get-value (e1 e2 ...))`. args kept as raw S-exprs."""
    args: list[SexprNode]
    span: tuple[int, int] = (-1, -1)
    dirty: bool = False


@dataclass
class GetUnsatCore(Smt2Statement):
    span: tuple[int, int] = (-1, -1)
    dirty: bool = False


@dataclass
class Push(Smt2Statement):
    """`(push N)`. N defaults to 1 if not given."""
    n: int = 1
    span: tuple[int, int] = (-1, -1)
    dirty: bool = False


@dataclass
class Pop(Smt2Statement):
    n: int = 1
    span: tuple[int, int] = (-1, -1)
    dirty: bool = False


@dataclass
class Exit(Smt2Statement):
    span: tuple[int, int] = (-1, -1)
    dirty: bool = False


@dataclass
class Comment(Smt2Statement):
    """Top-level comment block (no enclosing form)."""
    lines: list[str] = field(default_factory=list)
    span: tuple[int, int] = (-1, -1)
    dirty: bool = False


@dataclass
class Raw(Smt2Statement):
    """Fallback for top-level forms whose command we don't recognize.
    Keep the whole node so we can re-emit verbatim."""
    node: SexprNode
    span: tuple[int, int] = (-1, -1)
    dirty: bool = False


# ---- File container ---------------------------------------------------------


@dataclass
class Smt2File:
    """A parsed SMT-LIB file: ordered statements + reference to the
    original source string (so `emit` can byte-identical slice
    unchanged forms)."""
    statements: list[Smt2Statement] = field(default_factory=list)
    source: str = ''
    path: Path | None = None


# ---- Parser -----------------------------------------------------------------


def parse(src_or_path: str | Path) -> Smt2File:
    """Parse an SMT-LIB v2 file. Accepts a Path or raw source string."""
    if isinstance(src_or_path, Path):
        src = src_or_path.read_text()
        path: Path | None = src_or_path
    else:
        src = src_or_path
        path = None
    nodes = parse_sexprs(src)
    statements: list[Smt2Statement] = []
    for node in nodes:
        statements.append(_dispatch(node, src))
    return Smt2File(statements=statements, source=src, path=path)


def _dispatch(node: SexprNode, src: str) -> Smt2Statement:
    """Convert one top-level SexprNode into a typed Smt2Statement.

    Re-raises any `Smt2ParseError` from a handler with `src` attached so
    the message carries 1-based line/col (handlers don't see `src`)."""
    if isinstance(node, CommentBlock):
        return Comment(lines=list(node.lines), span=node.span)
    if not isinstance(node, List_):
        # Bare atom at the top level — wrap as Raw.
        return Raw(node=node, span=node.span)
    head = node.head_text
    if head is None:
        return Raw(node=node, span=node.span)
    handler = _HEAD_DISPATCH.get(head)
    if handler is None:
        return Raw(node=node, span=node.span)
    try:
        return handler(node)
    except Smt2ParseError as e:
        if e.line is None:
            raise Smt2ParseError(e.msg, e.pos, src=src) from None
        raise


# ---- Per-command handlers ---------------------------------------------------


def _expect_atom(node: SexprNode, what: str) -> str:
    if not isinstance(node, Atom):
        raise Smt2ParseError(f'expected {what}, got {type(node).__name__}',
                              getattr(node, 'span', (-1, -1))[0])
    return node.text


def _expect_list(node: SexprNode, what: str) -> List_:
    if not isinstance(node, List_):
        raise Smt2ParseError(f'expected {what} (a list)',
                              getattr(node, 'span', (-1, -1))[0])
    return node


def _parse_set_option(node: List_) -> SetOption:
    # (set-option :key value)
    if len(node.children) < 3:
        raise Smt2ParseError('set-option requires :key and value',
                              node.span[0])
    key_node = node.children[1]
    if not isinstance(key_node, Atom) or key_node.kind is not TokenKind.KEYWORD:
        raise Smt2ParseError('set-option key must be a :keyword', node.span[0])
    return SetOption(key=key_node.text,
                      value_node=node.children[2],
                      span=node.span)


def _parse_set_logic(node: List_) -> SetLogic:
    if len(node.children) != 2:
        raise Smt2ParseError('set-logic takes one argument', node.span[0])
    return SetLogic(logic=_expect_atom(node.children[1], 'logic name'),
                     span=node.span)


def _parse_declare_const(node: List_) -> DeclareConst:
    if len(node.children) != 3:
        raise Smt2ParseError('declare-const takes NAME and SORT', node.span[0])
    name = _expect_atom(node.children[1], 'declare-const name')
    return DeclareConst(name=name, sort_node=node.children[2], span=node.span)


def _parse_declare_fun(node: List_) -> DeclareFun:
    if len(node.children) != 4:
        raise Smt2ParseError(
            'declare-fun takes NAME (PARAM-SORTS...) RET-SORT', node.span[0])
    name = _expect_atom(node.children[1], 'declare-fun name')
    params_list = _expect_list(node.children[2], 'declare-fun param sorts')
    return DeclareFun(name=name,
                       param_sorts=list(params_list.children),
                       ret_sort_node=node.children[3],
                       span=node.span)


def _parse_define_fun(node: List_) -> DefineFun:
    # (define-fun NAME ((p1 s1) (p2 s2) ...) RET BODY)
    if len(node.children) != 5:
        raise Smt2ParseError(
            'define-fun takes NAME (PARAMS) RET BODY', node.span[0])
    name = _expect_atom(node.children[1], 'define-fun name')
    params_list = _expect_list(node.children[2], 'define-fun params')
    params: list[DefineFunParam] = []
    for p in params_list.children:
        pl = _expect_list(p, 'param (name sort)')
        if len(pl.children) != 2:
            raise Smt2ParseError('param must be (name sort)', pl.span[0])
        params.append(DefineFunParam(
            name=_expect_atom(pl.children[0], 'param name'),
            sort_node=pl.children[1]))
    return DefineFun(name=name, params=params,
                      ret_sort_node=node.children[3],
                      body=node.children[4],
                      span=node.span)


def _parse_assert(node: List_) -> Assert:
    # (assert EXPR)  or  (assert (! EXPR :named NAME))
    if len(node.children) != 2:
        raise Smt2ParseError('assert takes one expression', node.span[0])
    body = node.children[1]
    named: str | None = None
    if isinstance(body, List_) and len(body.children) >= 1:
        head0 = body.children[0]
        if isinstance(head0, Atom) and head0.text == '!':
            # (! EXPR :keyword value ...) — pull out :named if present
            named = _scan_named(body.children[2:])
            body = body.children[1] if len(body.children) >= 2 else body
    return Assert(body=body, named=named, span=node.span)


def _scan_named(rest: list[SexprNode]) -> str | None:
    """Walk a list of (:keyword value :keyword value ...) and return
    the :named value if present, else None."""
    i = 0
    while i + 1 < len(rest):
        k = rest[i]
        v = rest[i + 1]
        if isinstance(k, Atom) and k.text == ':named':
            if isinstance(v, Atom):
                return v.text
        i += 2
    return None


def _parse_simple(cls):
    """Factory for commands that take no arguments (check-sat, get-model,
    get-unsat-core, exit)."""
    def handler(node: List_) -> Smt2Statement:
        return cls(span=node.span)
    return handler


def _parse_check_sat_using(node: List_) -> CheckSatUsing:
    if len(node.children) != 2:
        raise Smt2ParseError('check-sat-using takes one tactic argument',
                              node.span[0])
    return CheckSatUsing(tactic_node=node.children[1], span=node.span)


def _parse_apply(node: List_) -> Apply:
    if len(node.children) != 2:
        raise Smt2ParseError('apply takes one tactic argument', node.span[0])
    return Apply(tactic_node=node.children[1], span=node.span)


def _parse_get_info(node: List_) -> GetInfo:
    if len(node.children) != 2:
        raise Smt2ParseError('get-info takes one :keyword', node.span[0])
    kw = node.children[1]
    if not isinstance(kw, Atom) or kw.kind is not TokenKind.KEYWORD:
        raise Smt2ParseError('get-info argument must be :keyword', node.span[0])
    return GetInfo(info_keyword=kw.text, span=node.span)


def _parse_get_value(node: List_) -> GetValue:
    # (get-value (e1 e2 ...))
    if len(node.children) != 2:
        raise Smt2ParseError('get-value takes one (e1 e2 ...) argument',
                              node.span[0])
    args_list = _expect_list(node.children[1], 'get-value argument list')
    return GetValue(args=list(args_list.children), span=node.span)


def _parse_push(node: List_) -> Push:
    n = _parse_optional_numeral(node, default=1)
    return Push(n=n, span=node.span)


def _parse_pop(node: List_) -> Pop:
    n = _parse_optional_numeral(node, default=1)
    return Pop(n=n, span=node.span)


def _parse_optional_numeral(node: List_, *, default: int) -> int:
    if len(node.children) == 1:
        return default
    if len(node.children) == 2:
        arg = node.children[1]
        if isinstance(arg, Atom) and arg.kind is TokenKind.NUMERAL:
            return int(arg.text)
    raise Smt2ParseError(f'{node.head_text} takes an optional numeral',
                          node.span[0])


_HEAD_DISPATCH = {
    'set-option': _parse_set_option,
    'set-logic': _parse_set_logic,
    'declare-const': _parse_declare_const,
    'declare-fun': _parse_declare_fun,
    'define-fun': _parse_define_fun,
    'assert': _parse_assert,
    'check-sat': _parse_simple(CheckSat),
    'check-sat-using': _parse_check_sat_using,
    'apply': _parse_apply,
    'get-model': _parse_simple(GetModel),
    'get-info': _parse_get_info,
    'get-value': _parse_get_value,
    'get-unsat-core': _parse_simple(GetUnsatCore),
    'push': _parse_push,
    'pop': _parse_pop,
    'exit': _parse_simple(Exit),
}
