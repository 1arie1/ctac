"""smt2 -> deep-embedded formula transpiler for ``ttac vc-check``.

A deliberately dumb, syntactic translation: each smt2 ``(assert ...)``
becomes a ``Ttac.BExp`` term via a name -> register-number table and a
structure-preserving walk. The only normalizations are the negative
integer literal ``(- 5)``, the right fold of n-ary ``and``/``or``, and
singleton unwrap. All semantic judgment lives in the Lean checker.

Terms are built as small tuples (see ``render``) shared with the
diagnostic expected-VC mirror, so matching constraints render to
byte-identical Lean text on both paths.
"""

from __future__ import annotations

from dataclasses import dataclass

from ctac.solver.smt2 import (
    Assert,
    Atom,
    CheckSat,
    Comment,
    DeclareConst,
    List_,
    SetLogic,
    SetOption,
    SexprNode,
    Smt2File,
    TokenKind,
)
from ctac.ttac import ast
from ctac.ttac.ast import Ty

from .naming import Numbering

# Term = ("lit", int) | ("litb", bool) | ("var", int) | ("blk", int)
#      | (op, Term, ...)
Term = tuple

_INT_OPS = {"+": "add", "-": "sub", "*": "mul", "div": "div"}
_CMP_OPS = {"<=": "le", "<": "lt"}


def render(t: Term) -> str:
    """Render a term as a parenthesized Lean anonymous-constructor
    application; ``render_top`` strips the outer parens for list entries."""
    kind = t[0]
    if kind == "lit":
        n = t[1]
        return f"(.lit {n})" if n >= 0 else f"(.lit ({n}))"
    if kind == "litb":
        return f"(.lit {'true' if t[1] else 'false'})"
    if kind == "var":
        return f"(.var {t[1]})"
    if kind == "blk":
        return f"(.blk {t[1]})"
    args = " ".join(render(a) for a in t[1:])
    return f"(.{kind} {args})"


def render_top(t: Term) -> str:
    s = render(t)
    return s[1:-1]


@dataclass(frozen=True)
class VcSymbols:
    numbering: Numbering
    types: dict[str, Ty]
    sorts: dict[str, Ty]  # every declared smt2 const
    block_vars: dict[str, int]  # "BLK_<label>" / "BLK_EXIT" -> guard index


class TranspileError(Exception):
    def __init__(self, message: str, span: tuple[int, int] | None = None) -> None:
        self.span = span
        super().__init__(message)


def _line_col(src: str, pos: int) -> tuple[int, int]:
    line = src.count("\n", 0, pos) + 1
    col = pos - (src.rfind("\n", 0, pos) + 1) + 1
    return line, col


def _at(src: str, node: SexprNode) -> str:
    line, col = _line_col(src, node.span[0])
    return f"{line}:{col}"


def build_vc_symbols(
    program: ast.Program,
    numbering: Numbering,
    types: dict[str, Ty],
    smt: Smt2File,
) -> tuple[VcSymbols, list[str]]:
    errors: list[str] = []
    block_vars = {
        f"BLK_{label}": idx for label, idx in numbering.block_index.items()
    }
    block_vars["BLK_EXIT"] = len(numbering.block_index)

    sorts: dict[str, Ty] = {}
    for stmt in smt.statements:
        if not isinstance(stmt, DeclareConst):
            continue
        name = stmt.name
        sort = stmt.sort_node
        if not (isinstance(sort, Atom) and sort.text in ("Int", "Bool")):
            errors.append(
                f"declare-const '{name}': only Int and Bool sorts are "
                "supported (scalar VCs only)"
            )
            continue
        declared = Ty.INT if sort.text == "Int" else Ty.BOOL
        if name in sorts:
            errors.append(f"duplicate declare-const '{name}'")
            continue
        if name in numbering.int_regs:
            if declared is not Ty.INT:
                errors.append(f"sort mismatch: '{name}' is an int register "
                              "but declared Bool")
        elif name in numbering.bool_regs:
            if declared is not Ty.BOOL:
                errors.append(f"sort mismatch: '{name}' is a bool register "
                              "but declared Int")
        elif name in block_vars:
            if declared is not Ty.BOOL:
                errors.append(f"sort mismatch: '{name}' must be Bool")
        else:
            errors.append(
                f"unknown constant '{name}': not a program register, "
                "BLK_<label>, or BLK_EXIT"
            )
            continue
        sorts[name] = declared

    syms = VcSymbols(
        numbering=numbering,
        types=types,
        sorts=sorts,
        block_vars=block_vars,
    )
    return syms, errors


_IGNORED_STMTS = (Comment, SetLogic, SetOption, CheckSat)


def triage_statements(smt: Smt2File) -> tuple[list[Assert], list[str]]:
    asserts: list[Assert] = []
    errors: list[str] = []
    for stmt in smt.statements:
        if isinstance(stmt, Assert):
            asserts.append(stmt)
        elif isinstance(stmt, (DeclareConst, *_IGNORED_STMTS)):
            continue
        else:
            kind = type(stmt).__name__
            errors.append(
                f"unsupported statement {kind}: vc-check handles scalar "
                "declare-const/assert VCs only (bytemap/UF VCs are out of scope)"
            )
    if not asserts:
        errors.append("smt2 file contains no asserts")
    return asserts, errors


def _sort_of(node: SexprNode, syms: VcSymbols, src: str) -> Ty:
    if isinstance(node, Atom):
        if node.kind == TokenKind.NUMERAL:
            return Ty.INT
        if node.text in ("true", "false"):
            return Ty.BOOL
        ty = syms.sorts.get(node.text)
        if ty is None:
            raise TranspileError(
                f"undeclared symbol '{node.text}' at {_at(src, node)}", node.span
            )
        return ty
    if isinstance(node, List_):
        head = node.head_text
        if head in _INT_OPS:
            return Ty.INT
        if head in ("<=", "<", "=", "and", "or", "not", "=>"):
            return Ty.BOOL
        if head == "ite":
            if len(node.children) != 4:
                raise TranspileError(f"ite arity at {_at(src, node)}", node.span)
            t = _sort_of(node.children[2], syms, src)
            e = _sort_of(node.children[3], syms, src)
            if t is not e:
                raise TranspileError(
                    f"ite branches have different sorts at {_at(src, node)}",
                    node.span,
                )
            return t
    raise TranspileError(
        f"unsupported expression at {_at(src, node)}", node.span
    )


def _int_term(node: SexprNode, syms: VcSymbols, src: str) -> Term:
    if isinstance(node, Atom):
        if node.kind == TokenKind.NUMERAL:
            return ("lit", int(node.text))
        if node.text in syms.numbering.int_regs:
            return ("var", syms.numbering.int_regs[node.text])
        if node.text in syms.sorts:
            raise TranspileError(
                f"'{node.text}' is Bool-sorted but used as Int at "
                f"{_at(src, node)}", node.span,
            )
        raise TranspileError(
            f"undeclared symbol '{node.text}' at {_at(src, node)}", node.span
        )
    if isinstance(node, List_):
        head = node.head_text
        args = node.children[1:]
        if head == "-" and len(args) == 1:
            inner = args[0]
            if isinstance(inner, Atom) and inner.kind == TokenKind.NUMERAL:
                return ("lit", -int(inner.text))
            raise TranspileError(
                f"unary minus of a non-literal at {_at(src, node)}", node.span
            )
        if head in _INT_OPS:
            if len(args) != 2:
                raise TranspileError(
                    f"'{head}' expects 2 operands at {_at(src, node)}", node.span
                )
            return (
                _INT_OPS[head],
                _int_term(args[0], syms, src),
                _int_term(args[1], syms, src),
            )
        if head == "ite":
            return (
                "ite",
                _bool_term(node.children[1], syms, src),
                _int_term(node.children[2], syms, src),
                _int_term(node.children[3], syms, src),
            )
    raise TranspileError(
        f"unsupported Int expression at {_at(src, node)}", node.span
    )


def _bool_term(node: SexprNode, syms: VcSymbols, src: str) -> Term:
    if isinstance(node, Atom):
        if node.text == "true":
            return ("litb", True)
        if node.text == "false":
            return ("litb", False)
        if node.text in syms.block_vars:
            return ("blk", syms.block_vars[node.text])
        if node.text in syms.numbering.bool_regs:
            return ("var", syms.numbering.bool_regs[node.text])
        if node.text in syms.sorts:
            raise TranspileError(
                f"'{node.text}' is Int-sorted but used as Bool at "
                f"{_at(src, node)}", node.span,
            )
        raise TranspileError(
            f"undeclared symbol '{node.text}' at {_at(src, node)}", node.span
        )
    if isinstance(node, List_):
        head = node.head_text
        args = node.children[1:]
        if head in _CMP_OPS:
            if len(args) != 2:
                raise TranspileError(
                    f"'{head}' expects 2 operands at {_at(src, node)}", node.span
                )
            return (
                _CMP_OPS[head],
                _int_term(args[0], syms, src),
                _int_term(args[1], syms, src),
            )
        if head == "=":
            if len(args) != 2:
                raise TranspileError(
                    f"'=' expects 2 operands at {_at(src, node)}", node.span
                )
            lhs_ty = _sort_of(args[0], syms, src)
            rhs_ty = _sort_of(args[1], syms, src)
            if lhs_ty is not rhs_ty:
                raise TranspileError(
                    f"operands of '=' have different sorts at {_at(src, node)}",
                    node.span,
                )
            if lhs_ty is Ty.INT:
                return ("eqI", _int_term(args[0], syms, src),
                        _int_term(args[1], syms, src))
            return ("eqB", _bool_term(args[0], syms, src),
                    _bool_term(args[1], syms, src))
        if head == "not":
            if len(args) != 1:
                raise TranspileError(
                    f"'not' expects 1 operand at {_at(src, node)}", node.span
                )
            return ("not", _bool_term(args[0], syms, src))
        if head in ("and", "or"):
            if not args:
                raise TranspileError(
                    f"empty '{head}' at {_at(src, node)}", node.span
                )
            terms = [_bool_term(a, syms, src) for a in args]
            out = terms[-1]
            for t in reversed(terms[:-1]):
                out = (head, t, out)
            return out
        if head == "=>":
            if len(args) != 2:
                raise TranspileError(
                    f"'=>' expects 2 operands at {_at(src, node)}", node.span
                )
            return ("imp", _bool_term(args[0], syms, src),
                    _bool_term(args[1], syms, src))
        if head == "ite":
            if len(args) != 3:
                raise TranspileError(f"ite arity at {_at(src, node)}", node.span)
            return (
                "ite",
                _bool_term(args[0], syms, src),
                _bool_term(args[1], syms, src),
                _bool_term(args[2], syms, src),
            )
        raise TranspileError(
            f"unsupported operator '{head}' at {_at(src, node)}", node.span
        )
    raise TranspileError(
        f"unsupported Bool expression at {_at(src, node)}", node.span
    )


@dataclass(frozen=True)
class VcAssert:
    term: Term
    source: str  # normalized smt2 source slice (audit-trail comment)
    line: int


def transpile_vc(
    smt: Smt2File, syms: VcSymbols
) -> tuple[list[VcAssert], list[str]]:
    asserts, errors = triage_statements(smt)
    out: list[VcAssert] = []
    src = smt.source
    for stmt in asserts:
        try:
            term = _bool_term(stmt.body, syms, src)
        except TranspileError as exc:
            errors.append(str(exc))
            continue
        snippet = " ".join(src[stmt.span[0]:stmt.span[1]].split())
        if len(snippet) > 100:
            snippet = snippet[:97] + "..."
        out.append(
            VcAssert(term=term, source=snippet, line=_line_col(src, stmt.span[0])[0])
        )
    return out, errors
