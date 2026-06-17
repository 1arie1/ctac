"""Recursive-descent parser for Tiny TAC.

Program/block/command structure is parsed top-down; expressions use
precedence climbing (Pratt). Postfix ``[...]`` (load/update) and
``.field`` bind tightest; ``not`` is prefix; binary operators follow the
precedence table below.
"""

from __future__ import annotations

from . import ast
from .errors import TtacParseError
from .lexer import Token, tokenize

# Binary operator left-binding power, low to high. Comparisons are the
# floor that prefix ``not`` reaches into (so ``not a == b`` is
# ``not (a == b)`` while ``not b and c`` is ``(not b) and c``).
_BINOP_BP = {
    "or": 1,
    "and": 2,
    "==": 4,
    "<=": 4,
    "<": 4,
    "+": 5,
    "-": 5,
    "*": 6,
    "/": 6,
}
_CMP_BP = 4

_TYPES = {t.value: t for t in ast.Ty}

# RHS-lead keywords that select a non-expression assignment form, mapped
# to the number of LHS targets they bind.
_RHS_KEYWORD_ARITY = {
    "havoc": 1,
    "phi": 1,
    "get_ref": 1,
    "borrow": 1,
    "borrow_mut": 2,
    "borrow_ref": 1,
    "borrow_ref_mut": 2,
    "put_ref": 1,
}

# Names that may not be used as a plain register reference in expressions.
_RESERVED = {
    "assume",
    "assert",
    "borrow",
    "borrow_mut",
    "borrow_ref",
    "borrow_ref_mut",
    "get_ref",
    "goto",
    "halt",
    "havoc",
    "if",
    "else",
    "not",
    "phi",
    "put_ref",
    "release",
    "and",
    "or",
    "bool",
    "int",
    "bytemap",
    "ref",
}

_FIELDS = {"addr", "value", "promise"}


class _Cursor:
    def __init__(self, tokens: list[Token]) -> None:
        self._toks = tokens
        self._i = 0

    def peek(self, ahead: int = 0) -> Token:
        j = self._i + ahead
        if j >= len(self._toks):
            return self._toks[-1]
        return self._toks[j]

    def advance(self) -> Token:
        tok = self.peek()
        if tok.kind != "EOF":
            self._i += 1
        return tok

    def at(self, kind: str) -> bool:
        return self.peek().kind == kind

    def at_name(self, value: str) -> bool:
        tok = self.peek()
        return tok.kind == "NAME" and tok.value == value

    def expect(self, kind: str) -> Token:
        tok = self.peek()
        if tok.kind != kind:
            raise self.err(f"expected {kind!r}, found {self._desc(tok)}")
        return self.advance()

    def expect_name(self) -> Token:
        tok = self.peek()
        if tok.kind != "NAME":
            raise self.err(f"expected a name, found {self._desc(tok)}")
        return self.advance()

    def expect_keyword(self, value: str) -> Token:
        if not self.at_name(value):
            raise self.err(f"expected {value!r}, found {self._desc(self.peek())}")
        return self.advance()

    def err(self, message: str) -> TtacParseError:
        tok = self.peek()
        return TtacParseError(message, tok.line, tok.col)

    @staticmethod
    def _desc(tok: Token) -> str:
        if tok.kind == "EOF":
            return "end of input"
        if tok.kind == "NEWLINE":
            return "end of line"
        return repr(tok.value)

    def skip_newlines(self) -> None:
        while self.at("NEWLINE"):
            self.advance()


def parse_program(source: str) -> ast.Program:
    """Parse a full ``ttac`` program from source text."""
    cur = _Cursor(tokenize(source))
    blocks: list[ast.Block] = []
    cur.skip_newlines()
    while not cur.at("EOF"):
        blocks.append(_parse_block(cur))
        cur.skip_newlines()

    labels = [b.label for b in blocks]
    entry = "entry" if "entry" in labels else (labels[0] if labels else None)
    exit_ = "exit" if "exit" in labels else None
    return ast.Program(tuple(blocks), entry, exit_)


def _parse_block(cur: _Cursor) -> ast.Block:
    label = cur.expect_name().value
    cur.expect(":")
    cur.expect("NEWLINE")

    commands: list[ast.Cmd] = []
    while True:
        cur.skip_newlines()
        tok = cur.peek()
        if tok.kind == "NAME" and tok.value in ("halt", "goto", "if"):
            term = _parse_terminator(cur)
            return ast.Block(label, tuple(commands), term)
        if tok.kind == "EOF":
            raise cur.err(f"block {label!r} has no terminator")
        commands.append(_parse_command(cur))


def _parse_terminator(cur: _Cursor) -> ast.Terminator:
    tok = cur.advance()
    if tok.value == "halt":
        _end_statement(cur)
        return ast.Halt()
    if tok.value == "goto":
        target = cur.expect_name().value
        _end_statement(cur)
        return ast.Goto(target)
    # if c goto B1 else B2
    cond = cur.expect_name().value
    cur.expect_keyword("goto")
    then_target = cur.expect_name().value
    cur.expect_keyword("else")
    else_target = cur.expect_name().value
    _end_statement(cur)
    return ast.IfGoto(cond, then_target, else_target)


def _end_statement(cur: _Cursor) -> None:
    if cur.at("EOF"):
        return
    cur.expect("NEWLINE")


def _parse_command(cur: _Cursor) -> ast.Cmd:
    if cur.at_name("assume"):
        cur.advance()
        cond = _parse_expr(cur, 0)
        _end_statement(cur)
        return ast.Assume(cond)
    if cur.at_name("assert"):
        cur.advance()
        name = cur.expect_name().value
        _end_statement(cur)
        return ast.Assert(name)
    if cur.at_name("release"):
        cur.advance()
        ref = cur.expect_name().value
        _end_statement(cur)
        return ast.Release(ref)
    return _parse_assignment(cur)


def _parse_target(cur: _Cursor) -> ast.Target:
    name = cur.expect_name().value
    ty: ast.Ty | None = None
    if cur.at(":"):
        cur.advance()
        ty_tok = cur.expect_name()
        if ty_tok.value not in _TYPES:
            raise TtacParseError(
                f"unknown type {ty_tok.value!r}", ty_tok.line, ty_tok.col
            )
        ty = _TYPES[ty_tok.value]
    return ast.Target(name, ty)


def _parse_assignment(cur: _Cursor) -> ast.Cmd:
    targets = [_parse_target(cur)]
    while cur.at(","):
        cur.advance()
        targets.append(_parse_target(cur))
    cur.expect(":=")

    lead = cur.peek()
    keyword = lead.value if lead.kind == "NAME" and lead.value in _RHS_KEYWORD_ARITY else None
    if keyword is not None:
        arity = _RHS_KEYWORD_ARITY[keyword]
        if len(targets) != arity:
            raise TtacParseError(
                f"{keyword!r} binds {arity} target(s), got {len(targets)}",
                lead.line,
                lead.col,
            )
        cmd = _parse_keyword_rhs(cur, keyword, targets)
    else:
        if len(targets) != 1:
            raise TtacParseError(
                "expression assignment binds a single target",
                lead.line,
                lead.col,
            )
        rhs = _parse_expr(cur, 0)
        cmd = ast.Assign(targets[0], rhs)
    _end_statement(cur)
    return cmd


def _parse_keyword_rhs(cur: _Cursor, keyword: str, targets: list[ast.Target]) -> ast.Cmd:
    cur.advance()  # consume the keyword
    if keyword == "havoc":
        return ast.Havoc(targets[0])
    if keyword == "phi":
        return ast.Phi(targets[0], _parse_phi_arms(cur))
    if keyword == "get_ref":
        return ast.GetRef(targets[0], cur.expect_name().value)
    if keyword == "borrow":
        base, index = _parse_location(cur)
        return ast.Borrow(targets[0], base, index)
    if keyword == "borrow_mut":
        base, index = _parse_location(cur)
        return ast.BorrowMut(targets[0], targets[1], base, index)
    if keyword == "borrow_ref":
        return ast.BorrowRef(targets[0], cur.expect_name().value)
    if keyword == "borrow_ref_mut":
        return ast.BorrowRefMut(targets[0], targets[1], cur.expect_name().value)
    # put_ref r, v
    ref = cur.expect_name().value
    cur.expect(",")
    value = _parse_expr(cur, 0)
    return ast.PutRef(targets[0], ref, value)


def _parse_location(cur: _Cursor) -> tuple[ast.Expr, ast.Expr]:
    base = ast.Var(cur.expect_name().value)
    cur.expect("[")
    index = _parse_expr(cur, 0)
    cur.expect("]")
    return base, index


def _parse_phi_arms(cur: _Cursor) -> tuple[ast.PhiArm, ...]:
    cur.expect("[")
    arms: list[ast.PhiArm] = []
    if not cur.at("]"):
        while True:
            label = cur.expect_name().value
            cur.expect(":")
            value = cur.expect_name().value
            arms.append(ast.PhiArm(label, value))
            if cur.at(","):
                cur.advance()
                continue
            break
    cur.expect("]")
    return tuple(arms)


# --- expressions (precedence climbing) ---


def _binop(tok: Token) -> str | None:
    if tok.kind in ("==", "<=", "<", "+", "-", "*", "/"):
        return tok.kind
    if tok.kind == "NAME" and tok.value in ("and", "or"):
        return tok.value
    return None


def _parse_expr(cur: _Cursor, min_bp: int) -> ast.Expr:
    left = _parse_unary(cur)
    while True:
        op = _binop(cur.peek())
        if op is None or _BINOP_BP[op] < min_bp:
            return left
        cur.advance()
        right = _parse_expr(cur, _BINOP_BP[op] + 1)
        left = ast.BinExpr(op, left, right)


def _parse_unary(cur: _Cursor) -> ast.Expr:
    if cur.at_name("not"):
        cur.advance()
        operand = _parse_expr(cur, _CMP_BP)
        return ast.UnExpr("not", operand)
    return _parse_postfix(cur, _parse_primary(cur))


def _parse_postfix(cur: _Cursor, base: ast.Expr) -> ast.Expr:
    while True:
        if cur.at("["):
            cur.advance()
            index = _parse_expr(cur, 0)
            if cur.at(":="):
                cur.advance()
                value = _parse_expr(cur, 0)
                cur.expect("]")
                base = ast.Update(base, index, value)
            else:
                cur.expect("]")
                base = ast.Load(base, index)
        elif cur.at("."):
            cur.advance()
            field_tok = cur.expect_name()
            if field_tok.value not in _FIELDS:
                raise TtacParseError(
                    f"unknown field {field_tok.value!r}", field_tok.line, field_tok.col
                )
            base = ast.Field(base, field_tok.value)
        else:
            return base


def _parse_primary(cur: _Cursor) -> ast.Expr:
    tok = cur.peek()
    if tok.kind == "INT":
        cur.advance()
        return ast.Num(int(tok.value))
    if cur.at_name("true"):
        cur.advance()
        return ast.BoolLit(True)
    if cur.at_name("false"):
        cur.advance()
        return ast.BoolLit(False)
    if cur.at_name("havoc"):
        cur.advance()
        return ast.HavocExpr()
    if cur.at_name("if"):
        return _parse_if_expr(cur)
    if cur.at("("):
        cur.advance()
        inner = _parse_expr(cur, 0)
        cur.expect(")")
        return inner
    if cur.at("{"):
        return _parse_record(cur)
    if tok.kind == "NAME":
        if tok.value in _RESERVED:
            raise cur.err(f"unexpected keyword {tok.value!r} in expression")
        cur.advance()
        return ast.Var(tok.value)
    raise cur.err(f"unexpected {_Cursor._desc(tok)} in expression")


def _parse_if_expr(cur: _Cursor) -> ast.Expr:
    cur.advance()  # if
    cond = _parse_expr(cur, 0)
    cur.expect("{")
    then = _parse_expr(cur, 0)
    cur.expect("}")
    cur.expect_keyword("else")
    cur.expect("{")
    els = _parse_expr(cur, 0)
    cur.expect("}")
    return ast.IfExpr(cond, then, els)


def _parse_record(cur: _Cursor) -> ast.Expr:
    cur.expect("{")
    fields: dict[str, ast.Expr] = {}
    while True:
        name_tok = cur.expect_name()
        if name_tok.value not in _FIELDS:
            raise TtacParseError(
                f"unknown record field {name_tok.value!r}", name_tok.line, name_tok.col
            )
        cur.expect(":")
        fields[name_tok.value] = _parse_expr(cur, 0)
        if cur.at(","):
            cur.advance()
            continue
        break
    cur.expect("}")
    missing = _FIELDS - fields.keys()
    if missing:
        raise cur.err(f"ref record missing field(s): {', '.join(sorted(missing))}")
    return ast.Record(fields["addr"], fields["value"], fields["promise"])
