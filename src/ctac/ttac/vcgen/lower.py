"""TinyTAC expression -> VC term lowering.

The replaceable counterpart of ctac's ``vc/tac.py`` ``TacExprLowerer``:
it maps ``ttac`` expressions onto the shared ``ctac.smt.vc`` term
combinators, with ``ttac``'s documented semantics --- ``int`` = SMT
``Int`` (``+ - * div``), ``bool`` = ``Bool``, ``bytemap`` = UF
``Int->Int`` via the builder's bytemap. References are out of scope
(desugared before vcgen); records/fields/havoc-as-expression raise.
"""

from __future__ import annotations

from ctac.smt.vc.bytemap import MapTerm
from ctac.smt.vc.builder import VCBuilder
from ctac.smt.vc.terms import (
    Bool,
    Int,
    Sort,
    Term,
    add,
    and_,
    div,
    eq,
    false,
    ite,
    le,
    lt,
    mul,
    not_,
    or_,
    sub,
    term,
    true,
)

from ctac.ttac import ast
from ctac.ttac.errors import VcGenError

ScalarOrMap = Term | MapTerm

_BINARY = {"+": add, "-": sub, "*": mul, "/": div}


class TtacLowerer:
    def __init__(self, vc: VCBuilder, symbol_sorts: dict[str, str]) -> None:
        self.vc = vc
        self.sorts = symbol_sorts  # name -> "int" | "bool" | "bytemap"

    def sort_of(self, name: str) -> Sort:
        return Bool if self.sorts.get(name) == "bool" else Int

    def _is_map(self, name: str) -> bool:
        return self.sorts.get(name) == "bytemap"

    def symbol(self, name: str) -> ScalarOrMap:
        if self._is_map(name):
            return self.vc.bytemap.ref(name)
        return self.vc.const(name, self.sort_of(name))

    def lower(self, e: ast.Expr) -> ScalarOrMap:
        if isinstance(e, ast.Num):
            return term(str(e.value), Int)
        if isinstance(e, ast.BoolLit):
            return true() if e.value else false()
        if isinstance(e, ast.Var):
            return self.symbol(e.name)
        if isinstance(e, ast.Load):
            return self.vc.bytemap.select(self.lower_map(e.base), self.lower_int(e.index))
        if isinstance(e, ast.BinExpr):
            return self._binary(e)
        if isinstance(e, ast.UnExpr):  # "not"
            return not_(self.lower_bool(e.operand))
        if isinstance(e, ast.IfExpr):
            cond = self.lower_bool(e.cond)
            then = self.lower_scalar(e.then)
            els = self.lower_scalar(e.els)
            return ite(cond, then, els, then.sort)
        if isinstance(e, (ast.Record, ast.Field, ast.HavocExpr)):
            raise VcGenError(
                f"{type(e).__name__} is a reference construct; desugar references before vcgen"
            )
        if isinstance(e, ast.Update):
            raise VcGenError("bytemap update is only valid as an assignment right-hand side")
        raise VcGenError(f"unsupported expression {type(e).__name__}")

    def _binary(self, e: ast.BinExpr) -> Term:
        op = e.op
        if op in _BINARY:
            return _BINARY[op](self.lower_int(e.lhs), self.lower_int(e.rhs))
        if op == "<=":
            return le(self.lower_int(e.lhs), self.lower_int(e.rhs))
        if op == "<":
            return lt(self.lower_int(e.lhs), self.lower_int(e.rhs))
        if op == "==":
            return eq(self.lower_scalar(e.lhs), self.lower_scalar(e.rhs))
        if op == "and":
            return and_(self.lower_bool(e.lhs), self.lower_bool(e.rhs))
        if op == "or":
            return or_(self.lower_bool(e.lhs), self.lower_bool(e.rhs))
        raise VcGenError(f"unsupported operator {op!r}")

    def lower_map(self, e: ast.Expr) -> MapTerm:
        out = self.lower(e)
        if not isinstance(out, MapTerm):
            raise VcGenError(f"expected a bytemap expression, got {out.smt()}")
        return out

    def lower_scalar(self, e: ast.Expr) -> Term:
        out = self.lower(e)
        if isinstance(out, MapTerm):
            raise VcGenError(f"expected a scalar expression, got bytemap {out.smt()}")
        return out

    def lower_int(self, e: ast.Expr) -> Term:
        return self.lower_scalar(e)

    def lower_bool(self, e: ast.Expr) -> Term:
        return self.lower_scalar(e)
