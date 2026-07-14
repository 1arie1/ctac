"""Type inference for Tiny TAC.

Assigns every variable one of the four ``ttac`` types
(``bool | int | bytemap | ref``). The program is assumed to be in
DSA/SSA form (see ``dsa.check_dsa``), so each variable is determined by
its definition; copies, phi merges, and dynamic merges share a type.

Implementation: a union-find over variable names with a per-class type
label. The validated ``networkx.utils.UnionFind`` owns the partitioning;
we layer a ``representative -> Ty`` label on top, combined with ``meet``.
``ttac`` typing is structural (no data-dependent rules), so a single
constraint-collection pass plus union-find resolution is exact - no
fixpoint iteration.

``analyze_types`` never raises (it collects all unknowns/conflicts for
diagnostics); ``infer_types`` hard-fails via ``TtacTypeError`` when the
typing is not total.
"""

from __future__ import annotations

from dataclasses import dataclass

from networkx.utils import UnionFind

from ctac.ttac import ast
from ctac.ttac.ast import Ty
from ctac.ttac.errors import TtacTypeError

from .defuse import extract_def_use

_CONFLICT = object()  # sentinel: a class with contradictory type evidence

# A constraint result: a concrete Ty, ("var", name), or None (unknown).
_Var = tuple[str, str]


def _meet(a: object, b: object) -> object:
    if a is None:
        return b
    if b is None:
        return a
    if a is _CONFLICT or b is _CONFLICT:
        return _CONFLICT
    return a if a == b else _CONFLICT


@dataclass(frozen=True)
class TypeResult:
    types: dict[str, Ty | None]  # None == unknown (also set for conflicts)
    conflicts: frozenset[str]
    errors: tuple[str, ...]
    class_members: dict[str, tuple[str, ...]]

    @property
    def is_total(self) -> bool:
        return not self.errors and all(t is not None for t in self.types.values())


class _Solver:
    def __init__(self) -> None:
        self._uf: UnionFind = UnionFind()
        self._label: dict[str, object] = {}
        self.errors: list[str] = []

    def add(self, name: str) -> str:
        return self._uf[name]

    def meet(self, name: str, ty: Ty) -> None:
        rep = self._uf[name]
        self._label[rep] = _meet(self._label.get(rep), ty)

    def union(self, a: str, b: str) -> None:
        ra, rb = self._uf[a], self._uf[b]
        if ra == rb:
            return
        merged = _meet(self._label.get(ra), self._label.get(rb))
        self._uf.union(a, b)
        new_rep = self._uf[a]
        for old in (ra, rb):
            if old != new_rep:
                self._label.pop(old, None)
        self._label[new_rep] = merged

    def label_of(self, name: str) -> object:
        return self._label.get(self._uf[name])

    def rep(self, name: str) -> str:
        return self._uf[name]


def analyze_types(program: ast.Program) -> TypeResult:
    du = extract_def_use(program)
    s = _Solver()

    def expect(expr: ast.Expr, ty: Ty) -> None:
        _apply(s, _constrain(s, expr), ty)

    for block in program.blocks:
        for cmd in block.commands:
            _constrain_cmd(s, cmd, expect)
        if isinstance(block.terminator, ast.IfGoto):
            s.meet(block.terminator.cond, Ty.BOOL)

    # Register every variable so unused/unconstrained ones surface as unknown.
    for sym in du.symbols:
        s.add(sym)

    types: dict[str, Ty | None] = {}
    conflicts: set[str] = set()
    members: dict[str, list[str]] = {}
    for sym in sorted(du.symbols):
        members.setdefault(s.rep(sym), []).append(sym)
        lab = s.label_of(sym)
        if lab is _CONFLICT:
            types[sym] = None
            conflicts.add(sym)
        elif isinstance(lab, Ty):
            types[sym] = lab
        else:
            types[sym] = None

    return TypeResult(
        types=types,
        conflicts=frozenset(conflicts),
        errors=tuple(s.errors),
        class_members={r: tuple(m) for r, m in members.items()},
    )


def infer_types(program: ast.Program) -> dict[str, Ty]:
    """Return a total variable->type map, or raise ``TtacTypeError``."""
    res = analyze_types(program)
    unknown = tuple(
        sym for sym, t in sorted(res.types.items())
        if t is None and sym not in res.conflicts
    )
    if unknown or res.conflicts or res.errors:
        raise TtacTypeError(
            unknown=unknown,
            conflicts=tuple(sorted(res.conflicts)),
            errors=res.errors,
        )
    return {sym: t for sym, t in res.types.items() if t is not None}


# --- constraint generation ---


def _apply(s: _Solver, result: object, ty: Ty) -> None:
    """Constrain a constrain-result to have type ``ty``."""
    if isinstance(result, tuple):  # ("var", name)
        s.meet(result[1], ty)
    elif isinstance(result, Ty):
        if result != ty:
            s.errors.append(f"expected {ty.value}, found {result.value}")
    # None (havoc / unknown): nothing to pin.


def _unify(s: _Solver, a: object, b: object) -> None:
    """Constrain two constrain-results to share a type (e.g. == operands)."""
    if a is None or b is None:
        return
    a_var = isinstance(a, tuple)
    b_var = isinstance(b, tuple)
    if a_var and b_var:
        s.union(a[1], b[1])
    elif a_var:
        s.meet(a[1], b)  # b is a Ty
    elif b_var:
        s.meet(b[1], a)  # a is a Ty
    elif a != b:
        s.errors.append(f"incompatible types {a.value} and {b.value}")


def _constrain(s: _Solver, expr: ast.Expr) -> object:
    if isinstance(expr, ast.Num):
        return Ty.INT
    if isinstance(expr, ast.BoolLit):
        return Ty.BOOL
    if isinstance(expr, ast.HavocExpr):
        return None
    if isinstance(expr, ast.Var):
        return ("var", expr.name)
    if isinstance(expr, ast.Load):
        _apply(s, _constrain(s, expr.base), Ty.BYTEMAP)
        _apply(s, _constrain(s, expr.index), Ty.INT)
        return Ty.INT
    if isinstance(expr, ast.Update):
        _apply(s, _constrain(s, expr.base), Ty.BYTEMAP)
        _apply(s, _constrain(s, expr.index), Ty.INT)
        _apply(s, _constrain(s, expr.value), Ty.INT)
        return Ty.BYTEMAP
    if isinstance(expr, ast.BinExpr):
        return _constrain_bin(s, expr)
    if isinstance(expr, ast.UnExpr):  # not
        _apply(s, _constrain(s, expr.operand), Ty.BOOL)
        return Ty.BOOL
    if isinstance(expr, ast.Record):
        _apply(s, _constrain(s, expr.addr), Ty.INT)
        _apply(s, _constrain(s, expr.value), Ty.INT)
        _apply(s, _constrain(s, expr.promise), Ty.INT)
        return Ty.REF
    if isinstance(expr, ast.Field):
        _apply(s, _constrain(s, expr.base), Ty.REF)
        return Ty.INT
    if isinstance(expr, ast.IfExpr):
        _apply(s, _constrain(s, expr.cond), Ty.BOOL)
        a = _constrain(s, expr.then)
        b = _constrain(s, expr.els)
        _unify(s, a, b)
        return a if a is not None else b
    raise TypeError(f"unknown expression node {type(expr).__name__}")


def _constrain_bin(s: _Solver, expr: ast.BinExpr) -> object:
    op = expr.op
    if op in ("+", "-", "*", "/"):
        _apply(s, _constrain(s, expr.lhs), Ty.INT)
        _apply(s, _constrain(s, expr.rhs), Ty.INT)
        return Ty.INT
    if op in ("<=", "<"):
        _apply(s, _constrain(s, expr.lhs), Ty.INT)
        _apply(s, _constrain(s, expr.rhs), Ty.INT)
        return Ty.BOOL
    if op == "==":
        _unify(s, _constrain(s, expr.lhs), _constrain(s, expr.rhs))
        return Ty.BOOL
    if op in ("and", "or"):
        _apply(s, _constrain(s, expr.lhs), Ty.BOOL)
        _apply(s, _constrain(s, expr.rhs), Ty.BOOL)
        return Ty.BOOL
    raise TypeError(f"unknown binary operator {op!r}")


def _annot(s: _Solver, target: ast.Target) -> None:
    if target.ty is not None:
        s.meet(target.name, target.ty)


def _constrain_cmd(s: _Solver, cmd: ast.Cmd, expect) -> None:
    if isinstance(cmd, ast.Assign):
        _annot(s, cmd.target)
        r = _constrain(s, cmd.rhs)
        if isinstance(r, tuple):
            s.union(cmd.target.name, r[1])
        elif isinstance(r, Ty):
            s.meet(cmd.target.name, r)
        else:
            s.add(cmd.target.name)
    elif isinstance(cmd, ast.Havoc):
        _annot(s, cmd.target)
        s.add(cmd.target.name)
    elif isinstance(cmd, ast.Phi):
        _annot(s, cmd.target)
        for arm in cmd.arms:
            s.union(cmd.target.name, arm.value)
    elif isinstance(cmd, ast.GetRef):
        _annot(s, cmd.target)
        s.meet(cmd.target.name, Ty.INT)
        s.meet(cmd.ref, Ty.REF)
    elif isinstance(cmd, ast.Borrow):
        _annot(s, cmd.target)
        s.meet(cmd.target.name, Ty.REF)
        expect(cmd.base, Ty.BYTEMAP)
        expect(cmd.index, Ty.INT)
    elif isinstance(cmd, ast.BorrowMut):
        _annot(s, cmd.ref_target)
        _annot(s, cmd.map_target)
        s.meet(cmd.ref_target.name, Ty.REF)
        s.meet(cmd.map_target.name, Ty.BYTEMAP)
        expect(cmd.base, Ty.BYTEMAP)
        expect(cmd.index, Ty.INT)
    elif isinstance(cmd, ast.BorrowRef):
        _annot(s, cmd.target)
        s.meet(cmd.target.name, Ty.REF)
        s.meet(cmd.src, Ty.REF)
    elif isinstance(cmd, ast.BorrowRefMut):
        _annot(s, cmd.ref_target)
        _annot(s, cmd.cont_target)
        s.meet(cmd.ref_target.name, Ty.REF)
        s.meet(cmd.cont_target.name, Ty.REF)
        s.meet(cmd.src, Ty.REF)
    elif isinstance(cmd, ast.PutRef):
        _annot(s, cmd.target)
        s.meet(cmd.target.name, Ty.REF)
        s.meet(cmd.ref, Ty.REF)
        expect(cmd.value, Ty.INT)
    elif isinstance(cmd, ast.Release):
        s.meet(cmd.ref, Ty.REF)
    elif isinstance(cmd, ast.Assume):
        expect(cmd.cond, Ty.BOOL)
    elif isinstance(cmd, ast.Assert):
        s.meet(cmd.cond_name, Ty.BOOL)
    else:
        raise TypeError(f"unknown command node {type(cmd).__name__}")
