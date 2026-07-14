"""Summary statistics for a Tiny TAC program.

The ``ttac`` analog of ``ctac stats``: command/terminator kinds,
expression ops, the bytemap capability (free / ro / rw), reference and
borrow usage, the type distribution, and shape flags. Reuses the generic
``StatsCollection`` + ``render_plain_stats`` formatting and the
``BytemapCapability`` value strings.

Robust on any parseable program (uses the non-raising ``analyze_types``
for sorts) — including programs that still contain references.
"""

from __future__ import annotations

from collections import Counter

import networkx as nx

from ctac.analysis.model import BytemapCapability
from ctac.tool.stats_model import StatsCollection

from . import ast
from .analysis import analyze_types
from .analysis import cfg as ttac_cfg
from .analysis import check_dsa

_BORROW_CMD_LABEL = {
    ast.Borrow: "borrow",
    ast.BorrowMut: "borrow_mut",
    ast.BorrowRef: "borrow_ref",
    ast.BorrowRefMut: "borrow_ref_mut",
    ast.GetRef: "get_ref",
    ast.PutRef: "put_ref",
    ast.Release: "release",
}

_BINOP_LABEL = {
    "+": "+", "-": "-", "*": "*", "/": "/",
    "<=": "<=", "<": "<", "==": "==", "and": "and", "or": "or",
}


def stats_to_dict(collection: StatsCollection) -> dict[str, object]:
    return {e.path: e.value.value for e in collection.entries()}


def _walk_expr(expr: ast.Expr, ops: Counter, counters: dict[str, int]) -> None:
    if isinstance(expr, ast.Load):
        ops["load"] += 1
        _walk_expr(expr.base, ops, counters)
        _walk_expr(expr.index, ops, counters)
    elif isinstance(expr, ast.Update):
        ops["update"] += 1
        counters["updates"] += 1
        for sub in (expr.base, expr.index, expr.value):
            _walk_expr(sub, ops, counters)
    elif isinstance(expr, ast.BinExpr):
        ops[_BINOP_LABEL.get(expr.op, expr.op)] += 1
        if expr.op == "*" and not isinstance(expr.lhs, ast.Num) and not isinstance(expr.rhs, ast.Num):
            counters["nl_mul"] += 1
        if expr.op == "/" and not isinstance(expr.rhs, ast.Num):
            counters["nl_div"] += 1
        _walk_expr(expr.lhs, ops, counters)
        _walk_expr(expr.rhs, ops, counters)
    elif isinstance(expr, ast.UnExpr):
        ops["not"] += 1
        _walk_expr(expr.operand, ops, counters)
    elif isinstance(expr, ast.IfExpr):
        ops["if"] += 1
        for sub in (expr.cond, expr.then, expr.els):
            _walk_expr(sub, ops, counters)
    elif isinstance(expr, ast.Record):
        ops["record"] += 1
        for sub in (expr.addr, expr.value, expr.promise):
            _walk_expr(sub, ops, counters)
    elif isinstance(expr, ast.Field):
        ops["field"] += 1
        _walk_expr(expr.base, ops, counters)
    # Num / BoolLit / Var / HavocExpr: leaves, not counted as ops.


def _cmd_exprs(cmd: ast.Cmd):
    if isinstance(cmd, ast.Assign):
        yield cmd.rhs
    elif isinstance(cmd, ast.Assume):
        yield cmd.cond
    elif isinstance(cmd, ast.PutRef):
        yield cmd.value
    elif isinstance(cmd, (ast.Borrow, ast.BorrowMut)):
        yield ast.Load(cmd.base, cmd.index)  # the borrowed location is a read


def collect_stats(program: ast.Program) -> StatsCollection:
    s = StatsCollection()
    blocks = program.blocks
    commands = [c for b in blocks for c in b.commands]

    s.add_num("overview.blocks", len(blocks))
    s.add_num("overview.commands", len(commands))
    s.add_str("overview.entry", program.entry or "-")
    s.add_str("overview.exit", program.exit or "-")

    for name, cnt in _ranked(Counter(type(c).__name__ for c in commands)):
        s.add_num(f"command_kinds.{name}", cnt)
    for name, cnt in _ranked(Counter(type(b.terminator).__name__ for b in blocks)):
        s.add_num(f"terminator_kinds.{name}", cnt)

    ops: Counter[str] = Counter()
    counters = {"updates": 0, "nl_mul": 0, "nl_div": 0}
    for cmd in commands:
        for expr in _cmd_exprs(cmd):
            _walk_expr(expr, ops, counters)
    for op, cnt in _ranked(ops):
        s.add_num(f"expression_ops.{op}", cnt)
    s.add_num("nonlinear_ops.multiplication", counters["nl_mul"])
    s.add_num("nonlinear_ops.division", counters["nl_div"])

    types = analyze_types(program)
    sort_of = types.types  # name -> Ty | None
    ty_counts: Counter[str] = Counter()
    for ty in sort_of.values():
        ty_counts[ty.value if ty is not None else "unknown"] += 1
    for kind in ("int", "bool", "bytemap", "ref", "unknown"):
        if ty_counts[kind]:
            s.add_num(f"types.{kind}", ty_counts[kind])
    s.add_str("types.total", _b(types.is_total))

    bytemap_syms = {n for n, ty in sort_of.items() if ty == ast.Ty.BYTEMAP}
    ref_syms = sum(1 for ty in sort_of.values() if ty == ast.Ty.REF)
    borrow_counts: Counter[str] = Counter()
    for cmd in commands:
        label = _BORROW_CMD_LABEL.get(type(cmd))
        if label is not None:
            borrow_counts[label] += 1
    has_borrow = bool(borrow_counts)
    s.add_str("references.reference_free", _b(not has_borrow and ref_syms == 0))
    s.add_num("references.ref_symbols", ref_syms)
    for label in ("borrow", "borrow_mut", "borrow_ref", "borrow_ref_mut",
                  "get_ref", "put_ref", "release"):
        if borrow_counts[label]:
            s.add_num(f"references.{label}", borrow_counts[label])

    loads = ops["load"]
    bytemap_havocs = sum(
        1 for c in commands if isinstance(c, ast.Havoc) and c.target.name in bytemap_syms
    )
    has_bytemap_assign = any(
        isinstance(c, ast.Assign) and c.target.name in bytemap_syms for c in commands
    )
    s.add_str("memory.capability", _capability(bytemap_syms, counters["updates"],
                                               has_bytemap_assign, borrow_counts).value)
    s.add_num("memory.bytemap_symbols", len(bytemap_syms))
    s.add_num("memory.loads", loads)
    s.add_num("memory.updates", counters["updates"])
    s.add_num("memory.havocs", bytemap_havocs)

    s.add_num("shape.asserts", sum(1 for c in commands if isinstance(c, ast.Assert)))
    s.add_num("shape.assumes", sum(1 for c in commands if isinstance(c, ast.Assume)))
    s.add_str("shape.dsa_valid", _b(check_dsa(program).is_valid))
    s.add_str("shape.loop_free", _b(nx.is_directed_acyclic_graph(ttac_cfg.to_digraph(program))))
    return s


def _capability(bytemap_syms, updates, has_bytemap_assign, borrow_counts) -> BytemapCapability:
    if not bytemap_syms:
        return BytemapCapability.BYTEMAP_FREE
    if updates or has_bytemap_assign or borrow_counts["borrow_mut"]:
        return BytemapCapability.BYTEMAP_RW
    return BytemapCapability.BYTEMAP_RO


def _ranked(counter: Counter) -> list[tuple[str, int]]:
    return sorted(counter.items(), key=lambda kv: (-kv[1], kv[0]))


def _b(value: bool) -> str:
    return "true" if value else "false"
