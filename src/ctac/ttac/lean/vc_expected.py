"""Diagnostic mirror of the Lean expected-constraint generator.

Reproduces, over the same ``Term`` tuples the transpiler emits, the
constraint set ``Ttac.Vc.expected`` computes - including the encoder's
constant folds. Used only to explain a failing check before the (slow,
authoritative) ``lake build``; never trusted.
"""

from __future__ import annotations

from collections import Counter
from dataclasses import dataclass

from ctac.ttac import ast
from ctac.ttac.ast import Ty

from .emit import expr_ty
from .naming import Numbering
from .vc import Term, VcAssert, VcMapDef, render_top

TRUE: Term = ("litb", True)
FALSE: Term = ("litb", False)

_BIN_I = {"+": "add", "-": "sub", "*": "mul", "/": "div"}


def mk_imp(g: Term, phi: Term) -> Term:
    if g == TRUE:
        return phi
    if phi == TRUE:
        return TRUE
    return ("imp", g, phi)


def mk_not(a: Term) -> Term:
    if a == TRUE:
        return FALSE
    if a == FALSE:
        return TRUE
    return ("not", a)


def mk_and2(a: Term, b: Term) -> Term:
    if a == TRUE:
        return b
    if b == TRUE:
        return a
    if a == FALSE or b == FALSE:
        return FALSE
    if a == b:
        return a
    return ("and", a, b)


def mk_or2(a: Term, b: Term) -> Term:
    if a == FALSE:
        return b
    if b == FALSE:
        return a
    if a == TRUE or b == TRUE:
        return TRUE
    if a == b:
        return a
    return ("or", a, b)


def dedup1(items: list[Term]) -> list[Term]:
    out: list[Term] = []
    for x in items:
        if x not in out:
            out.append(x)
    return out


def or_chain(first: Term, rest: list[Term]) -> Term:
    if not rest:
        return first
    return ("or", first, or_chain(rest[0], rest[1:]))


def mk_or(items: list[Term]) -> Term:
    u = dedup1(items)
    if TRUE in u:
        return TRUE
    f = [x for x in u if x != FALSE]
    if not f:
        return FALSE
    return or_chain(f[0], f[1:])


def amo_clauses(items: list[Term]) -> list[Term]:
    u = dedup1([x for x in items if x != FALSE])
    return [
        ("or", ("not", u[i]), ("not", u[j]))
        for i in range(len(u))
        for j in range(i + 1, len(u))
    ]


def mk_ite_i(c: Term, t: Term, e: Term) -> Term:
    if t == e:
        return t
    if c == TRUE:
        return t
    if c == FALSE:
        return e
    return ("ite", c, t, e)


def mk_ite_b(c: Term, t: Term, e: Term) -> Term:
    if t == e:
        return t
    if c == TRUE:
        return t
    if c == FALSE:
        return e
    if t == TRUE and e == FALSE:
        return c
    if t == FALSE and e == TRUE:
        return mk_not(c)
    return ("ite", c, t, e)


def lower_mexpr(e: ast.Expr, num: Numbering, types: dict[str, Ty]) -> Term:
    if isinstance(e, ast.Var):
        return ("varM", num.map_regs[e.name])
    if isinstance(e, ast.Update):
        return (
            "store",
            lower_mexpr(e.base, num, types),
            lower_iexpr(e.index, num, types),
            lower_iexpr(e.value, num, types),
        )
    raise TypeError(f"unsupported map expression {type(e).__name__}")


def lower_iexpr(e: ast.Expr, num: Numbering, types: dict[str, Ty]) -> Term:
    if isinstance(e, ast.Num):
        return ("litI", e.value)
    if isinstance(e, ast.Var):
        return ("varI", num.int_regs[e.name])
    if isinstance(e, ast.Load):
        return (
            "select",
            lower_mexpr(e.base, num, types),
            lower_iexpr(e.index, num, types),
        )
    if isinstance(e, ast.BinExpr):
        return (
            _BIN_I[e.op],
            lower_iexpr(e.lhs, num, types),
            lower_iexpr(e.rhs, num, types),
        )
    if isinstance(e, ast.IfExpr):
        return mk_ite_i(
            lower_bexpr(e.cond, num, types),
            lower_iexpr(e.then, num, types),
            lower_iexpr(e.els, num, types),
        )
    raise TypeError(f"unsupported int expression {type(e).__name__}")


def lower_bexpr(e: ast.Expr, num: Numbering, types: dict[str, Ty]) -> Term:
    if isinstance(e, ast.BoolLit):
        return ("litb", e.value)
    if isinstance(e, ast.Var):
        return ("varB", num.bool_regs[e.name])
    if isinstance(e, ast.UnExpr):
        return mk_not(lower_bexpr(e.operand, num, types))
    if isinstance(e, ast.BinExpr):
        if e.op in ("<=", "<"):
            op = "le" if e.op == "<=" else "lt"
            return (op, lower_iexpr(e.lhs, num, types),
                    lower_iexpr(e.rhs, num, types))
        if e.op == "==":
            if expr_ty(e.lhs, types) is Ty.INT:
                return ("eqI", lower_iexpr(e.lhs, num, types),
                        lower_iexpr(e.rhs, num, types))
            return ("eqB", lower_bexpr(e.lhs, num, types),
                    lower_bexpr(e.rhs, num, types))
        mk = mk_and2 if e.op == "and" else mk_or2
        return mk(lower_bexpr(e.lhs, num, types),
                  lower_bexpr(e.rhs, num, types))
    if isinstance(e, ast.IfExpr):
        return mk_ite_b(
            lower_bexpr(e.cond, num, types),
            lower_bexpr(e.then, num, types),
            lower_bexpr(e.els, num, types),
        )
    raise TypeError(f"unsupported bool expression {type(e).__name__}")


def expected_vc(
    program: ast.Program, num: Numbering, types: dict[str, Ty]
) -> list[Term]:
    entry = num.entry_index
    n_blocks = len(program.blocks)

    def guard(b: int) -> Term:
        return TRUE if b == entry else ("blk", b)

    exit_term: Term = ("blk", n_blocks)

    edges: list[tuple[int, int, Term]] = []
    for b, block in enumerate(program.blocks):
        term = block.terminator
        if isinstance(term, ast.Goto):
            edges.append((b, num.block_index[term.target], TRUE))
        elif isinstance(term, ast.IfGoto):
            cond: Term = ("varB", num.bool_regs[term.cond])
            edges.append((b, num.block_index[term.then_target], cond))
            edges.append((b, num.block_index[term.else_target], ("not", cond)))

    def phi_rhs(arms, regs: dict[str, int], mk_ite, var_tag: str) -> Term:
        chain: Term = (var_tag, regs[arms[-1].value])
        for arm in reversed(arms[:-1]):
            chain = mk_ite(
                guard(num.block_index[arm.label]),
                (var_tag, regs[arm.value]),
                chain,
            )
        return chain

    out: list[Term] = []
    assert_site: tuple[int, int] | None = None  # (block idx, cond reg)

    for b, block in enumerate(program.blocks):
        g = guard(b)
        for cmd in block.commands:
            if isinstance(cmd, ast.Assign):
                ty = types[cmd.target.name]
                if ty is Ty.BYTEMAP:
                    continue  # a map definition, not a boolean constraint
                if ty is Ty.INT:
                    eq: Term = ("eqI", ("varI", num.int_regs[cmd.target.name]),
                                lower_iexpr(cmd.rhs, num, types))
                else:
                    eq = ("eqB", ("varB", num.bool_regs[cmd.target.name]),
                          lower_bexpr(cmd.rhs, num, types))
                out.append(mk_imp(g, eq))
            elif isinstance(cmd, ast.Assume):
                out.append(mk_imp(g, lower_bexpr(cmd.cond, num, types)))
            elif isinstance(cmd, ast.Phi):
                ty = types[cmd.target.name]
                if ty is not Ty.BYTEMAP:
                    is_int = ty is Ty.INT
                    regs = num.int_regs if is_int else num.bool_regs
                    mk_ite = mk_ite_i if is_int else mk_ite_b
                    eq_op = "eqI" if is_int else "eqB"
                    var_tag = "varI" if is_int else "varB"
                    out.append(
                        (eq_op, (var_tag, regs[cmd.target.name]),
                         phi_rhs(cmd.arms, regs, mk_ite, var_tag))
                    )
                if len(cmd.arms) >= 2:
                    out.extend(amo_clauses(
                        [guard(num.block_index[a.label]) for a in cmd.arms]
                    ))
            elif isinstance(cmd, ast.Assert):
                assert_site = (b, num.bool_regs[cmd.cond_name])

    for s in range(n_blocks):
        if s == entry:
            continue
        ins = [(p, cond) for (p, t, cond) in edges if t == s]
        g_s = guard(s)
        edge_terms = [mk_and2(guard(p), cond) for p, cond in ins]
        pred_terms = [guard(p) for p, _ in ins]
        out.append(mk_imp(g_s, mk_or(edge_terms)))
        out.append(mk_imp(g_s, mk_or(pred_terms)))
        out.extend(mk_imp(g_s, cl) for cl in amo_clauses(pred_terms))

    if assert_site is not None:
        a_b, ok_reg = assert_site
        out.append(mk_imp(exit_term,
                          mk_and2(guard(a_b), mk_not(("varB", ok_reg)))))
        out.append(exit_term)

    return out


def expected_map_defs(
    program: ast.Program, num: Numbering, types: dict[str, Ty]
) -> list[tuple[int, Term]]:
    """Mirror of ``Ttac.Vc.expectedMapDefs``: one entry per map
    assignment (store/alias, lowered) and per map phi (the same folded
    ITE chain the boolean phi constraint uses)."""
    entry = num.entry_index

    def guard(b: int) -> Term:
        return TRUE if b == entry else ("blk", b)

    out: list[tuple[int, Term]] = []
    for block in program.blocks:
        for cmd in block.commands:
            if (
                isinstance(cmd, (ast.Assign, ast.Phi))
                and types[cmd.target.name] is Ty.BYTEMAP
            ):
                target = num.map_regs[cmd.target.name]
                if isinstance(cmd, ast.Assign):
                    out.append((target, lower_mexpr(cmd.rhs, num, types)))
                else:
                    chain: Term = ("varM", num.map_regs[cmd.arms[-1].value])
                    for arm in reversed(cmd.arms[:-1]):
                        chain = mk_ite_i(
                            guard(num.block_index[arm.label]),
                            ("varM", num.map_regs[arm.value]),
                            chain,
                        )
                    out.append((target, chain))
    return out


@dataclass(frozen=True)
class VcMismatch:
    kind: str  # "unexpected-assert" | "missing-assert"
    #          | "unexpected-map-def" | "missing-map-def"
    detail: str


def precheck_diff(
    actual: list[VcAssert],
    expected: list[Term],
    actual_map_defs: list[VcMapDef] = (),
    expected_defs: list[tuple[int, Term]] = (),
) -> tuple[VcMismatch, ...]:
    """Multiset diff of rendered constraint strings (diagnostic only)."""
    expected_counts = Counter(render_top(t) for t in expected)
    mismatches: list[VcMismatch] = []
    seen: Counter[str] = Counter()
    for a in actual:
        key = render_top(a.term)
        seen[key] += 1
        if key not in expected_counts:
            mismatches.append(VcMismatch(
                kind="unexpected-assert",
                detail=f"line {a.line}: {a.source}",
            ))
    # Note: `vc ⊆ expected` is the Lean-side contract; extra *expected*
    # constraints missing from the smt2 are fine soundness-wise, but a
    # dropped assert usually signals tampering - report it.
    for key in expected_counts:
        if key == ".litB true":
            continue  # encoder-dropped (folded-away) constraints
        if seen[key] == 0:
            mismatches.append(VcMismatch(kind="missing-assert", detail=key))

    expected_def_counts = Counter(
        (target, render_top(t)) for target, t in expected_defs
    )
    seen_defs: Counter[tuple[int, str]] = Counter()
    for md in actual_map_defs:
        key = (md.target, render_top(md.term))
        seen_defs[key] += 1
        if key not in expected_def_counts:
            mismatches.append(VcMismatch(
                kind="unexpected-map-def",
                detail=f"line {md.line}: {md.source}",
            ))
    for key in expected_def_counts:
        if seen_defs[key] == 0:
            mismatches.append(VcMismatch(
                kind="missing-map-def", detail=f"map {key[0]}: {key[1]}"
            ))
    return tuple(mismatches)
