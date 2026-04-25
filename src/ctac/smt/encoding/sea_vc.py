from __future__ import annotations

import re
from collections import defaultdict
from dataclasses import dataclass
from typing import Callable

from ctac.analysis import analyze_dsa, analyze_use_before_def, extract_def_use
from ctac.analysis.symbols import canonical_symbol
from ctac.ast.nodes import (
    ApplyExpr,
    AssertCmd,
    AssignExpCmd,
    AssignHavocCmd,
    AssumeExpCmd,
    ConstExpr,
    SymbolRef,
    TacExpr,
)
from ctac.smt.encoding.base import EncoderContext, SmtEncodingError, SmtEncoder
from ctac.smt.encoding.path_skeleton import (
    block_by_id,
    block_guard,
    blk_var_name,
    predecessor_edges,
    sanitize_ident,
)
from ctac.smt.model import SmtDeclaration, SmtScript
from ctac.ast.bit_mask import (
    high_mask_clear_low_k as _is_high_mask_clear_low_k,
    low_mask_width as _is_low_mask,
    shifted_contiguous_mask,
)
from ctac.ast.range_constraints import match_inclusive_range_constraint

_SYMBOL_LINE = re.compile(r"^\s*([A-Za-z_][A-Za-z0-9_]*):([A-Za-z0-9_]+)\s*$")
_BASE_SYMBOL = re.compile(r"^(.*):\d+$")
_TYPED_CONST = re.compile(
    r"^(?P<num>(?:-?[0-9]+|0[xX][0-9a-fA-F_]+))\((?P<tag>[A-Za-z0-9_]+)\)$"
)
_SAFE_MATH_NARROW_BIF = re.compile(r"^safe_math_narrow_bv(?P<w>\d+):bif$")
_IDENT_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")

_BV256_MOD = 1 << 256
_BV256_MAX = _BV256_MOD - 1
_BLANK_LINE_MARKER = "__CTAC_BLANK_LINE__"


def _sort_from_tag(tag: str) -> str | None:
    t = tag.lower()
    if t == "bool":
        return "Bool"
    if t == "int":
        return "Int"
    if t.startswith("bv") and t[2:].isdigit():
        return tag
    return None


def _parse_symbol_sorts(symbol_table_text: str) -> dict[str, str]:
    out: dict[str, str] = {}
    for line in symbol_table_text.splitlines():
        m = _SYMBOL_LINE.match(line)
        if m is None:
            continue
        out[m.group(1)] = _sort_from_tag(m.group(2)) or m.group(2)
    return out


def _parse_int_token(token: str) -> int:
    t = token.replace("_", "").strip()
    if t.startswith(("0x", "0X")):
        return int(t, 16)
    return int(t, 10)


def _parse_const(token: str) -> int:
    tok = token.strip()
    m = _TYPED_CONST.fullmatch(tok)
    if m is not None:
        return _parse_int_token(m.group("num"))
    return _parse_int_token(tok)


def _is_pow2(n: int) -> int | None:
    if n <= 0:
        return None
    if n & (n - 1) != 0:
        return None
    return n.bit_length() - 1


def _or_terms(terms: list[str]) -> str:
    uniq: list[str] = []
    seen: set[str] = set()
    for t in terms:
        if t in seen:
            continue
        seen.add(t)
        uniq.append(t)
    if not uniq:
        return "false"
    if "true" in uniq:
        return "true"
    uniq = [t for t in uniq if t != "false"]
    if not uniq:
        return "false"
    if len(uniq) == 1:
        return uniq[0]
    return f"(or {' '.join(uniq)})"


def _and_terms(terms: list[str]) -> str:
    if not terms:
        return "true"
    out: list[str] = []
    seen: set[str] = set()
    for t in terms:
        if t in seen:
            continue
        seen.add(t)
        out.append(t)
    if "false" in out:
        return "false"
    out = [t for t in out if t != "true"]
    if not out:
        return "true"
    if len(out) == 1:
        return out[0]
    return f"(and {' '.join(out)})"


def _implies(lhs: str, rhs: str) -> str:
    if lhs == "true":
        return rhs
    if lhs == "false":
        return "true"
    if rhs == "true":
        return "true"
    return f"(=> {lhs} {rhs})"


def _at_most_one_terms(terms: list[str]) -> list[str]:
    uniq: list[str] = []
    seen: set[str] = set()
    for t in terms:
        if t == "false" or t in seen:
            continue
        seen.add(t)
        uniq.append(t)
    if len(uniq) <= 1:
        return []
    out: list[str] = []
    for i in range(len(uniq)):
        for j in range(i + 1, len(uniq)):
            out.append(f"(or (not {uniq[i]}) (not {uniq[j]}))")
    return out


def _simplify_ite(cond: str, then_term: str, else_term: str, *, sort: str) -> str:
    if then_term == else_term:
        return then_term
    if cond == "true":
        return then_term
    if cond == "false":
        return else_term
    # These are always safe/desired if the leaves are boolean literals,
    # even when sort inference upstream is imperfect.
    if then_term == "true" and else_term == "false":
        return cond
    if then_term == "false" and else_term == "true":
        return f"(not {cond})"
    if sort == "Bool":
        if then_term == "true":
            return _or_terms([cond, else_term])
        if else_term == "false":
            return _and_terms([cond, then_term])
        if then_term == "false":
            return _and_terms([f"(not {cond})", else_term])
        if else_term == "true":
            return _or_terms([f"(not {cond})", then_term])
    return f"(ite {cond} {then_term} {else_term})"


def _xor_axiom_define_fun() -> str:
    return (
        "(define-fun bv256_xor_axiom ((x Int) (y Int)) Bool "
        "(=> (and (<= 0 x 1) (<= 0 y 1)) "
        "(= (bv256_xor x y) (ite (= x y) 0 1))))"
    )


_UF_AXIOM_DEFINE_BY_UF: dict[str, tuple[str, Callable[[], str]]] = {
    "bv256_xor": ("bv256_xor_axiom", _xor_axiom_define_fun),
}


def _order_constant_defs(const_defs: dict[str, str], *, predefined: set[str]) -> list[str]:
    deps: dict[str, set[str]] = {}
    for name, expr in const_defs.items():
        refs = set(_IDENT_RE.findall(expr))
        deps[name] = {r for r in refs if r in const_defs and r != name}

    ordered: list[str] = []
    temp: set[str] = set()
    perm: set[str] = set()

    def visit(n: str) -> None:
        if n in perm:
            return
        if n in temp:
            return
        temp.add(n)
        for d in sorted(deps.get(n, ())):
            if d in predefined:
                continue
            visit(d)
        temp.remove(n)
        perm.add(n)
        ordered.append(n)

    for n in sorted(const_defs):
        visit(n)
    return ordered


def _iter_expr_symbols(expr: TacExpr):
    if isinstance(expr, SymbolRef):
        yield canonical_symbol(expr.name, strip_var_suffixes=True)
        return
    if isinstance(expr, ApplyExpr):
        # TAC Apply(...) encodes callee in args[0] (a function tag/symbol-like token),
        # which is not a program variable and must not be harvested as an SMT const.
        start_idx = 1 if expr.op == "Apply" and expr.args else 0
        for arg in expr.args[start_idx:]:
            yield from _iter_expr_symbols(arg)


def _expr_is_bool_like(expr: TacExpr) -> bool:
    if isinstance(expr, ConstExpr):
        return expr.value.strip() in {"true", "false"}
    if isinstance(expr, ApplyExpr):
        op = expr.op
        if op in {"Not", "LNot", "LAnd", "LOr", "Eq", "Ne", "Neq", "Lt", "Le", "Gt", "Ge"}:
            return True
        if op == "Ite" and len(expr.args) == 3:
            # TAC inputs are assumed well-typed, so if either branch is Bool-like
            # the other branch is also Bool-like.
            return _expr_is_bool_like(expr.args[1]) or _expr_is_bool_like(expr.args[2])
    return False


def _expr_refine_bounds(expr: TacExpr, *, symbol: str) -> tuple[bool, bool]:
    """
    Return (has_lower_bound, has_upper_bound) for immediate refinement of symbol.
    Conservative: only recognizes symbol-vs-constant comparisons and range conjunctions.
    """
    range_match = match_inclusive_range_constraint(expr, strip_var_suffixes=True)
    if range_match is not None and range_match.symbol == symbol:
        return True, True
    if isinstance(expr, ApplyExpr):
        op = expr.op
        if op in {"Lt", "Le", "Gt", "Ge"} and len(expr.args) == 2:
            a0, a1 = expr.args
            # Keep this conservative: only treat direct symbol-vs-constant
            # comparisons as an immediate range refinement.
            if (
                isinstance(a0, SymbolRef)
                and isinstance(a1, ConstExpr)
                and canonical_symbol(a0.name, strip_var_suffixes=True) == symbol
            ):
                if op in {"Gt", "Ge"}:
                    return True, False
                return False, True
            if (
                isinstance(a0, ConstExpr)
                and isinstance(a1, SymbolRef)
                and canonical_symbol(a1.name, strip_var_suffixes=True) == symbol
            ):
                if op in {"Lt", "Le"}:
                    # const <sym / const <= sym -> lower bound on sym
                    return True, False
                # const > sym / const >= sym -> upper bound on sym
                return False, True
        if op == "LAnd":
            has_lo = False
            has_hi = False
            for arg in expr.args:
                lo, hi = _expr_refine_bounds(arg, symbol=symbol)
                has_lo = has_lo or lo
                has_hi = has_hi or hi
            return has_lo, has_hi
    return False, False


@dataclass
class SeaVcEncoder(SmtEncoder):
    name: str = "sea_vc"

    def encode(self, ctx: EncoderContext) -> SmtScript:
        program = ctx.tac_file.program
        if not program.blocks:
            raise SmtEncodingError("program has no blocks")
        entry_block_id = program.blocks[0].id

        du = extract_def_use(program)
        dsa = analyze_dsa(program, def_use=du)
        if not dsa.is_valid:
            first = dsa.issues[0]
            raise SmtEncodingError(f"DSA precondition failed: {first.kind} at {first.block_id}:{first.cmd_index}")

        # Use-before-def precondition: every used symbol must have at
        # least one reaching def. DSA only flags multiple-defs and
        # shape; a symbol with zero defs slips past it. sea_vc would
        # then encode the symbol as a free SMT const — z3 may pick a
        # value the program never could have produced, masking real
        # encoder/program bugs. Reject explicitly so the merged
        # program's structural integrity is what's verified.
        ubd = analyze_use_before_def(program, def_use=du)
        if ubd.issues:
            first = ubd.issues[0]
            raise SmtEncodingError(
                f"use-before-def: {first.symbol!r} at "
                f"{first.block_id}:{first.cmd_index} "
                f"({first.cmd_kind}) — symbol used with no reaching def"
            )

        dynamic_symbols = {x.symbol for x in dsa.dynamic_assignments}
        raw_sorts = _parse_symbol_sorts(ctx.tac_file.symbol_table_text)
        symbols: set[str] = set(du.symbol_to_id)
        bool_hints: set[str] = set()
        for block in program.blocks:
            for cmd in block.commands:
                if isinstance(cmd, AssignExpCmd):
                    lhs = canonical_symbol(cmd.lhs, strip_var_suffixes=True)
                    symbols.add(lhs)
                    symbols.update(_iter_expr_symbols(cmd.rhs))
                    if _expr_is_bool_like(cmd.rhs):
                        bool_hints.add(lhs)
                elif isinstance(cmd, AssignHavocCmd):
                    symbols.add(canonical_symbol(cmd.lhs, strip_var_suffixes=True))
                elif isinstance(cmd, AssumeExpCmd):
                    symbols.update(_iter_expr_symbols(cmd.condition))
                    if isinstance(cmd.condition, SymbolRef):
                        bool_hints.add(canonical_symbol(cmd.condition.name, strip_var_suffixes=True))
                elif isinstance(cmd, AssertCmd):
                    symbols.update(_iter_expr_symbols(cmd.predicate))
                    if isinstance(cmd.predicate, SymbolRef):
                        bool_hints.add(canonical_symbol(cmd.predicate.name, strip_var_suffixes=True))
                elif hasattr(cmd, "condition") and isinstance(getattr(cmd, "condition"), str):
                    # Jumpi-style symbol condition.
                    cond_name = canonical_symbol(getattr(cmd, "condition"), strip_var_suffixes=True)
                    symbols.add(cond_name)
                    bool_hints.add(cond_name)
        assert_expr = ctx.assert_site.command.predicate
        symbols.update(_iter_expr_symbols(assert_expr))
        ordered_symbols = sorted(symbols)

        symbol_term: dict[str, str] = {s: sanitize_ident(s) for s in ordered_symbols}
        memory_symbols: set[str] = set()
        symbol_sort: dict[str, str] = {}
        for s in ordered_symbols:
            base = _BASE_SYMBOL.sub(r"\1", s)
            raw = raw_sorts.get(s) or raw_sorts.get(base) or "bv256"
            raw_lc = raw.lower()
            if raw_lc in {"bytemap", "ghostmap"}:
                memory_symbols.add(s)
                # Placeholder — memory symbols are encoded as UFs, not SMT
                # values; this entry exists so the few sites that still
                # look up symbol_sort[sym] don't need a second special case.
                symbol_sort[s] = "Int"
            else:
                symbol_sort[s] = "Bool" if (raw_lc == "bool" or s in bool_hints) else "Int"

        # Reject multi-def bytemaps early: sea_vc models each memory symbol
        # as a single uninterpreted function, so multiple havocs (or any
        # mix of defs) for the same bytemap aren't representable today.
        multi_def_memory = sorted(
            sym
            for sym in memory_symbols
            if len(du.definitions_by_symbol.get(sym, ())) > 1
        )
        if multi_def_memory:
            bad = ", ".join(multi_def_memory)
            raise SmtEncodingError(
                f"bytemap with multiple definitions is not supported in sea_vc: {bad}"
            )

        decls: list[SmtDeclaration] = []
        decl_seen: set[str] = set()
        uf_decl_lines: set[str] = set()
        for s in ordered_symbols:
            nm = symbol_term[s]
            if nm in decl_seen:
                continue
            decl_seen.add(nm)
            if s in memory_symbols:
                uf_decl_lines.add(f"(declare-fun {nm} (Int) Int)")
            else:
                decls.append(SmtDeclaration(name=nm, sort=symbol_sort[s]))
        for b in program.blocks:
            if b.id == entry_block_id:
                continue
            nm = blk_var_name(b.id)
            if nm not in decl_seen:
                decl_seen.add(nm)
                decls.append(SmtDeclaration(name=nm, sort="Bool"))
        decls.append(SmtDeclaration(name="BLK_EXIT", sort="Bool"))

        # DSA partition guard: no symbol encoded as both static and dynamic.
        static_symbols = {sym for sym in du.definitions_by_symbol if sym not in dynamic_symbols}
        if static_symbols & dynamic_symbols:
            bad = ", ".join(sorted(static_symbols & dynamic_symbols))
            raise SmtEncodingError(f"DSA partition violated for symbol(s): {bad}")

        uf_apps: dict[str, set[tuple[str, ...]]] = defaultdict(set)
        memory_apps: set[tuple[str, str]] = set()
        constraints: list[str] = []
        block_pos = {b.id: i for i, b in enumerate(program.blocks)}
        # If a havoc is immediately followed by a range-refining assume over the same
        # symbol, elide only the already-implied side(s) of the default bv256 domain.
        # map: (block_id, cmd_index) -> (has_lower, has_upper)
        havoc_refine_bounds: dict[tuple[str, int], tuple[bool, bool]] = {}
        for b in program.blocks:
            for i in range(len(b.commands) - 1):
                c0 = b.commands[i]
                c1 = b.commands[i + 1]
                if not isinstance(c0, AssignHavocCmd) or not isinstance(c1, AssumeExpCmd):
                    continue
                lhs = canonical_symbol(c0.lhs, strip_var_suffixes=True)
                lo, hi = _expr_refine_bounds(c1.condition, symbol=lhs)
                if lo or hi:
                    havoc_refine_bounds[(b.id, i)] = (lo, hi)
        havoc_counter = 0
        const_defs: dict[str, str] = {}
        const_name_by_value: dict[int, str] = {
            _BV256_MOD: "BV256_MOD",
            _BV256_MAX: "BV256_MAX",
        }

        def _register_const(name: str, expr: str) -> str:
            base = name
            idx = 1
            while name in const_defs and const_defs[name] != expr:
                idx += 1
                name = f"{base}_{idx}"
            const_defs[name] = expr
            return name

        def _const_name_for(n: int) -> str:
            if n in const_name_by_value:
                return const_name_by_value[n]
            pow_k = _is_pow2(n)
            if pow_k is not None:
                name = _register_const(f"POW2_{pow_k}", str(n))
            else:
                lo_mask_k = _is_low_mask(n)
                hi_mask_k = _is_high_mask_clear_low_k(n)
                if lo_mask_k is not None and lo_mask_k >= 32:
                    p = _const_name_for(1 << lo_mask_k)
                    name = _register_const(f"MASK_LOW_{lo_mask_k}", f"(- {p} 1)")
                elif hi_mask_k is not None and hi_mask_k >= 1:
                    p = _const_name_for(1 << hi_mask_k)
                    name = _register_const(f"MASK_CLEAR_LOW_{hi_mask_k}", f"(- BV256_MOD {p})")
                else:
                    abs_n = abs(n)
                    if 0 < n < _BV256_MOD:
                        delta = _BV256_MOD - n
                        # Prefer symbolic "BV256_MOD - delta" when close to domain upper bound.
                        if 0 < delta <= (1 << 64):
                            d = _int_literal(delta)
                            name = _register_const(f"BV256_MOD_MINUS_{delta}", f"(- BV256_MOD {d})")
                        else:
                            name = _register_const(f"C_{abs_n}", str(n))
                    else:
                        prefix = "NEG_" if n < 0 else ""
                        expr = f"(- {abs_n})" if n < 0 else str(n)
                        name = _register_const(f"{prefix}C_{abs_n}", expr)
            const_name_by_value[n] = name
            return name

        def _int_literal(n: int) -> str:
            if n in {_BV256_MOD, _BV256_MAX}:
                return const_name_by_value[n]
            # Keep small constants inline, lift larger constants for readability.
            if abs(n) < (1 << 16):
                return str(n)
            # Promote especially semantic constants even if moderate size.
            if _is_pow2(n) is not None or _is_low_mask(n) is not None or _is_high_mask_clear_low_k(n) is not None:
                return _const_name_for(n)
            # Only lift generic numerals when truly large.
            if abs(n) < (1 << 64):
                return str(n)
            return _const_name_for(n)

        def add_constraint(expr: str) -> None:
            if expr == "true":
                return
            constraints.append(expr)

        def add_havoc_range_if_bv256(
            sym: str,
            term: str,
            *,
            block_id: str | None = None,
            cmd_index: int | None = None,
        ) -> None:
            base = _BASE_SYMBOL.sub(r"\1", sym)
            raw = (raw_sorts.get(sym) or raw_sorts.get(base) or "").lower()
            if raw == "bv256":
                if block_id is not None and cmd_index is not None and (block_id, cmd_index) in havoc_refine_bounds:
                    # Refined sites merge any remaining domain side into the
                    # immediately following assume instead of standalone asserts.
                    return
                add_constraint(f"(<= 0 {term} BV256_MAX)")

        def declare_havoc(sym: str, block_id: str, cmd_index: int) -> str:
            nonlocal havoc_counter
            havoc_counter += 1
            nm = f"HAVOC_{sanitize_ident(sym)}_{sanitize_ident(block_id)}_{cmd_index}_{havoc_counter}"
            if nm not in decl_seen:
                decl_seen.add(nm)
                decls.append(SmtDeclaration(name=nm, sort=symbol_sort[sym]))
            add_havoc_range_if_bv256(sym, nm, block_id=block_id, cmd_index=cmd_index)
            return nm

        def emit_expr(expr: TacExpr, *, expected_sort: str | None = None) -> tuple[str, str]:
            def to_bool(term: str, sort: str) -> str:
                if sort == "Bool":
                    return term
                # TAC conditions are sometimes encoded as Int/BV expressions.
                return f"(not (= {term} 0))"

            if isinstance(expr, SymbolRef):
                sym = canonical_symbol(expr.name, strip_var_suffixes=True)
                if sym not in symbol_term:
                    raise SmtEncodingError(f"unknown symbol in expression: {expr.name!r}")
                return symbol_term[sym], symbol_sort[sym]
            if isinstance(expr, ConstExpr):
                tok = expr.value.strip()
                if tok in {"true", "false"}:
                    return tok, "Bool"
                val = _parse_const(tok)
                return _int_literal(val), "Int"
            if isinstance(expr, ApplyExpr):
                op = expr.op

                if op == "Apply":
                    if len(expr.args) >= 2 and isinstance(expr.args[0], SymbolRef):
                        callee = expr.args[0].name
                        if _SAFE_MATH_NARROW_BIF.fullmatch(callee):
                            return emit_expr(expr.args[1], expected_sort=expected_sort)
                        uf = f"uf_{sanitize_ident(callee)}"
                        args = [emit_expr(a, expected_sort="Int")[0] for a in expr.args[1:]]
                        ret_sort = expected_sort or "Int"
                        smt_sort = "Bool" if ret_sort == "Bool" else "Int"
                        dom = " ".join("Int" for _ in args)
                        uf_decl_lines.add(f"(declare-fun {uf} ({dom}) {smt_sort})")
                        uf_apps[uf].add(tuple(args))
                        return (f"({uf} {' '.join(args)})" if args else f"({uf})"), smt_sort
                    raise SmtEncodingError("unsupported Apply(...) form")

                if op in {"Not", "LNot"}:
                    a, s = emit_expr(expr.args[0], expected_sort="Bool")
                    return f"(not {to_bool(a, s)})", "Bool"
                if op in {"LAnd", "LOr"}:
                    # Normalize range conjunctions into chained inequality:
                    # lo <= x && x <= hi  ==>  (<= lo x hi)
                    if op == "LAnd":
                        range_match = match_inclusive_range_constraint(expr, strip_var_suffixes=True)
                        if range_match is not None and range_match.symbol in symbol_term:
                            x_term = symbol_term[range_match.symbol]
                            lo_term, _ = emit_expr(range_match.lower, expected_sort="Int")
                            hi_term, _ = emit_expr(range_match.upper, expected_sort="Int")
                            return f"(<= {lo_term} {x_term} {hi_term})", "Bool"
                    smt = "and" if op == "LAnd" else "or"
                    terms: list[str] = []
                    for arg in expr.args:
                        a, s = emit_expr(arg, expected_sort="Bool")
                        terms.append(to_bool(a, s))
                    return (_and_terms(terms) if smt == "and" else _or_terms(terms)), "Bool"
                if op in {"Eq", "Ne", "Neq"}:
                    a1, _ = emit_expr(expr.args[0])
                    a2, _ = emit_expr(expr.args[1])
                    eq = f"(= {a1} {a2})"
                    return (eq, "Bool") if op == "Eq" else (f"(not {eq})", "Bool")
                if op in {"Lt", "Le", "Gt", "Ge"}:
                    a1, _ = emit_expr(expr.args[0], expected_sort="Int")
                    a2, _ = emit_expr(expr.args[1], expected_sort="Int")
                    smt = {"Lt": "<", "Le": "<=", "Gt": ">", "Ge": ">="}[op]
                    return f"({smt} {a1} {a2})", "Bool"
                if op in {"Add", "Sub", "Mul"}:
                    a1, _ = emit_expr(expr.args[0], expected_sort="Int")
                    a2, _ = emit_expr(expr.args[1], expected_sort="Int")
                    smt = {"Add": "+", "Sub": "-", "Mul": "*"}[op]
                    return f"(mod ({smt} {a1} {a2}) BV256_MOD)", "Int"
                if op in {"Div", "Mod", "IntAdd", "IntSub", "IntMul", "IntDiv", "IntMod"}:
                    a1, _ = emit_expr(expr.args[0], expected_sort="Int")
                    a2, _ = emit_expr(expr.args[1], expected_sort="Int")
                    smt = {
                        "Div": "div",
                        "Mod": "mod",
                        "IntAdd": "+",
                        "IntSub": "-",
                        "IntMul": "*",
                        "IntDiv": "div",
                        "IntMod": "mod",
                    }[op]
                    return f"({smt} {a1} {a2})", "Int"
                if op in {"Shl", "BvShl", "BVShl", "LShift", "ShiftLeft"}:
                    if len(expr.args) != 2:
                        raise SmtEncodingError(f"{op} expects two args")
                    x, _ = emit_expr(expr.args[0], expected_sort="Int")
                    if not isinstance(expr.args[1], ConstExpr):
                        uf = "bv256_shl"
                        y, _ = emit_expr(expr.args[1], expected_sort="Int")
                        uf_decl_lines.add(f"(declare-fun {uf} (Int Int) Int)")
                        uf_apps[uf].add((x, y))
                        return f"({uf} {x} {y})", "Int"
                    k = _parse_const(expr.args[1].value)
                    if k < 0:
                        raise SmtEncodingError("negative shift is unsupported")
                    return f"(* {x} {_int_literal(1 << k)})", "Int"
                if op in {"ShiftRightLogical", "Lshr", "LShr", "BvLShr", "BVLShr"}:
                    if len(expr.args) != 2:
                        raise SmtEncodingError(f"{op} expects two args")
                    x, _ = emit_expr(expr.args[0], expected_sort="Int")
                    if not isinstance(expr.args[1], ConstExpr):
                        uf = "bv256_lshr"
                        y, _ = emit_expr(expr.args[1], expected_sort="Int")
                        uf_decl_lines.add(f"(declare-fun {uf} (Int Int) Int)")
                        uf_apps[uf].add((x, y))
                        return f"({uf} {x} {y})", "Int"
                    k = _parse_const(expr.args[1].value)
                    if k < 0:
                        raise SmtEncodingError("negative shift is unsupported")
                    return f"(div {x} {_int_literal(1 << k)})", "Int"
                if op in {"BAnd", "BitAnd", "BvAnd", "BVAnd", "BWAnd", "BWAND"}:
                    if len(expr.args) != 2:
                        raise SmtEncodingError(f"{op} expects two args")
                    left, right = expr.args
                    x_t, _ = emit_expr(left, expected_sort="Int")
                    y_t, _ = emit_expr(right, expected_sort="Int")
                    k_low = None
                    k_high = None
                    m: int | None = None
                    if isinstance(right, ConstExpr):
                        m = _parse_const(right.value)
                        k_low = _is_low_mask(m)
                        k_high = _is_high_mask_clear_low_k(m)
                        target = x_t
                    elif isinstance(left, ConstExpr):
                        m = _parse_const(left.value)
                        k_low = _is_low_mask(m)
                        k_high = _is_high_mask_clear_low_k(m)
                        target = y_t
                    else:
                        target = x_t
                    if k_low is not None:
                        return f"(mod {target} {_int_literal(1 << k_low)})", "Int"
                    if k_high is not None:
                        p = _int_literal(1 << k_high)
                        return f"(* (div {target} {p}) {p})", "Int"
                    if m is not None:
                        sw = shifted_contiguous_mask(m)
                        if sw is not None:
                            lo, w = sw
                            if lo > 0:
                                pow_lo = _int_literal(1 << lo)
                                pow_w = _int_literal(1 << w)
                                return f"(* (mod (div {target} {pow_lo}) {pow_w}) {pow_lo})", "Int"
                    uf = "bv256_and"
                    uf_decl_lines.add(f"(declare-fun {uf} (Int Int) Int)")
                    uf_apps[uf].add((x_t, y_t))
                    return f"({uf} {x_t} {y_t})", "Int"
                if op in {"BXor", "BitXor", "BvXor", "BVXor", "Xor", "BWXor", "BWXOr", "BWXOR"}:
                    a1, _ = emit_expr(expr.args[0], expected_sort="Int")
                    a2, _ = emit_expr(expr.args[1], expected_sort="Int")
                    uf = "bv256_xor"
                    uf_decl_lines.add(f"(declare-fun {uf} (Int Int) Int)")
                    uf_apps[uf].add((a1, a2))
                    return f"({uf} {a1} {a2})", "Int"
                if op in {"BOr", "BitOr", "BvOr", "BVOr", "BWOr", "BWOR"}:
                    a1, _ = emit_expr(expr.args[0], expected_sort="Int")
                    a2, _ = emit_expr(expr.args[1], expected_sort="Int")
                    uf = "bv256_or"
                    uf_decl_lines.add(f"(declare-fun {uf} (Int Int) Int)")
                    uf_apps[uf].add((a1, a2))
                    return f"({uf} {a1} {a2})", "Int"
                if op == "Ite":
                    if len(expr.args) != 3:
                        raise SmtEncodingError("Ite expects three args")
                    c, cs = emit_expr(expr.args[0], expected_sort="Bool")
                    c = to_bool(c, cs)
                    t, ts = emit_expr(expr.args[1], expected_sort=expected_sort)
                    e, es = emit_expr(expr.args[2], expected_sort=ts)
                    if ts != es:
                        raise SmtEncodingError("Ite branch sort mismatch")
                    return _simplify_ite(c, t, e, sort=ts), ts
                if op == "Select":
                    if len(expr.args) != 2:
                        raise SmtEncodingError("Select expects (memory, index)")
                    mem, idx = expr.args
                    if not isinstance(mem, SymbolRef):
                        raise SmtEncodingError(
                            "Select memory argument must be a SymbolRef"
                        )
                    mem_name = canonical_symbol(mem.name, strip_var_suffixes=True)
                    if mem_name not in memory_symbols:
                        raise SmtEncodingError(
                            f"Select on non-memory symbol: {mem_name!r}"
                        )
                    idx_term, _ = emit_expr(idx, expected_sort="Int")
                    # Bytemap cells are bv256-valued in TAC, but the SMT UF
                    # has sort ``Int -> Int`` with no domain constraint —
                    # z3 is free to pick negative or >BV256_MAX values that
                    # satisfy the Int-level VC but can't replay through a
                    # bv256 register. Track each application so we can emit
                    # a per-app range axiom below.
                    memory_apps.add((symbol_term[mem_name], idx_term))
                    return f"({symbol_term[mem_name]} {idx_term})", "Int"

                raise SmtEncodingError(f"unsupported operator in sea_vc: {op}")
            raise SmtEncodingError(f"unsupported expression node: {expr!r}")

        # Static assignment encoding and assume constraints.
        for ds in du.definitions:
            if ds.symbol in dynamic_symbols:
                continue
            b = block_by_id(program, ds.block_id)
            cmd = b.commands[ds.cmd_index]
            if isinstance(cmd, AssignExpCmd):
                lhs = symbol_term[ds.symbol]
                rhs, _ = emit_expr(cmd.rhs, expected_sort=symbol_sort[ds.symbol])
                add_constraint(f"(= {lhs} {rhs})")
            elif isinstance(cmd, AssignHavocCmd):
                add_havoc_range_if_bv256(ds.symbol, symbol_term[ds.symbol], block_id=ds.block_id, cmd_index=ds.cmd_index)
        static_end = len(constraints)

        for block in program.blocks:
            guard = block_guard(block.id, entry_block_id=entry_block_id)
            has_assume_in_block = any(isinstance(c, AssumeExpCmd) for c in block.commands)
            for idx, cmd in enumerate(block.commands):
                if isinstance(cmd, AssumeExpCmd):
                    cond_expr = cmd.condition
                    # If the previous command is a havoc with immediate refinement,
                    # merge the remaining bv256-domain side(s) into this assume
                    # at AST level so range normalization can produce chained
                    # inequalities `(<= lo x hi)`.
                    if idx > 0:
                        prev = block.commands[idx - 1]
                        if isinstance(prev, AssignHavocCmd):
                            prev_sym = canonical_symbol(prev.lhs, strip_var_suffixes=True)
                            lo_hi = havoc_refine_bounds.get((block.id, idx - 1))
                            if lo_hi is not None and prev_sym in symbol_term:
                                base = _BASE_SYMBOL.sub(r"\1", prev_sym)
                                raw = (raw_sorts.get(prev_sym) or raw_sorts.get(base) or "").lower()
                                if raw == "bv256":
                                    has_lo, has_hi = lo_hi
                                    extra_preds: list[TacExpr] = []
                                    if not has_lo:
                                        extra_preds.append(
                                            ApplyExpr("Ge", (SymbolRef(prev_sym), ConstExpr("0")))
                                        )
                                    if not has_hi:
                                        extra_preds.append(
                                            ApplyExpr("Le", (SymbolRef(prev_sym), ConstExpr(str(_BV256_MAX))))
                                        )
                                    if extra_preds:
                                        cond_expr = ApplyExpr("LAnd", (cond_expr, *extra_preds))

                    cond, s = emit_expr(cond_expr, expected_sort="Bool")
                    if s != "Bool":
                        raise SmtEncodingError("Assume condition must be Bool")
                    add_constraint(_implies(guard, cond))
            if has_assume_in_block:
                remaining_blocks = program.blocks[program.blocks.index(block) + 1 :]
                if any(any(isinstance(c, AssumeExpCmd) for c in b.commands) for b in remaining_blocks):
                    constraints.append(_BLANK_LINE_MARKER)
        assume_end = len(constraints)

        # Dynamic assignment groups as compact ITEs.
        dynamic_by_symbol: dict[str, list] = defaultdict(list)
        for d in dsa.dynamic_assignments:
            dynamic_by_symbol[d.symbol].append(d)
        for sym, rows in sorted(dynamic_by_symbol.items()):
            grouped_conds: dict[str, list[str]] = defaultdict(list)
            rhs_rank: dict[str, int] = {}
            for row in rows:
                b = block_by_id(program, row.block_id)
                cmd = b.commands[row.cmd_index]
                if isinstance(cmd, AssignExpCmd):
                    rhs, _ = emit_expr(cmd.rhs, expected_sort=symbol_sort[sym])
                elif isinstance(cmd, AssignHavocCmd):
                    rhs = declare_havoc(sym, row.block_id, row.cmd_index)
                else:
                    raise SmtEncodingError(
                        f"dynamic assignment for {sym} must be AssignExpCmd/AssignHavocCmd"
                    )
                grouped_conds[rhs].append(block_guard(row.block_id, entry_block_id=entry_block_id))
                rhs_rank[rhs] = min(rhs_rank.get(rhs, 10**9), block_pos.get(row.block_id, 10**9))

            cases: list[tuple[str, str]] = []
            for rhs, conds in grouped_conds.items():
                cond = _or_terms(conds)
                if cond == "false":
                    continue
                cases.append((cond, rhs))
            cases.sort(key=lambda x: rhs_rank.get(x[1], 10**9))
            if not cases:
                raise SmtEncodingError(f"no dynamic cases found for symbol {sym}")
            value = cases[-1][1]
            for cond, rhs in reversed(cases[:-1]):
                value = _simplify_ite(cond, rhs, value, sort=symbol_sort[sym])
            add_constraint(f"(= {symbol_term[sym]} {value})")
        dynamic_end = len(constraints)

        # CFG predecessor constraints.
        preds = predecessor_edges(program, symbol_term_by_name=symbol_term)
        for block in program.blocks:
            if block.id == entry_block_id:
                continue
            lhs = blk_var_name(block.id)
            edge_terms: list[str] = []
            pred_block_terms: list[str] = []
            for pe in preds.get(block.id, []):
                pred_guard = block_guard(pe.pred_block_id, entry_block_id=entry_block_id)
                edge_terms.append(_and_terms([pred_guard, pe.branch_cond]))
                pred_block_terms.append(pred_guard)
            # Edge-level predecessor feasibility (with branch conditions).
            add_constraint(_implies(lhs, _or_terms(edge_terms)))
            # Block-level predecessor existence (without edge conditions), to pair
            # with exclusivity over the same predecessor-block variables.
            add_constraint(_implies(lhs, _or_terms(pred_block_terms)))
            # Exclusivity is over predecessor blocks, not edge predicates.
            for amo in _at_most_one_terms(pred_block_terms):
                add_constraint(_implies(lhs, amo))
        cfg_end = len(constraints)

        # Exit objective bound to assert block and failing assert predicate.
        assert_guard = block_guard(ctx.assert_site.block_id, entry_block_id=entry_block_id)
        assert_cond, assert_sort = emit_expr(assert_expr, expected_sort="Bool")
        if assert_sort != "Bool":
            raise SmtEncodingError("Assert predicate must lower to Bool")
        exit_rhs = _and_terms([f"(not {assert_cond})", assert_guard])
        add_constraint(_implies("BLK_EXIT", exit_rhs))
        add_constraint("BLK_EXIT")
        exit_end = len(constraints)

        # Render definitions + assertions.
        out_lines: list[str] = [
            f"(define-fun BV256_MOD () Int {_BV256_MOD})",
            "(define-fun BV256_MAX () Int (- BV256_MOD 1))",
        ]
        for name in _order_constant_defs(const_defs, predefined={"BV256_MOD", "BV256_MAX"}):
            if name in {"BV256_MOD", "BV256_MAX"}:
                continue
            out_lines.append(f"(define-fun {name} () Int {const_defs[name]})")
        out_lines.extend(sorted(uf_decl_lines))

        def emit_banner(title: str) -> None:
            bar = "+" + ("=" * 78) + "+"
            pad = " " * 2
            out_lines.append("")
            out_lines.append(f"; {bar}")
            out_lines.append("; |                                                                              |")
            out_lines.append(f"; |{pad}{title:<76}|")
            out_lines.append("; |                                                                              |")
            out_lines.append(f"; {bar}")
            out_lines.append("")

        # Emit UF axiom definitions once, then instantiate per application.
        emitted_axiom_funs: set[str] = set()
        printed_axiom_banner = False
        for uf in sorted(uf_apps):
            axiom_info = _UF_AXIOM_DEFINE_BY_UF.get(uf)
            if axiom_info is None:
                continue
            axiom_fun_name, axiom_fun_builder = axiom_info
            if not printed_axiom_banner:
                emit_banner("Axiom Instantiations")
                printed_axiom_banner = True
            if axiom_fun_name not in emitted_axiom_funs:
                out_lines.append(axiom_fun_builder())
                emitted_axiom_funs.add(axiom_fun_name)
            out_lines.append(f"; instantiate {axiom_fun_name} for each {uf} application")
            for args in sorted(uf_apps[uf]):
                out_lines.append(f"(assert ({axiom_fun_name} {' '.join(args)}))")

        # Memory cells are bv256-valued. Without a per-application range
        # axiom, z3 can pick negative or >BV256_MAX values that satisfy the
        # Int-level VC but can't be loaded back into a bv256 register, which
        # breaks model replay through ``ctac run``. One ``0 <= M(idx) <=
        # BV256_MAX`` per unique application is enough.
        if memory_apps:
            if not printed_axiom_banner:
                emit_banner("Axiom Instantiations")
                printed_axiom_banner = True
            out_lines.append("; memory bv256-range axioms (one per Select application)")
            for mem_name, idx_term in sorted(memory_apps):
                out_lines.append(
                    f"(assert (<= 0 ({mem_name} {idx_term}) BV256_MAX))"
                )

        tac_named_i = 0

        def emit_constraint_section(name: str, start: int, end: int, *, name_asserts: bool) -> None:
            nonlocal tac_named_i
            emit_banner(name)
            for c in constraints[start:end]:
                if c == _BLANK_LINE_MARKER:
                    out_lines.append("")
                elif name_asserts and ctx.unsat_core:
                    tac_named_i += 1
                    out_lines.append(f"(assert (! {c} :named TAC_{tac_named_i}))")
                else:
                    out_lines.append(f"(assert {c})")

        emit_constraint_section(
            "Static Assignments and Havoc Domain", 0, static_end, name_asserts=True
        )
        emit_constraint_section("Assumptions", static_end, assume_end, name_asserts=True)
        emit_constraint_section(
            "Dynamic Assignments", assume_end, dynamic_end, name_asserts=True
        )
        emit_constraint_section("CFG Reachability", dynamic_end, cfg_end, name_asserts=False)
        emit_constraint_section(
            "Exit and Assert-Failure Objective", cfg_end, exit_end, name_asserts=False
        )
        # Default to QF_UFNIA so the logic set is consistent across outputs and
        # solver tactics don't have to branch on what this specific VC needed.
        # With ``tight_logic=True`` we narrow to QF_NIA when no uninterpreted
        # functions were actually declared for this VC.
        if uf_decl_lines:
            logic = "QF_UFNIA"
        elif ctx.tight_logic:
            logic = "QF_NIA"
        else:
            logic = "QF_UFNIA"

        return SmtScript(
            logic=logic,
            declarations=tuple(decls),
            assertions=tuple(out_lines),
            comments=(
                "sea_vc: DSA + reachability encoding.",
                "SAT means reachable exit with failing assert and satisfied assumes.",
            ),
            check_sat=True,
            unsat_core=ctx.unsat_core,
        )
