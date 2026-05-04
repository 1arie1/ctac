from __future__ import annotations

import re
from collections import defaultdict
from contextlib import contextmanager
from dataclasses import dataclass
from typing import Callable, Iterator

from ctac.analysis import analyze_dsa, analyze_use_before_def, extract_def_use
from ctac.analysis.symbols import canonical_symbol
from ctac.ast.nodes import (
    ApplyExpr,
    AssertCmd,
    AssignExpCmd,
    AssignHavocCmd,
    AssumeExpCmd,
    ConstExpr,
    JumpiCmd,
    SymbolRef,
    TacExpr,
)
from ctac.smt.cfg import CFG_ENCODERS, CfgEmit, build_cfg_input
from ctac.smt.encoding.base import EncoderContext, SmtEncodingError, SmtEncoder
from ctac.smt.encoding.map_chain import (
    KV,
    MapChain,
    NamedMap,
    OpaqueRef,
    chain_opaque_self,
)
from ctac.smt.encoding.map_chain import store as chain_store
from ctac.smt.encoding.map_chain import reachable_named_targets
from ctac.smt.encoding.path_skeleton import (
    block_by_id,
    block_guard,
    blk_var_name,
    sanitize_ident,
)
from ctac.smt.model import SmtDeclaration, SmtScript
from ctac.smt.util import and_terms, implies, or_terms
from ctac.ast.bit_mask import (
    high_mask_clear_low_k as _is_high_mask_clear_low_k,
    low_mask_width as _is_low_mask,
    shifted_contiguous_mask,
)
from ctac.ast.range_constraints import match_inclusive_range_constraint

_SYMBOL_LINE = re.compile(
    r"^\s*([A-Za-z_][A-Za-z0-9_]*):([A-Za-z0-9_]+)(?::\d+)?\s*$"
)
_BASE_SYMBOL = re.compile(r"^(.*):\d+$")
_TYPED_CONST = re.compile(
    r"^(?P<num>(?:-?[0-9]+|0[xX]-?[0-9a-fA-F_]+))\((?P<tag>[A-Za-z0-9_]+)\)$"
)
_SAFE_MATH_NARROW_BIF = re.compile(r"^safe_math_narrow_bv(?P<w>\d+):bif$")
_IDENT_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")

_BV256_MOD = 1 << 256
_BV256_MAX = _BV256_MOD - 1
_BLANK_LINE_MARKER = "__CTAC_BLANK_LINE__"

_INLINE_LINEAR_OPS = frozenset({"Add", "Sub", "IntAdd", "IntSub"})
_INLINE_LINEAR_SCALE_OPS = frozenset({"Mul", "IntMul"})


def _peel_narrow(expr: TacExpr) -> TacExpr:
    """Peel ``safe_math_narrow_bvN`` wrappers — the encoder treats
    them as identity, so for inlining-shape purposes
    ``narrow(IntAdd(k, R))`` is structurally just ``IntAdd(k, R)``."""
    while (
        isinstance(expr, ApplyExpr)
        and expr.op == "Apply"
        and len(expr.args) >= 2
        and isinstance(expr.args[0], SymbolRef)
        and _SAFE_MATH_NARROW_BIF.fullmatch(expr.args[0].name)
    ):
        expr = expr.args[1]
    return expr


def _is_inlinable_rhs(expr: TacExpr) -> bool:
    """Conservative shape filter for ``--inline-scalars``: accepts
    constants, aliases, and one-level binary linear arithmetic with a
    constant operand."""
    expr = _peel_narrow(expr)
    if isinstance(expr, (ConstExpr, SymbolRef)):
        return True
    if isinstance(expr, ApplyExpr) and len(expr.args) == 2:
        if expr.op in _INLINE_LINEAR_OPS or expr.op in _INLINE_LINEAR_SCALE_OPS:
            has_const = any(isinstance(a, ConstExpr) for a in expr.args)
            all_simple = all(
                isinstance(a, (ConstExpr, SymbolRef)) for a in expr.args
            )
            return has_const and all_simple
    return False


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
        # TAC dumps emit negative hex as ``0x-N`` (sign right after
        # the radix prefix). Python's ``int(_, 16)`` doesn't accept
        # that shape; strip and re-prefix.
        body = t[2:]
        if body.startswith("-"):
            return -int(body[1:], 16)
        return int(body, 16)
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


def _render_expr_short(expr: TacExpr, max_len: int = 160) -> str:
    """One-line, human-readable rendering of a TacExpr for error messages.

    Mirrors the ``Op(arg, arg)`` shape of the dump rather than calling into
    ``ctac.ast.pretty`` (keeps the encoder free of printer dependencies and
    avoids recursive failures during error formatting). Truncated to
    ``max_len`` so deeply-nested RHSes don't drown the diagnostic."""
    if isinstance(expr, SymbolRef):
        s = expr.name
    elif isinstance(expr, ConstExpr):
        s = expr.value
    elif isinstance(expr, ApplyExpr):
        args = ", ".join(_render_expr_short(a, max_len) for a in expr.args)
        s = f"{expr.op}({args})"
    else:
        s = repr(expr)
    if len(s) > max_len:
        s = s[: max_len - 3] + "..."
    return s


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
            return or_terms([cond, else_term])
        if else_term == "false":
            return and_terms([cond, then_term])
        if then_term == "false":
            return and_terms([f"(not {cond})", else_term])
        if else_term == "true":
            return or_terms([f"(not {cond})", then_term])
    return f"(ite {cond} {then_term} {else_term})"


def _xor_axiom_define_fun() -> str:
    return (
        "(define-fun bv256_xor_axiom ((x Int) (y Int)) Bool "
        "(=> (and (<= 0 x 1) (<= 0 y 1)) "
        "(= (bv256_xor x y) (ite (= x y) 0 1))))"
    )


def _int_ceil_div_axiom_define_fun() -> str:
    # Partial axiom for ceiling division of integers: defined when the
    # divisor is positive. Outside ``b > 0`` the function is left totally
    # free (z3 can pick any value) — same totalization style as
    # bv256_xor's "outside {0,1}^2 it's free".
    return (
        "(define-fun int_ceil_div_axiom ((a Int) (b Int)) Bool "
        "(=> (> b 0) "
        "(and (>= (* b (int_ceil_div a b)) a) "
        "(< (* b (int_ceil_div a b)) (+ a b)))))"
    )


def _int_mul_div_axiom_define_fun() -> str:
    # Total axiom for ``int_mul_div``. Two branches by divisor sign:
    #
    # * c > 0:  Euclidean bounds. No ``(* a b)`` mention — pure NIA on
    #   ``(* c IMD)``, which keeps the formula linear in the most
    #   common case (positive divisor) and avoids handing z3 the
    #   nonlinear product directly.
    # * c <= 0: tie ``int_mul_div`` to z3's built-in ``div`` over
    #   ``(* a b)``. Costs a nonlinear-mul mention but is needed for
    #   soundness — without it, ``int_mul_div`` is a free UF at
    #   c <= 0, distinct from z3's ``div``-at-c<=0 (also free, but a
    #   different free function), and the rewrite
    #   ``IntDiv(IntMul(a, b), c) -> IntMulDiv(a, b, c)`` is
    #   unsound. z3 confirms: with only the c > 0 branch, the
    #   inequality ``(int_mul_div a b c) != (div (* a b) c)`` is sat
    #   at c = -1; adding the c <= 0 branch makes it unsat for all c.
    #
    # In practice the c <= 0 branch is dormant for SBF programs that
    # assert their divisors positive — z3 propagates ``c > 0``,
    # selects the bounds branch, and the ``(* a b)`` term in the
    # c <= 0 branch never materializes. The rewrite stays cheap
    # where it matters and stays sound everywhere else.
    return (
        "(define-fun int_mul_div_axiom ((a Int) (b Int) (c Int)) Bool "
        "(and "
        "(=> (> c 0) "
        "(and (<= (* c (int_mul_div a b c)) (* a b)) "
        "(< (* a b) (+ (* c (int_mul_div a b c)) c)))) "
        "(=> (<= c 0) "
        "(= (int_mul_div a b c) (div (* a b) c)))))"
    )


_UF_AXIOM_DEFINE_BY_UF: dict[str, tuple[str, Callable[[], str]]] = {
    "bv256_xor": ("bv256_xor_axiom", _xor_axiom_define_fun),
    "int_ceil_div": ("int_ceil_div_axiom", _int_ceil_div_axiom_define_fun),
    "int_mul_div": ("int_mul_div_axiom", _int_mul_div_axiom_define_fun),
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
        # Populated below (post `maps_with_store_def`) when
        # ``--inline-scalars`` is set. Lookup-only inside ``emit_expr``,
        # so an empty dict is the no-op.
        inline_subs: dict[str, str] = {}
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

        # ``ReachabilityCertora<block-id>`` symbols are the production
        # pipeline's name for per-block reachability predicates — same
        # concept as our ``BLK_<id>``. The TAC ships them as free
        # havoc'd Bools (production adds the equality axioms during
        # lowering, which our pipeline doesn't reproduce). We alias
        # them to the matching ``BLK_<id>`` via ``define-fun`` so z3
        # substitutes inline. No constraints, no equality assertion,
        # no extra solver work. Static analysis won't see the
        # semantics through this alias — the constraints are missing
        # — but it matches what production does today.
        block_id_set = {b.id for b in program.blocks}
        reach_alias: dict[str, str] = {}
        encoder_warnings: list[str] = []
        for s in ordered_symbols:
            if not s.startswith("ReachabilityCertora"):
                continue
            block_id = s[len("ReachabilityCertora"):]
            if block_id in block_id_set:
                reach_alias[s] = block_guard(block_id, entry_block_id=entry_block_id)
        if reach_alias:
            encoder_warnings.append(
                f"aliased {len(reach_alias)} ReachabilityCertora* "
                "symbol(s) to BLK_* via define-fun "
                "(production-pipeline compatibility — TAC ships these "
                "as unconstrained Bools)"
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
            elif s in reach_alias:
                # Alias is emitted as a ``define-fun`` later in a
                # banner-marked block. Skip the ``declare-const`` here.
                continue
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

        # uf_apps: per-UF, a map from (encoded args tuple) to the set
        # of block ids whose top-level emit_expr produced that
        # application. Block ids power --guard-axioms; without it only
        # the keys are consumed.
        uf_apps: dict[str, dict[tuple[str, ...], set[str]]] = defaultdict(dict)
        # leaf_apps: bytemap leaf-UF range-axiom keys. Always emitted
        # unguarded (they're generic and cheap), so no per-block
        # attribution is needed.
        leaf_apps: set[tuple[str, str]] = set()
        leaf_visited: set[tuple[str, str]] = set()
        # Set of canonical bytemap symbol names referenced by some
        # ``Select`` term. Always populated; consumed only when
        # ``ctx.store_reduce`` is on (dead-map elision).
        live_map_names: set[str] = set()
        # Per-map chain data structures (built only under store_reduce).
        # See `src/ctac/smt/encoding/map_chain.py`.
        map_chains: dict[str, MapChain] = {}
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

        def _symbol_is_bv256(sym: str) -> bool:
            base = _BASE_SYMBOL.sub(r"\1", sym)
            raw = (raw_sorts.get(sym) or raw_sorts.get(base) or "").lower()
            return raw == "bv256"

        def add_havoc_range_if_bv256(
            sym: str,
            term: str,
            *,
            block_id: str | None = None,
            cmd_index: int | None = None,
        ) -> None:
            if not _symbol_is_bv256(sym):
                return
            if block_id is not None and cmd_index is not None and (block_id, cmd_index) in havoc_refine_bounds:
                # Refined sites merge any remaining domain side into the
                # immediately following assume instead of standalone asserts.
                return
            add_constraint(f"(<= 0 {term} BV256_MAX)")

        def _rhs_is_top_level_narrow(rhs: TacExpr) -> bool:
            """True when ``rhs`` is ``Apply(safe_math_narrow_bvN:bif, ...)``.

            This is the canonical "checked narrow" pattern. The current
            encoder treats the narrow as identity on the inner expression
            (so the LHS inherits the inner's unbounded ``Int``); with
            ``--narrow-range`` we recover the LHS's bv-domain via an
            explicit range axiom.
            """
            if not isinstance(rhs, ApplyExpr):
                return False
            if rhs.op != "Apply" or not rhs.args:
                return False
            head = rhs.args[0]
            if not isinstance(head, SymbolRef):
                return False
            return _SAFE_MATH_NARROW_BIF.fullmatch(head.name) is not None

        def add_narrow_range_if_bv256(sym: str, term: str) -> None:
            """Emit the LHS bv256 range axiom for a narrow assignment.

            ``--narrow-range`` opt-in. Symbols whose declared sort is
            not ``bv256`` are silent (a future change can generalize to
            arbitrary bv widths once the rest of the encoder grows
            non-bv256 support)."""
            if not ctx.narrow_range:
                return
            if not _symbol_is_bv256(sym):
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

        # Source-context stack for error diagnostics. Each top-level
        # ``emit_expr`` callsite (per-command rhs/assume/assert/map-body)
        # pushes a string describing where in the program the encoding
        # is happening; ``SmtEncodingError`` raised from within is caught
        # once and re-raised with that chain appended. Without this the
        # only signal a user gets is the operator name with no pointer
        # back to the offending TAC line.
        source_stack: list[str] = []

        @contextmanager
        def _with_source(ctx: str) -> Iterator[None]:
            source_stack.append(ctx)
            try:
                yield
            except SmtEncodingError as e:
                if getattr(e, "_ctac_ctx_added", False):
                    raise
                chain = " -> ".join(source_stack)
                new = SmtEncodingError(f"{e}\n  while encoding {chain}")
                new._ctac_ctx_added = True  # type: ignore[attr-defined]
                raise new from e
            finally:
                source_stack.pop()

        # Block-context stack for axiom-trigger attribution. Each
        # top-level ``emit_expr`` callsite (per-command rhs/assume/
        # assert/map-body) pushes the id of the block that triggered
        # the encoding. ``uf_apps`` / ``leaf_apps`` consult the top of
        # the stack so an axiom instance carries the set of blocks
        # whose terms triggered it; ``--guard-axioms`` then guards the
        # axiom assert by the OR of those block guards.
        block_stack: list[str] = []

        @contextmanager
        def _with_block(block_id: str) -> Iterator[None]:
            block_stack.append(block_id)
            try:
                yield
            finally:
                block_stack.pop()

        def _current_block() -> str | None:
            return block_stack[-1] if block_stack else None

        def _add_uf_app(uf: str, args: tuple[str, ...]) -> None:
            blk = _current_block()
            slot = uf_apps[uf].setdefault(args, set())
            if blk is not None:
                slot.add(blk)

        def emit_expr(expr: TacExpr, *, expected_sort: str | None = None) -> tuple[str, str]:
            def to_bool(term: str, sort: str) -> str:
                if sort == "Bool":
                    return term
                # TAC conditions are sometimes encoded as Int/BV expressions.
                return f"(not (= {term} 0))"

            if isinstance(expr, SymbolRef):
                sym = canonical_symbol(expr.name, strip_var_suffixes=True)
                if sym in inline_subs:
                    # ``--inline-scalars``: the symbol's static def has
                    # been substituted at every use site. The pre-pass
                    # populated ``inline_subs[sym]`` with the SMT form
                    # of the RHS already.
                    return inline_subs[sym], symbol_sort[sym]
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
                        # Twos-complement encode/decode bifs are
                        # represented by ``to_s256`` / ``from_s256``
                        # define-funs in the preamble.
                        if callee == "wrap_twos_complement_256:bif" and len(expr.args) == 2:
                            arg, _ = emit_expr(expr.args[1], expected_sort="Int")
                            return f"(to_s256 {arg})", "Int"
                        if callee == "unwrap_twos_complement_256:bif" and len(expr.args) == 2:
                            arg, _ = emit_expr(expr.args[1], expected_sort="Int")
                            return f"(from_s256 {arg})", "Int"
                        uf = f"uf_{sanitize_ident(callee)}"
                        args = [emit_expr(a, expected_sort="Int")[0] for a in expr.args[1:]]
                        ret_sort = expected_sort or "Int"
                        smt_sort = "Bool" if ret_sort == "Bool" else "Int"
                        dom = " ".join("Int" for _ in args)
                        uf_decl_lines.add(f"(declare-fun {uf} ({dom}) {smt_sort})")
                        _add_uf_app(uf, tuple(args))
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
                    return (and_terms(terms) if smt == "and" else or_terms(terms)), "Bool"
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
                if op in {"Add", "Sub"}:
                    # bv256-wrap arithmetic. Single-wrap ITE form (default,
                    # ``bv_add_sub_axiom == "no-mod"``) is sound because both
                    # operands are in [0, BV256_MAX], so Add wraps at most
                    # once upward and Sub at most once downward; both arms
                    # of the ITE are linear in the operands, exposing the
                    # arithmetic to LRA / solve-eqs / ctx-simplify. The
                    # ``"mod"`` legacy form keeps the prior opaque modulus
                    # wrapping for byte-identical comparison runs.
                    a1, _ = emit_expr(expr.args[0], expected_sort="Int")
                    a2, _ = emit_expr(expr.args[1], expected_sort="Int")
                    smt = "+" if op == "Add" else "-"
                    raw = f"({smt} {a1} {a2})"
                    if ctx.bv_add_sub_axiom == "mod":
                        return f"(mod {raw} BV256_MOD)", "Int"
                    if op == "Add":
                        # No-overflow side OR single wrap upward.
                        return (
                            f"(ite (<= {raw} BV256_MAX) {raw} (- {raw} BV256_MOD))",
                            "Int",
                        )
                    # Sub: 2's-complement-consistent. (- a b) ∈ [-BV256_MAX,
                    # BV256_MAX]; negative case is ``+ BV256_MOD`` so e.g.
                    # ``a - b == -1`` resolves to ``BV256_MAX``.
                    return (
                        f"(ite (>= {raw} 0) {raw} (+ {raw} BV256_MOD))",
                        "Int",
                    )
                if op == "Mul":
                    # bv256-wrap multiplication can produce many wraps;
                    # the single-wrap-ITE shape is unsound here. Stays on
                    # the opaque modulus form unconditionally (a future
                    # multi-variant axiomatization for Mul would slot in
                    # the same way Add/Sub now do).
                    a1, _ = emit_expr(expr.args[0], expected_sort="Int")
                    a2, _ = emit_expr(expr.args[1], expected_sort="Int")
                    return f"(mod (* {a1} {a2}) BV256_MOD)", "Int"
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
                if op == "IntCeilDiv":
                    # Ceiling division — total UF axiomatized partially
                    # for ``b > 0`` via ``int_ceil_div_axiom``. Per-app
                    # axiom instantiation happens at finalize time.
                    if len(expr.args) != 2:
                        raise SmtEncodingError("IntCeilDiv expects two args")
                    a1, _ = emit_expr(expr.args[0], expected_sort="Int")
                    a2, _ = emit_expr(expr.args[1], expected_sort="Int")
                    uf = "int_ceil_div"
                    uf_decl_lines.add(f"(declare-fun {uf} (Int Int) Int)")
                    _add_uf_app(uf, (a1, a2))
                    return f"({uf} {a1} {a2})", "Int"
                if op == "IntMulDiv":
                    # Floor multiply-then-divide: floor((a*b)/c). Total UF
                    # axiomatized partially for ``c > 0`` via
                    # ``int_mul_div_axiom``. Per-app axiom instantiation
                    # happens at finalize time.
                    if len(expr.args) != 3:
                        raise SmtEncodingError("IntMulDiv expects three args")
                    a1, _ = emit_expr(expr.args[0], expected_sort="Int")
                    a2, _ = emit_expr(expr.args[1], expected_sort="Int")
                    a3, _ = emit_expr(expr.args[2], expected_sort="Int")
                    uf = "int_mul_div"
                    uf_decl_lines.add(f"(declare-fun {uf} (Int Int Int) Int)")
                    _add_uf_app(uf, (a1, a2, a3))
                    return f"({uf} {a1} {a2} {a3})", "Int"
                if op in {"Shl", "BvShl", "BVShl", "LShift", "ShiftLeft"}:
                    if len(expr.args) != 2:
                        raise SmtEncodingError(f"{op} expects two args")
                    x, _ = emit_expr(expr.args[0], expected_sort="Int")
                    if not isinstance(expr.args[1], ConstExpr):
                        uf = "bv256_shl"
                        y, _ = emit_expr(expr.args[1], expected_sort="Int")
                        uf_decl_lines.add(f"(declare-fun {uf} (Int Int) Int)")
                        _add_uf_app(uf, (x, y))
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
                        _add_uf_app(uf, (x, y))
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
                    _add_uf_app(uf, (x_t, y_t))
                    return f"({uf} {x_t} {y_t})", "Int"
                if op in {"BXor", "BitXor", "BvXor", "BVXor", "Xor", "BWXor", "BWXOr", "BWXOR"}:
                    a1, _ = emit_expr(expr.args[0], expected_sort="Int")
                    a2, _ = emit_expr(expr.args[1], expected_sort="Int")
                    uf = "bv256_xor"
                    uf_decl_lines.add(f"(declare-fun {uf} (Int Int) Int)")
                    _add_uf_app(uf, (a1, a2))
                    return f"({uf} {a1} {a2})", "Int"
                if op in {"BOr", "BitOr", "BvOr", "BVOr", "BWOr", "BWOR"}:
                    a1, _ = emit_expr(expr.args[0], expected_sort="Int")
                    a2, _ = emit_expr(expr.args[1], expected_sort="Int")
                    uf = "bv256_or"
                    uf_decl_lines.add(f"(declare-fun {uf} (Int Int) Int)")
                    _add_uf_app(uf, (a1, a2))
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
                    # Bytemap cells are bv256-valued in TAC, but the SMT
                    # UF has sort ``Int -> Int`` with no domain
                    # constraint — z3 is free to pick negative or
                    # >BV256_MAX values that satisfy the Int-level VC
                    # but can't replay through a bv256 register. The
                    # axiom is only load-bearing on the leaf UF maps at
                    # the bottom of M's chain (stored values carry
                    # their own scalar bv256 bound), so push the walk
                    # down to leaves rather than axiomatizing
                    # ``(M idx)`` directly.
                    _collect_leaves(mem, idx_term)
                    # Track which map symbols are queried by some Select
                    # — the seed set for `--store-reduce` dead-map
                    # elision. Always populated so the closure logic
                    # below has a consistent signal regardless of the
                    # flag.
                    live_map_names.add(mem_name)
                    return f"({symbol_term[mem_name]} {idx_term})", "Int"

                raise SmtEncodingError(
                    f"unsupported operator in sea_vc: {op} in {_render_expr_short(expr)}"
                )
            raise SmtEncodingError(
                f"unsupported expression node: {_render_expr_short(expr)}"
            )

        # ──────────────────────────────────────────────────────────
        # Bytemap definitions (lambda-style ``define-fun`` per map).
        #
        # A memory symbol with at least one ``Store`` def is encoded
        # as a function definition rather than an uninterpreted
        # function declaration. The body for ``M = Store(M_old, k, v)``
        # is ``(ite (= i k) v (M_old i))`` where ``i`` is the
        # parameter; nested Stores fold into nested ITEs in one body.
        # DSA-dynamic maps (multiple Store-defs across blocks) emit
        # per-block bodies plus a merged define-fun selecting on
        # block guards — same shape sea_vc uses for non-map dynamic
        # vars, lifted from value to function level. Block exclusivity
        # makes the last branch the implicit default.
        # ──────────────────────────────────────────────────────────

        _MAP_PARAM = "idx"

        def _per_block_havoc_name(map_term: str, block_id: str) -> str:
            """Internal name for the per-block havoc body of a DSA-dynamic
            map. Both the map-section emit and the leaf-axiom collector
            use this helper so the names cannot drift."""
            return f"{map_term}_at_{sanitize_ident(block_id)}"

        def _is_map_branch(expr: TacExpr) -> bool:
            """Sub-expression usable as a branch in a map ``define-fun``
            body: a SymbolRef to a map symbol, a Store-tree, or a
            nested Ite of map-branches."""
            if isinstance(expr, SymbolRef):
                return canonical_symbol(expr.name, strip_var_suffixes=True) in memory_symbols
            if isinstance(expr, ApplyExpr):
                if expr.op == "Store" and len(expr.args) == 3:
                    return _is_map_branch(expr.args[0])
                if expr.op == "Ite" and len(expr.args) == 3:
                    return _is_map_branch(expr.args[1]) and _is_map_branch(expr.args[2])
            return False

        def _expr_is_map_define_shape(expr: TacExpr) -> bool:
            """RHS shapes that we lower to a map ``define-fun`` body:
            Store-trees, and value-level Ite on map-branches (TAC's
            SSA merge of bytemaps). Bare SymbolRef aliases are not
            map-defines."""
            if isinstance(expr, ApplyExpr):
                if expr.op == "Store":
                    return True
                if expr.op == "Ite" and len(expr.args) == 3:
                    return _is_map_branch(expr.args[1]) and _is_map_branch(expr.args[2])
            return False

        # Memory symbols handled via the map section (function-level
        # ``define-fun``): either at least one Store-def, or multiple
        # defs of any kind (DSA-dynamic havocs that merge at a join
        # need the same per-block-then-merged shape). Skipped in the
        # static / dynamic constraint loops below; their per-symbol
        # ``declare-fun`` is dropped from uf_decl_lines.
        maps_with_store_def: set[str] = set()
        for mem_sym in memory_symbols:
            defs = du.definitions_by_symbol.get(mem_sym, ())
            if len(defs) > 1:
                maps_with_store_def.add(mem_sym)
                continue
            for ds in defs:
                cmd = block_by_id(program, ds.block_id).commands[ds.cmd_index]
                if isinstance(cmd, AssignExpCmd) and _expr_is_map_define_shape(cmd.rhs):
                    maps_with_store_def.add(mem_sym)
                    break
        for mem_sym in maps_with_store_def:
            uf_decl_lines.discard(
                f"(declare-fun {symbol_term[mem_sym]} (Int) Int)"
            )

        # Inline-scalars pre-pass. Populates ``inline_subs`` (already
        # in scope, consulted by ``emit_expr``) for static
        # ``AssignExpCmd`` defs whose RHS matches the conservative
        # linear-shape filter. Iterating in DSA order means alias
        # chains collapse transitively (later defs see earlier ones
        # already in ``inline_subs`` via the SymbolRef branch).
        if ctx.inline_scalars:
            # Symbols referenced by name (not as TacExpr) cannot be
            # inlined safely: their declarations need to stay live
            # because the reference site bypasses ``emit_expr``. Today
            # this is just JumpiCmd conditions, which are name strings
            # consumed by the CFG section.
            jumpi_cond_syms: set[str] = set()
            for blk in program.blocks:
                for cmd in blk.commands:
                    if isinstance(cmd, JumpiCmd):
                        jumpi_cond_syms.add(
                            canonical_symbol(cmd.condition, strip_var_suffixes=True)
                        )
            for ds in du.definitions:
                if ds.symbol in dynamic_symbols:
                    continue
                if ds.symbol in maps_with_store_def:
                    continue
                if ds.symbol in memory_symbols:
                    # Memory symbols are functions, not inlinable scalars.
                    continue
                if ds.symbol in jumpi_cond_syms:
                    # The CFG section references the symbol by name;
                    # inlining would leave dangling text.
                    continue
                b = block_by_id(program, ds.block_id)
                cmd = b.commands[ds.cmd_index]
                if not isinstance(cmd, AssignExpCmd):
                    continue
                if not _is_inlinable_rhs(cmd.rhs):
                    continue
                with _with_source(
                    f"inline rhs of {ds.symbol} in block {ds.block_id} "
                    f"cmd {ds.cmd_index}"
                ), _with_block(ds.block_id):
                    rhs_smt, _ = emit_expr(
                        cmd.rhs, expected_sort=symbol_sort[ds.symbol]
                    )
                inline_subs[ds.symbol] = rhs_smt

        # ──────────────────────────────────────────────────────────
        # Per-bytemap chain construction (only under --store-reduce).
        # See `src/ctac/smt/encoding/map_chain.py` for the data
        # structure. Built in source order so each ``M_new = Store(M_old,
        # k, v)`` finds ``MapChain[M_old]`` already populated. Maps
        # whose RHS shape we don't recognize (Ite-anchored, compound
        # m_old, multi-def DSA-dynamic, havoc-leaf) get the
        # self-referential opaque chain ``[OpaqueRef(M)]``; their
        # bodies are emitted by the existing logic.
        # ──────────────────────────────────────────────────────────
        if ctx.store_reduce:
            # Default every memory symbol to opaque-self so that
            # NamedMap/OpaqueRef lookups always find an entry.
            for mem_sym in memory_symbols:
                map_chains[mem_sym] = chain_opaque_self(mem_sym)
            for b in program.blocks:
                for cmd in b.commands:
                    if not isinstance(cmd, AssignExpCmd):
                        continue
                    sym = canonical_symbol(cmd.lhs, strip_var_suffixes=True)
                    if sym not in memory_symbols:
                        continue
                    if sym in dynamic_symbols:
                        # Multi-def map: existing per-block + merged
                        # emission. Stays opaque.
                        continue
                    rhs = cmd.rhs
                    if (
                        isinstance(rhs, ApplyExpr)
                        and rhs.op == "Store"
                        and len(rhs.args) == 3
                        and isinstance(rhs.args[0], SymbolRef)
                    ):
                        m_old_name = canonical_symbol(
                            rhs.args[0].name, strip_var_suffixes=True
                        )
                        old_chain = map_chains.get(m_old_name) or chain_opaque_self(
                            m_old_name
                        )
                        map_chains[sym] = chain_store(
                            old_chain,
                            rhs.args[1],
                            rhs.args[2],
                            owner=m_old_name,
                            registry=map_chains,
                        )
                    # Ite-anchored / compound m_old: leave opaque.

        def _emit_map_body(expr: TacExpr) -> str:
            """Build the body of a map ``define-fun``.

            * SymbolRef → ``(M_old idx)`` function application.
            * Store(M_old, k, v) → ``(ite (= idx k) v <body_for_M_old>)``.
            * Ite(c, M_t, M_f) on map-typed branches (TAC SSA merge
              of bytemaps) → ``(ite <c> (M_t idx) (M_f idx))``. We
              lift the equality into application-level form to keep
              the result inside QF_UFNIA — a value-level
              ``(= M_lhs (ite c M_t M_f))`` would force z3 into
              array-extensional reasoning (incomplete)."""
            if isinstance(expr, SymbolRef):
                m_name = canonical_symbol(expr.name, strip_var_suffixes=True)
                if m_name not in symbol_term:
                    raise SmtEncodingError(
                        f"map body references unknown symbol: {m_name!r}"
                    )
                return f"({symbol_term[m_name]} {_MAP_PARAM})"
            if isinstance(expr, ApplyExpr) and expr.op == "Store" and len(expr.args) == 3:
                m_old, k, v = expr.args
                k_term, _ = emit_expr(k, expected_sort="Int")
                v_term, _ = emit_expr(v, expected_sort="Int")
                old_body = _emit_map_body(m_old)
                return f"(ite (= {_MAP_PARAM} {k_term}) {v_term} {old_body})"
            if isinstance(expr, ApplyExpr) and expr.op == "Ite" and len(expr.args) == 3:
                cond, t_arg, f_arg = expr.args
                cond_term, cond_sort = emit_expr(cond, expected_sort="Bool")
                if cond_sort != "Bool":
                    cond_term = f"(not (= {cond_term} 0))"
                t_body = _emit_map_body(t_arg)
                f_body = _emit_map_body(f_arg)
                return f"(ite {cond_term} {t_body} {f_body})"
            raise SmtEncodingError(
                f"map body has unsupported shape: {expr!r}"
            )

        def _collect_leaves(map_expr: TacExpr, idx_term: str) -> None:
            """Walk down to leaf UF maps and record per-application
            range-axiom keys.

            The bv256-range axiom on `(M idx)` is only load-bearing on
            the *leaf* uninterpreted maps at the bottom of M's
            Store/Ite chain. Stored values are bv256-bounded by their
            own scalar def-site axioms, so we skip them. When the
            store key matches the access index syntactically, the
            access is known to hit the stored value — no descent into
            ``m_old`` is needed for that path.

            ``leaf_visited`` is shared across all calls in this encode
            session and keyed on ``(map_symbol_name, idx_term)`` to
            avoid re-walking deep chains across multiple Selects with
            the same index."""
            if isinstance(map_expr, SymbolRef):
                m_name = canonical_symbol(map_expr.name, strip_var_suffixes=True)
                cache_key = (m_name, idx_term)
                if cache_key in leaf_visited:
                    return
                leaf_visited.add(cache_key)
                if m_name not in maps_with_store_def:
                    leaf_apps.add((symbol_term[m_name], idx_term))
                    return
                for ds in du.definitions_by_symbol.get(m_name, ()):
                    cmd = block_by_id(program, ds.block_id).commands[ds.cmd_index]
                    if isinstance(cmd, AssignHavocCmd):
                        block_nm = _per_block_havoc_name(symbol_term[m_name], ds.block_id)
                        leaf_apps.add((block_nm, idx_term))
                    elif isinstance(cmd, AssignExpCmd):
                        _collect_leaves(cmd.rhs, idx_term)
                return
            if isinstance(map_expr, ApplyExpr):
                if map_expr.op == "Store" and len(map_expr.args) == 3:
                    m_old, k, _v = map_expr.args
                    k_term, _ = emit_expr(k, expected_sort="Int")
                    if k_term == idx_term:
                        # Known hit: the stored value covers this
                        # access; its own scalar bv256 bound suffices.
                        return
                    _collect_leaves(m_old, idx_term)
                    return
                if map_expr.op == "Ite" and len(map_expr.args) == 3:
                    _c, t_arg, f_arg = map_expr.args
                    _collect_leaves(t_arg, idx_term)
                    _collect_leaves(f_arg, idx_term)
                    return
            raise SmtEncodingError(
                f"leaf-axiom walk: unsupported map shape "
                f"{_render_expr_short(map_expr)}"
            )

        # ──────────────────────────────────────────────────────────
        # Live-map closure for `--store-reduce`. Seed:
        # every map referenced by some `Select(M, _)` in the program.
        # Closure: walk each live map's chain (NamedMap / OpaqueRef
        # entries -> add target) plus AST-level references for
        # opaque-anchored maps (Ite-of-bytemap arms; Store-RHS m_old
        # for compound shapes). When the flag is off, `live_map_names`
        # is populated identically (it's a cheap side effect) but
        # never consulted.
        # ──────────────────────────────────────────────────────────

        def _seed_live_from_selects(expr: TacExpr) -> None:
            if isinstance(expr, ApplyExpr):
                op_name = expr.op
                args = expr.args
                if op_name == "Apply" and args and isinstance(args[0], SymbolRef):
                    op_name = args[0].name
                    args = args[1:]
                if op_name == "Select" and len(args) == 2 and isinstance(args[0], SymbolRef):
                    name = canonical_symbol(args[0].name, strip_var_suffixes=True)
                    if name in memory_symbols:
                        live_map_names.add(name)
                for a in expr.args:
                    _seed_live_from_selects(a)

        for b in program.blocks:
            for cmd in b.commands:
                if isinstance(cmd, AssignExpCmd):
                    _seed_live_from_selects(cmd.rhs)
                elif isinstance(cmd, AssumeExpCmd):
                    _seed_live_from_selects(cmd.condition)
                elif isinstance(cmd, AssertCmd):
                    _seed_live_from_selects(cmd.predicate)

        if ctx.store_reduce:
            # Closure: chain references + AST-level references for
            # opaque-anchored static maps and DSA-dynamic per-block
            # bodies.
            def _walk_for_map_refs(e: TacExpr, sink: set[str]) -> None:
                if isinstance(e, SymbolRef):
                    n = canonical_symbol(e.name, strip_var_suffixes=True)
                    if n in memory_symbols:
                        sink.add(n)
                elif isinstance(e, ApplyExpr):
                    for a in e.args:
                        _walk_for_map_refs(a, sink)

            def _is_opaque_self_chain(m_name: str) -> bool:
                ch = map_chains.get(m_name)
                if ch is None or len(ch.entries) != 1:
                    return False
                only = ch.entries[0]
                return isinstance(only, OpaqueRef) and only.name == m_name

            worklist = list(live_map_names)
            while worklist:
                m = worklist.pop()
                # 1. Chain-level references.
                chain = map_chains.get(m)
                if chain is not None:
                    for tgt in reachable_named_targets(chain):
                        if tgt not in live_map_names:
                            live_map_names.add(tgt)
                            worklist.append(tgt)
                # 2. AST-level references — but ONLY for opaque-anchored
                #    maps (Ite-anchored statics, compound m_old, or
                #    DSA-dynamic multi-defs). Store-anchored static maps
                #    with a real chain already capture m_old via NamedMap;
                #    walking the AST there would resurrect dead
                #    intermediates that the chain has already inlined past.
                if _is_opaque_self_chain(m) or m in dynamic_symbols:
                    for ds in du.definitions_by_symbol.get(m, ()):
                        cmd = block_by_id(program, ds.block_id).commands[ds.cmd_index]
                        if isinstance(cmd, AssignExpCmd):
                            sink: set[str] = set()
                            _walk_for_map_refs(cmd.rhs, sink)
                            for n in sink:
                                if n not in live_map_names:
                                    live_map_names.add(n)
                                    worklist.append(n)

        # Walk all program defs in order; emit map definitions
        # alongside their natural program position (so cross-map
        # references — the body of M_n that uses M_{n-1} — see
        # M_{n-1} already defined). For dynamic maps, emit the
        # merged ``define-fun`` after the last per-block body.
        map_section_lines: list[str] = []
        per_block_rows: dict[str, list[tuple[str, str]]] = defaultdict(list)
        per_block_remaining: dict[str, int] = {
            sym: len(du.definitions_by_symbol.get(sym, ()))
            for sym in maps_with_store_def
            if sym in dynamic_symbols
        }
        def _chain_has_kvs(chain: MapChain) -> bool:
            """A chain produced by `chain_store(...)` always has at
            least one KV; opaque-self chains have none. Used to decide
            whether to use chain-based emit or fall back to the AST-
            walk-based ``_emit_map_body``."""
            return any(isinstance(e, KV) for e in chain.entries)

        def _emit_chain_body(chain: MapChain) -> str:
            """Emit a map ``define-fun`` body from a ``MapChain``. The
            terminal entry produces ``(name idx)``; earlier KVs wrap
            it in ``(ite (= idx k) v <below>)``. Sharing falls out of
            the canonical ``[KV(k, v), NamedMap(M_old)]`` shape — that
            chain emits as ``(ite (= idx k) v (M_old idx))``."""
            terminal = chain.entries[-1]
            if isinstance(terminal, (NamedMap, OpaqueRef)):
                if terminal.name not in symbol_term:
                    raise SmtEncodingError(
                        f"map chain terminal references unknown symbol: {terminal.name!r}"
                    )
                body = f"({symbol_term[terminal.name]} {_MAP_PARAM})"
            else:
                raise SmtEncodingError(
                    f"map chain has non-terminal final entry: {terminal!r}"
                )
            for entry in reversed(chain.entries[:-1]):
                if not isinstance(entry, KV):
                    raise SmtEncodingError(
                        f"map chain has non-KV entry before terminal: {entry!r}"
                    )
                k_term, _ = emit_expr(entry.k, expected_sort="Int")
                v_term, _ = emit_expr(entry.v, expected_sort="Int")
                body = f"(ite (= {_MAP_PARAM} {k_term}) {v_term} {body})"
            return body

        for b in program.blocks:
            for ci, cmd in enumerate(b.commands):
                if not isinstance(cmd, (AssignExpCmd, AssignHavocCmd)):
                    continue
                sym = cmd.lhs
                if sym not in maps_with_store_def:
                    continue
                # Dead-map elision under --store-reduce: skip maps
                # not reachable from any Select query (and not
                # transitively referenced by a live map).
                if ctx.store_reduce and sym not in live_map_names:
                    continue
                nm = symbol_term[sym]
                is_dynamic = sym in dynamic_symbols
                cond = block_guard(b.id, entry_block_id=entry_block_id)
                if isinstance(cmd, AssignHavocCmd):
                    # Dynamic-side havoc-def of a map: the per-block
                    # body is a fresh declared UF.
                    block_nm = _per_block_havoc_name(nm, b.id)
                    map_section_lines.append(
                        f"(declare-fun {block_nm} (Int) Int)"
                    )
                    if is_dynamic:
                        per_block_rows[sym].append(
                            (cond, f"({block_nm} {_MAP_PARAM})")
                        )
                else:  # AssignExpCmd
                    with _with_source(
                        f"map-body rhs of {sym} in block {b.id} cmd {ci}"
                    ), _with_block(b.id):
                        # Choose chain-based emit vs the AST-walk-based
                        # emit. Chain-based applies when the chain has
                        # a real KV-bearing structure (Store-anchored
                        # statics under store_reduce). DSA-dynamic and
                        # Ite-anchored / compound-m_old maps fall
                        # through to the existing emission.
                        chain = map_chains.get(sym)
                        if (
                            ctx.store_reduce
                            and not is_dynamic
                            and chain is not None
                            and _chain_has_kvs(chain)
                        ):
                            body = _emit_chain_body(chain)
                        else:
                            body = _emit_map_body(cmd.rhs)
                    if is_dynamic:
                        block_nm = _per_block_havoc_name(nm, b.id)
                        map_section_lines.append(
                            f"(define-fun {block_nm} (({_MAP_PARAM} Int)) Int {body})"
                        )
                        per_block_rows[sym].append(
                            (cond, f"({block_nm} {_MAP_PARAM})")
                        )
                    else:
                        map_section_lines.append(
                            f"(define-fun {nm} (({_MAP_PARAM} Int)) Int {body})"
                        )
                if is_dynamic:
                    per_block_remaining[sym] -= 1
                    if per_block_remaining[sym] == 0:
                        # All per-block bodies for this dynamic map
                        # are emitted; build the merged define-fun
                        # that selects via block guards. Last branch
                        # is the implicit default — block exclusivity
                        # makes the choice deterministic.
                        rows = per_block_rows[sym]
                        merged_body = rows[-1][1]
                        for c2, b2 in reversed(rows[:-1]):
                            merged_body = f"(ite {c2} {b2} {merged_body})"
                        map_section_lines.append(
                            f"(define-fun {nm} (({_MAP_PARAM} Int)) Int {merged_body})"
                        )

        # Static assignment encoding and assume constraints. Under
        # --guard-statics we batch the equalities by defining block and
        # also fold each block's assume conditions into the same
        # conjunction, emitting one
        # ``(=> BLK_b (and eq1 eq2 ... cond1 cond2 ...))`` per block
        # instead of per-equality / per-assume implications: solve-eqs
        # extracts the equalities (including those nested in assumes
        # like ``assume R == 0``) under a single shared guard, which it
        # cannot do across separate implications. Without --guard-statics
        # the default stream-based shape is preserved byte-for-byte:
        # bare ``(= lhs rhs)`` for statics, ``(=> BLK cond)`` per assume.
        grouped_static_eqs: dict[str, list[str]] = {}
        for ds in du.definitions:
            if ds.symbol in dynamic_symbols:
                continue
            if ds.symbol in maps_with_store_def:
                # Maps with Store-defs are handled by the map_section
                # ``define-fun`` (function-level), not value-level
                # equality constraints.
                continue
            b = block_by_id(program, ds.block_id)
            cmd = b.commands[ds.cmd_index]
            if isinstance(cmd, AssignExpCmd):
                if ctx.inline_scalars and ds.symbol in inline_subs:
                    # Equality is unnecessary — every use of ``ds.symbol``
                    # has been substituted by ``inline_subs[ds.symbol]``
                    # via ``emit_expr``. Re-instantiate the narrow-range
                    # axiom on the inlined RHS so the bv256-domain bound
                    # stays in the SMT (now binding the substituted
                    # expression rather than the now-eliminated symbol).
                    if _rhs_is_top_level_narrow(cmd.rhs):
                        add_narrow_range_if_bv256(
                            ds.symbol, inline_subs[ds.symbol]
                        )
                    continue
                lhs = symbol_term[ds.symbol]
                with _with_source(
                    f"static rhs of {ds.symbol} in block {ds.block_id} cmd {ds.cmd_index}"
                ), _with_block(ds.block_id):
                    rhs, _ = emit_expr(cmd.rhs, expected_sort=symbol_sort[ds.symbol])
                eq = f"(= {lhs} {rhs})"
                if ctx.guard_statics:
                    grouped_static_eqs.setdefault(ds.block_id, []).append(eq)
                else:
                    add_constraint(eq)
                if _rhs_is_top_level_narrow(cmd.rhs):
                    add_narrow_range_if_bv256(ds.symbol, lhs)
            elif isinstance(cmd, AssignHavocCmd):
                add_havoc_range_if_bv256(ds.symbol, symbol_term[ds.symbol], block_id=ds.block_id, cmd_index=ds.cmd_index)

        # Default-path: statics already emitted; freeze static_end here
        # so the per-section banners stay byte-identical to today's
        # output. Under --guard-statics the combined emission lands
        # later and we re-freeze static_end after it.
        if not ctx.guard_statics:
            static_end_default = len(constraints)

        # Assume conditions: under --guard-statics, collect into the
        # per-block conjunction; otherwise emit per-cmd as a guarded
        # implication (today's default).
        grouped_assume_conds: dict[str, list[str]] = {}
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

                    with _with_source(
                        f"assume condition in block {block.id} cmd {idx}"
                    ), _with_block(block.id):
                        cond, s = emit_expr(cond_expr, expected_sort="Bool")
                    if s != "Bool":
                        raise SmtEncodingError("Assume condition must be Bool")
                    if ctx.guard_statics:
                        grouped_assume_conds.setdefault(block.id, []).append(cond)
                    else:
                        add_constraint(implies(guard, cond))
            if has_assume_in_block and not ctx.guard_statics:
                remaining_blocks = program.blocks[program.blocks.index(block) + 1 :]
                if any(any(isinstance(c, AssumeExpCmd) for c in b.commands) for b in remaining_blocks):
                    constraints.append(_BLANK_LINE_MARKER)

        if ctx.guard_statics:
            # Combined per-block emission: statics first (in
            # du.definitions order, already deterministic), then assume
            # conds (in command order). Iterate program.blocks for
            # deterministic between-block ordering and blank-line
            # placement.
            blocks_with_emission = [
                b for b in program.blocks
                if b.id in grouped_static_eqs or b.id in grouped_assume_conds
            ]
            for i, block in enumerate(blocks_with_emission):
                eqs = grouped_static_eqs.get(block.id, [])
                conds = grouped_assume_conds.get(block.id, [])
                guard = block_guard(block.id, entry_block_id=entry_block_id)
                add_constraint(implies(guard, and_terms(eqs + conds)))
                if i < len(blocks_with_emission) - 1:
                    constraints.append(_BLANK_LINE_MARKER)
            # All static + assume content lives in the "Static" section.
            # The "Assumptions" section is empty.
            static_end = len(constraints)
            assume_end = static_end
        else:
            static_end = static_end_default
            assume_end = len(constraints)

        # Dynamic assignment groups as compact ITEs.
        dynamic_by_symbol: dict[str, list] = defaultdict(list)
        for d in dsa.dynamic_assignments:
            dynamic_by_symbol[d.symbol].append(d)
        for sym, rows in sorted(dynamic_by_symbol.items()):
            if sym in maps_with_store_def:
                # Maps with Store-defs are handled by map_section's
                # function-level merged ``define-fun``.
                continue
            grouped_conds: dict[str, list[str]] = defaultdict(list)
            rhs_rank: dict[str, int] = {}
            for row in rows:
                b = block_by_id(program, row.block_id)
                cmd = b.commands[row.cmd_index]
                if isinstance(cmd, AssignExpCmd):
                    with _with_source(
                        f"dynamic rhs of {sym} in block {row.block_id} cmd {row.cmd_index}"
                    ), _with_block(row.block_id):
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
                cond = or_terms(conds)
                if cond == "false":
                    continue
                cases.append((cond, rhs))
            cases.sort(key=lambda x: rhs_rank.get(x[1], 10**9))
            if not cases:
                raise SmtEncodingError(f"no dynamic cases found for symbol {sym}")
            sym_term = symbol_term[sym]
            if ctx.guard_dynamics:
                # Per-defining-block guarded equality. AMO over the
                # CFG block guards ensures at most one ``cond`` is
                # true per execution, so at most one equality fires.
                for cond, rhs in cases:
                    add_constraint(implies(cond, f"(= {sym_term} {rhs})"))
            else:
                value = cases[-1][1]
                for cond, rhs in reversed(cases[:-1]):
                    value = _simplify_ite(cond, rhs, value, sort=symbol_sort[sym])
                add_constraint(f"(= {sym_term} {value})")
        dynamic_end = len(constraints)

        # CFG predecessor constraints — dispatched through smt.cfg
        # so the strategy can be swapped from the CLI without
        # reaching into encode().
        cfg_input = build_cfg_input(
            program, entry_block_id=entry_block_id, symbol_term=symbol_term
        )
        cfg_encoder = CFG_ENCODERS.get(ctx.cfg_encoding)
        if cfg_encoder is None:
            raise SmtEncodingError(
                f"unknown cfg_encoding {ctx.cfg_encoding!r}; "
                f"available: {', '.join(sorted(CFG_ENCODERS))}"
            )
        cfg_emit = CfgEmit(
            add_constraint=add_constraint,
            add_decl=lambda name, sort: decls.append(SmtDeclaration(name=name, sort=sort)),
        )
        cfg_encoder(cfg_input, cfg_emit)
        cfg_end = len(constraints)

        # Exit objective bound to assert block and failing assert predicate.
        assert_guard = block_guard(ctx.assert_site.block_id, entry_block_id=entry_block_id)
        with _with_source(
            f"assert predicate in block {ctx.assert_site.block_id} "
            f"cmd {ctx.assert_site.cmd_index}"
        ), _with_block(ctx.assert_site.block_id):
            assert_cond, assert_sort = emit_expr(assert_expr, expected_sort="Bool")
        if assert_sort != "Bool":
            raise SmtEncodingError("Assert predicate must lower to Bool")
        exit_rhs = and_terms([f"(not {assert_cond})", assert_guard])
        add_constraint(implies("BLK_EXIT", exit_rhs))
        add_constraint("BLK_EXIT")
        exit_end = len(constraints)

        # Render definitions + assertions.
        out_lines: list[str] = [
            f"(define-fun BV256_MOD () Int {_BV256_MOD})",
            "(define-fun BV256_MAX () Int (- BV256_MOD 1))",
            "(define-fun BV256_HALF () Int (div BV256_MOD 2))",
            # Twos-complement encode/decode for bv256. Both total + pure;
            # ``to_s256(s) = s mod 2^256`` (Python-style mod, always
            # non-negative); ``from_s256(b) = b`` for the non-negative
            # half, ``b - 2^256`` for the high half (sign-extended).
            "(define-fun to_s256 ((s Int)) Int (mod s BV256_MOD))",
            "(define-fun from_s256 ((b Int)) Int (ite (< b BV256_HALF) b (- b BV256_MOD)))",
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

        if reach_alias:
            emit_banner("ReachabilityCertora -> BLK_ Aliases")
            out_lines.append(
                "; Production pipeline names per-block reachability"
            )
            out_lines.append(
                "; ``ReachabilityCertora<id>`` and adds equality axioms"
            )
            out_lines.append(
                "; during lowering. Our TAC source has the names but not"
            )
            out_lines.append(
                "; the axioms — alias each to the matching BLK_<id> so"
            )
            out_lines.append(
                "; z3 substitutes inline. Soundness-wise this *adds*"
            )
            out_lines.append(
                "; constraints (collapses two equivalent vars into one);"
            )
            out_lines.append(
                "; static analyses see the alias, not the underlying"
            )
            out_lines.append(
                "; CFG semantics, which is the production trade-off."
            )
            for sym in sorted(reach_alias):
                out_lines.append(
                    f"(define-fun {symbol_term[sym]} () Bool {reach_alias[sym]})"
                )

        if map_section_lines:
            emit_banner("Bytemap Definitions (lambda form)")
            # Topologically sort by inter-map references so each
            # ``define-fun`` body sees its dependencies already
            # declared. Block-order emission isn't enough: a TAC SSA
            # merge ``M571 = Ite(c, M569, M627)`` may sit in an
            # earlier block than the defs of M569 / M627.
            decl_re = re.compile(r"^\((?:declare-fun|define-fun) (\S+) ")
            line_by_name: dict[str, str] = {}
            ordered_names: list[str] = []
            for line in map_section_lines:
                m = decl_re.match(line)
                if m is None:
                    raise SmtEncodingError(
                        f"map section line has unexpected shape: {line!r}"
                    )
                name = m.group(1)
                line_by_name[name] = line
                ordered_names.append(name)
            defined_set = set(line_by_name)
            ident_re = re.compile(r"[A-Za-z_][A-Za-z_0-9]*")
            deps: dict[str, set[str]] = {}
            for name, line in line_by_name.items():
                _, _, body_part = line.partition(") Int ")
                refs = set(ident_re.findall(body_part)) & defined_set
                refs.discard(name)
                deps[name] = refs

            sorted_lines: list[str] = []
            temp: set[str] = set()
            perm: set[str] = set()

            def _visit(n: str) -> None:
                if n in perm or n in temp:
                    return
                temp.add(n)
                for d in sorted(deps.get(n, ())):
                    _visit(d)
                temp.remove(n)
                perm.add(n)
                sorted_lines.append(line_by_name[n])

            for n in ordered_names:
                _visit(n)
            out_lines.extend(sorted_lines)

        # Emit UF axiom definitions once, then instantiate per application.
        emitted_axiom_funs: set[str] = set()
        printed_axiom_banner = False
        def _axiom_guard(blocks: set[str]) -> str:
            # Reduce a set of trigger-block ids to a single guard term.
            # Empty (no recorded trigger) falls through unguarded —
            # safer to keep the axiom than drop it.
            if not blocks:
                return "true"
            return or_terms(
                [block_guard(b, entry_block_id=entry_block_id) for b in sorted(blocks)]
            )

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
                instance = f"({axiom_fun_name} {' '.join(args)})"
                if ctx.guard_axioms:
                    instance = implies(_axiom_guard(uf_apps[uf][args]), instance)
                out_lines.append(f"(assert {instance})")

        # Memory cells are bv256-valued. Without a per-application
        # range axiom, z3 can pick negative or >BV256_MAX values that
        # satisfy the Int-level VC but can't be loaded back into a
        # bv256 register, which breaks model replay through
        # ``ctac run``. The axiom is emitted on *leaf* UF maps only
        # (the bottoms of Store/Ite chains): chain tops are define-funs
        # that would expand on application, re-bounding stored values
        # whose scalar bv256 bound already covers them. Stored slots
        # are skipped during the walk for the same reason.
        # Memory bv256-range axioms stay unguarded even under
        # --guard-axioms. They are generic, cheap (a single
        # `(<= 0 (M idx) BV256_MAX)` per leaf application), and
        # always sound to assert; the cost they pay isn't worth a
        # block-reachability gate, and keeping them universally
        # asserted preserves the model-replay invariant `ctac run`
        # relies on regardless of which path z3 picks.
        if leaf_apps:
            if not printed_axiom_banner:
                emit_banner("Axiom Instantiations")
                printed_axiom_banner = True
            out_lines.append("; memory bv256-range axioms (one per leaf-UF application)")
            for mem_name, idx_term in sorted(leaf_apps):
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

        # Filter out declarations for inlined scalars: those symbols
        # have been substituted at every use site, so their
        # ``declare-const`` lines would be orphans.
        if ctx.inline_scalars and inline_subs:
            inlined_decl_names = {symbol_term[s] for s in inline_subs}
            decls = [d for d in decls if d.name not in inlined_decl_names]

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
            warnings=tuple(encoder_warnings),
        )
