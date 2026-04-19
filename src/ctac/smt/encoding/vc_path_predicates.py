from __future__ import annotations

import re
from dataclasses import dataclass

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
from ctac.smt.encoding.base import EncoderContext, SmtEncodingError, SmtEncoder
from ctac.smt.model import SmtDeclaration, SmtScript
from ctac.ast.parse_expr import parse_expr_safe

_BV_SORT = re.compile(r"^\(_\s+BitVec\s+(\d+)\)$")
_SYMBOL_LINE = re.compile(r"^\s*([A-Za-z_][A-Za-z0-9_]*):([A-Za-z0-9_]+)\s*$")
_TYPED_CONST = re.compile(
    r"^(?P<num>(?:-?[0-9]+|0[xX][0-9a-fA-F_]+))\((?P<tag>[A-Za-z0-9_]+)\)$"
)
_BASE_SYMBOL = re.compile(r"^(.*):\d+$")
_SAFE_MATH_NARROW_BIF = re.compile(r"^safe_math_narrow_bv(?P<w>\d+):bif$")


def _ident(*parts: str) -> str:
    raw = "__".join(parts)
    s = re.sub(r"[^A-Za-z0-9_]", "_", raw)
    if not s:
        return "_"
    if s[0].isdigit():
        return "_" + s
    return s


def _sort_from_tag(tag: str) -> str | None:
    t = tag.lower()
    if t == "bool":
        return "Bool"
    if t == "int":
        return "Int"
    if t.startswith("bv") and t[2:].isdigit():
        return f"(_ BitVec {int(t[2:])})"
    return None


def _parse_symbol_sorts(symbol_table_text: str) -> dict[str, str]:
    out: dict[str, str] = {}
    for line in symbol_table_text.splitlines():
        m = _SYMBOL_LINE.match(line)
        if m is None:
            continue
        name, tag = m.group(1), m.group(2)
        sort = _sort_from_tag(tag)
        if sort is not None:
            out[name] = sort
    return out


def _is_bitvec_sort(sort: str) -> bool:
    return _BV_SORT.fullmatch(sort) is not None


def _bitvec_width(sort: str) -> int:
    m = _BV_SORT.fullmatch(sort)
    if m is None:
        raise SmtEncodingError(f"expected bit-vector sort, got {sort}")
    return int(m.group(1))


def _int_from_token(token: str) -> int:
    t = token.replace("_", "").strip()
    if t.startswith(("0x", "0X")):
        return int(t, 16)
    return int(t, 10)


def _parse_const_token(token: str) -> tuple[int, str | None]:
    tok = token.strip()
    m = _TYPED_CONST.fullmatch(tok)
    if m is not None:
        return _int_from_token(m.group("num")), _sort_from_tag(m.group("tag"))
    return _int_from_token(tok), None


def _const_to_bv(token: str, width: int) -> str:
    val, _ = _parse_const_token(token)
    mod = 1 << width
    return f"(_ bv{val % mod} {width})"


def _iter_expr_symbols(expr: TacExpr):
    if isinstance(expr, SymbolRef):
        yield expr.name
        return
    if isinstance(expr, ApplyExpr):
        for arg in expr.args:
            yield from _iter_expr_symbols(arg)


@dataclass
class VCPathPredicatesEncoder(SmtEncoder):
    name: str = "vc-path-predicates"

    def encode(self, ctx: EncoderContext) -> SmtScript:
        program = ctx.tac_file.program
        if not program.blocks:
            raise SmtEncodingError("program has no basic blocks")

        raw_sorts = _parse_symbol_sorts(ctx.tac_file.symbol_table_text)
        symbols, bool_hints = self._collect_symbols(ctx)
        ordered_symbols = tuple(sorted(symbols))

        symbol_sort: dict[str, str] = {}
        for sym in ordered_symbols:
            symbol_sort[sym] = self._resolve_sort(sym, raw_sorts, bool_hints)
            if symbol_sort[sym] == "Int":
                raise SmtEncodingError(
                    "QF_BV encoding does not support Int-typed TAC symbols; "
                    "add/choose an encoding with explicit Int->BV conversion semantics"
                )

        decls: list[SmtDeclaration] = []
        decl_seen: set[str] = set()
        assertions: list[str] = []

        def declare(name: str, sort: str) -> None:
            if name in decl_seen:
                return
            decl_seen.add(name)
            decls.append(SmtDeclaration(name=name, sort=sort))

        block_order = [b.id for b in program.blocks]
        block_by_id = program.block_by_id()
        reach_var = {bid: _ident("reach", bid) for bid in block_order}
        for bid in block_order:
            declare(reach_var[bid], "Bool")

        in_var: dict[str, dict[str, str]] = {}
        out_var: dict[str, dict[str, str]] = {}
        for bid in block_order:
            in_var[bid] = {}
            out_var[bid] = {}
            for sym in ordered_symbols:
                vin = _ident("v", sym, "in", bid)
                vout = _ident("v", sym, "out", bid)
                in_var[bid][sym] = vin
                out_var[bid][sym] = vout
                declare(vin, symbol_sort[sym])
                declare(vout, symbol_sort[sym])

        edge_terms: dict[tuple[str, str], str] = {}
        pred_by_block: dict[str, list[str]] = {bid: [] for bid in block_order}
        end_env_by_block: dict[str, dict[str, str]] = {}
        assert_predicate_term: str | None = None

        for block in program.blocks:
            env = dict(in_var[block.id])
            for idx, cmd in enumerate(block.commands):
                if (
                    block.id == ctx.assert_site.block_id
                    and idx == ctx.assert_site.cmd_index
                    and isinstance(cmd, AssertCmd)
                ):
                    pred_expr = parse_expr_safe(cmd.predicate)
                    pred_term, pred_sort = self._emit_expr(
                        pred_expr, env, symbol_sort=symbol_sort, expected_sort="Bool"
                    )
                    if pred_sort != "Bool":
                        raise SmtEncodingError("AssertCmd predicate must lower to Bool")
                    assert_predicate_term = pred_term
                    continue

                if isinstance(cmd, AssignExpCmd):
                    next_var = _ident("v", cmd.lhs, block.id, str(idx))
                    declare(next_var, symbol_sort[cmd.lhs])
                    rhs_term, rhs_sort = self._emit_expr(
                        cmd.rhs,
                        env,
                        symbol_sort=symbol_sort,
                        expected_sort=symbol_sort[cmd.lhs],
                    )
                    if rhs_sort != symbol_sort[cmd.lhs]:
                        raise SmtEncodingError(
                            f"assignment sort mismatch for {cmd.lhs}: {rhs_sort} != {symbol_sort[cmd.lhs]}"
                        )
                    assertions.append(
                        f"(=> {reach_var[block.id]} (= {next_var} {rhs_term}))"
                    )
                    env[cmd.lhs] = next_var
                    continue

                if isinstance(cmd, AssignHavocCmd):
                    next_var = _ident("v", cmd.lhs, block.id, str(idx))
                    declare(next_var, symbol_sort[cmd.lhs])
                    env[cmd.lhs] = next_var
                    continue

                if isinstance(cmd, AssumeExpCmd):
                    cond_term, cond_sort = self._emit_expr(
                        cmd.condition, env, symbol_sort=symbol_sort, expected_sort="Bool"
                    )
                    if cond_sort != "Bool":
                        raise SmtEncodingError("AssumeExpCmd condition must lower to Bool")
                    assertions.append(f"(=> {reach_var[block.id]} {cond_term})")
                    continue

            end_env_by_block[block.id] = dict(env)
            for sym in ordered_symbols:
                assertions.append(
                    f"(=> {reach_var[block.id]} (= {out_var[block.id][sym]} {env[sym]}))"
                )

        for block in program.blocks:
            for succ in block.successors:
                if succ not in block_by_id:
                    continue
                pred_by_block[succ].append(block.id)
                term = self._edge_term(
                    block_id=block.id,
                    succ_id=succ,
                    reach_var=reach_var,
                    env=end_env_by_block[block.id],
                    block=block,
                    symbol_sort=symbol_sort,
                )
                edge_terms[(block.id, succ)] = term

        entry = block_order[0]
        assertions.append(reach_var[entry])
        for bid in block_order[1:]:
            incoming = [edge_terms[(pred, bid)] for pred in pred_by_block[bid]]
            if not incoming:
                assertions.append(f"(not {reach_var[bid]})")
            elif len(incoming) == 1:
                assertions.append(f"(= {reach_var[bid]} {incoming[0]})")
            else:
                assertions.append(
                    f"(= {reach_var[bid]} (or {' '.join(incoming)}))"
                )
            for pred in pred_by_block[bid]:
                et = edge_terms[(pred, bid)]
                for sym in ordered_symbols:
                    assertions.append(
                        f"(=> {et} (= {in_var[bid][sym]} {out_var[pred][sym]}))"
                    )

        if assert_predicate_term is None:
            raise SmtEncodingError("failed to derive assert predicate term")
        assertions.append(
            f"(and {reach_var[ctx.assert_site.block_id]} (not {assert_predicate_term}))"
        )

        return SmtScript(
            logic="QF_BV",
            declarations=tuple(decls),
            assertions=tuple(f"(assert {a})" for a in assertions),
            comments=(
                "VC is SAT iff some execution reaches AssertCmd with false predicate.",
                f"encoding: {self.name}",
            ),
            check_sat=True,
        )

    def _collect_symbols(self, ctx: EncoderContext) -> tuple[set[str], set[str]]:
        symbols: set[str] = set()
        bool_hints: set[str] = set()
        for block in ctx.tac_file.program.blocks:
            for cmd in block.commands:
                if isinstance(cmd, AssignExpCmd):
                    symbols.add(cmd.lhs)
                    symbols.update(_iter_expr_symbols(cmd.rhs))
                elif isinstance(cmd, AssignHavocCmd):
                    symbols.add(cmd.lhs)
                elif isinstance(cmd, AssumeExpCmd):
                    symbols.update(_iter_expr_symbols(cmd.condition))
                    if isinstance(cmd.condition, SymbolRef):
                        bool_hints.add(cmd.condition.name)
                elif isinstance(cmd, JumpiCmd):
                    symbols.add(cmd.condition)
                    bool_hints.add(cmd.condition)
                elif isinstance(cmd, AssertCmd):
                    pred_expr = parse_expr_safe(cmd.predicate)
                    symbols.update(_iter_expr_symbols(pred_expr))
                    if isinstance(pred_expr, SymbolRef):
                        bool_hints.add(pred_expr.name)
        return symbols, bool_hints

    def _resolve_sort(
        self, symbol: str, raw_sorts: dict[str, str], bool_hints: set[str]
    ) -> str:
        if symbol in raw_sorts:
            return raw_sorts[symbol]
        base = _BASE_SYMBOL.sub(r"\1", symbol)
        if base in raw_sorts:
            return raw_sorts[base]
        if symbol in bool_hints:
            return "Bool"
        return "(_ BitVec 256)"

    def _edge_term(
        self,
        *,
        block_id: str,
        succ_id: str,
        reach_var: dict[str, str],
        env: dict[str, str],
        block,
        symbol_sort: dict[str, str],
    ) -> str:
        if not block.commands or not isinstance(block.commands[-1], JumpiCmd):
            return reach_var[block_id]
        jump = block.commands[-1]
        assert isinstance(jump, JumpiCmd)
        cond_var = env.get(jump.condition)
        if cond_var is None:
            raise SmtEncodingError(f"missing jump condition symbol {jump.condition!r}")
        cond_sort = symbol_sort[jump.condition]
        if cond_sort != "Bool":
            raise SmtEncodingError(f"jump condition {jump.condition!r} must be Bool")
        if succ_id == jump.then_target:
            return f"(and {reach_var[block_id]} {cond_var})"
        if succ_id == jump.else_target:
            return f"(and {reach_var[block_id]} (not {cond_var}))"
        return "false"

    def _emit_expr(
        self,
        expr: TacExpr,
        env: dict[str, str],
        *,
        symbol_sort: dict[str, str],
        expected_sort: str | None = None,
    ) -> tuple[str, str]:
        if isinstance(expr, SymbolRef):
            if expr.name not in env:
                raise SmtEncodingError(f"unknown symbol {expr.name!r}")
            return env[expr.name], symbol_sort[expr.name]

        if isinstance(expr, ConstExpr):
            tok = expr.value.strip()
            if tok in {"true", "false"}:
                return tok, "Bool"
            if expected_sort is not None and _is_bitvec_sort(expected_sort):
                return _const_to_bv(tok, _bitvec_width(expected_sort)), expected_sort
            if tok.startswith(("0x", "0X")):
                return _const_to_bv(tok, 256), "(_ BitVec 256)"
            val, typed_sort = _parse_const_token(tok)
            if typed_sort is not None:
                if _is_bitvec_sort(typed_sort):
                    return _const_to_bv(tok, _bitvec_width(typed_sort)), typed_sort
                if typed_sort == "Int":
                    raise SmtEncodingError(
                        "QF_BV encoding does not support Int constants without explicit conversion"
                    )
                return str(val), typed_sort
            return _const_to_bv(str(val), 256), "(_ BitVec 256)"

        if isinstance(expr, ApplyExpr):
            op = expr.op
            if op == "Apply":
                if len(expr.args) == 2 and isinstance(expr.args[0], SymbolRef):
                    m = _SAFE_MATH_NARROW_BIF.fullmatch(expr.args[0].name)
                    if m is not None:
                        target_w = int(m.group("w"))
                        inner_t, inner_s = self._emit_expr(
                            expr.args[1],
                            env,
                            symbol_sort=symbol_sort,
                        )
                        target_sort = f"(_ BitVec {target_w})"
                        if inner_s == "Int":
                            raise SmtEncodingError(
                                "safe_math_narrow_bv*:bif requires Int->BV conversion, "
                                "unsupported by current QF_BV encoding"
                            )
                        if not _is_bitvec_sort(inner_s):
                            raise SmtEncodingError(
                                f"safe_math_narrow_bv*:bif expects BV input, got {inner_s}"
                            )
                        in_w = _bitvec_width(inner_s)
                        if in_w == target_w:
                            return inner_t, target_sort
                        if in_w > target_w:
                            return f"((_ extract {target_w - 1} 0) {inner_t})", target_sort
                        return f"((_ zero_extend {target_w - in_w}) {inner_t})", target_sort
                raise SmtEncodingError(
                    "unsupported Apply(...) TAC expression for current QF_BV encoding"
                )

            if op in {"Not", "LNot"}:
                arg_t, arg_s = self._emit_expr(
                    expr.args[0], env, symbol_sort=symbol_sort, expected_sort="Bool"
                )
                if arg_s != "Bool":
                    raise SmtEncodingError(f"{op} expects Bool argument")
                return f"(not {arg_t})", "Bool"

            if op in {"LAnd", "LOr"}:
                smt_op = "and" if op == "LAnd" else "or"
                args: list[str] = []
                for arg in expr.args:
                    t, s = self._emit_expr(arg, env, symbol_sort=symbol_sort, expected_sort="Bool")
                    if s != "Bool":
                        raise SmtEncodingError(f"{op} expects Bool arguments")
                    args.append(t)
                if not args:
                    return ("true" if smt_op == "and" else "false"), "Bool"
                if len(args) == 1:
                    return args[0], "Bool"
                return f"({smt_op} {' '.join(args)})", "Bool"

            if op in {"Eq", "Ne", "Neq"}:
                if len(expr.args) != 2:
                    raise SmtEncodingError(f"{op} expects exactly two arguments")
                left_t, left_s = self._emit_expr(expr.args[0], env, symbol_sort=symbol_sort)
                right_t, right_s = self._emit_expr(
                    expr.args[1], env, symbol_sort=symbol_sort, expected_sort=left_s
                )
                if left_s != right_s:
                    left_t, left_s = self._emit_expr(
                        expr.args[0], env, symbol_sort=symbol_sort, expected_sort=right_s
                    )
                if left_s != right_s:
                    raise SmtEncodingError(f"{op} argument sort mismatch: {left_s} vs {right_s}")
                eq = f"(= {left_t} {right_t})"
                if op == "Eq":
                    return eq, "Bool"
                return f"(not {eq})", "Bool"

            if op in {"Lt", "Le", "Gt", "Ge"}:
                if len(expr.args) != 2:
                    raise SmtEncodingError(f"{op} expects exactly two arguments")
                left_t, left_s = self._emit_expr(expr.args[0], env, symbol_sort=symbol_sort)
                right_t, right_s = self._emit_expr(
                    expr.args[1], env, symbol_sort=symbol_sort, expected_sort=left_s
                )
                if left_s != right_s:
                    left_t, left_s = self._emit_expr(
                        expr.args[0], env, symbol_sort=symbol_sort, expected_sort=right_s
                    )
                if left_s != right_s:
                    raise SmtEncodingError(f"{op} argument sort mismatch: {left_s} vs {right_s}")
                if _is_bitvec_sort(left_s):
                    smt = {
                        "Lt": "bvult",
                        "Le": "bvule",
                        "Gt": "bvugt",
                        "Ge": "bvuge",
                    }[op]
                    return f"({smt} {left_t} {right_t})", "Bool"
                if left_s == "Int":
                    raise SmtEncodingError(
                        f"{op} on Int is unsupported in current QF_BV encoding"
                    )
                raise SmtEncodingError(f"{op} unsupported sort {left_s}")

            if op in {"Add", "Sub", "Mul", "Div", "Mod"}:
                if len(expr.args) != 2:
                    raise SmtEncodingError(f"{op} expects exactly two arguments")
                left_t, left_s = self._emit_expr(
                    expr.args[0],
                    env,
                    symbol_sort=symbol_sort,
                    expected_sort=expected_sort,
                )
                right_t, right_s = self._emit_expr(
                    expr.args[1],
                    env,
                    symbol_sort=symbol_sort,
                    expected_sort=left_s,
                )
                if left_s != right_s:
                    raise SmtEncodingError(f"{op} argument sort mismatch: {left_s} vs {right_s}")
                if _is_bitvec_sort(left_s):
                    smt = {
                        "Add": "bvadd",
                        "Sub": "bvsub",
                        "Mul": "bvmul",
                        "Div": "bvudiv",
                        "Mod": "bvurem",
                    }[op]
                    return f"({smt} {left_t} {right_t})", left_s
                if left_s == "Int":
                    raise SmtEncodingError(
                        f"{op} on Int is unsupported in current QF_BV encoding"
                    )
                raise SmtEncodingError(f"{op} unsupported sort {left_s}")

            if op == "Ite":
                if len(expr.args) != 3:
                    raise SmtEncodingError("Ite expects exactly three arguments")
                c_t, c_s = self._emit_expr(
                    expr.args[0], env, symbol_sort=symbol_sort, expected_sort="Bool"
                )
                if c_s != "Bool":
                    raise SmtEncodingError("Ite condition must be Bool")
                t_t, t_s = self._emit_expr(
                    expr.args[1], env, symbol_sort=symbol_sort, expected_sort=expected_sort
                )
                e_t, e_s = self._emit_expr(
                    expr.args[2], env, symbol_sort=symbol_sort, expected_sort=t_s
                )
                if t_s != e_s:
                    raise SmtEncodingError("Ite branch sort mismatch")
                return f"(ite {c_t} {t_t} {e_t})", t_s

        raise SmtEncodingError(f"unsupported TAC expression form: {expr!r}")
