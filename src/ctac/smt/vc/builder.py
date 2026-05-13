from __future__ import annotations

import re
from collections import OrderedDict
from contextlib import contextmanager
from dataclasses import dataclass
from typing import Iterator, Literal, Sequence

from ctac.smt.vc.bytemap import UfDefineFunBytemap
from ctac.smt.vc.config import FactKind, FactPlacement, OpConfig, VCConfig
from ctac.smt.vc.ops import CallSite, LemmaSchema, Ops
from ctac.smt.vc.script import Assertion, ConstDecl, DefineFun, FunDecl, Scope, VCScript
from ctac.smt.vc.terms import Bool, Int, Sort, Term, and_, app, eq, le, not_, term

_BV256_MOD = 1 << 256
_BV256_MAX = _BV256_MOD - 1
_COMMON_BV_WIDTHS = (32, 64, 128, 256)
_SMALL_INT_INLINE_LIMIT = 1 << 14
_NEAR_POW2_DELTA_LIMIT = 1 << 16


@dataclass(frozen=True)
class StmtContext:
    block: str | None
    stmt_id: str | int | None
    comment: str | None = None


@dataclass(frozen=True)
class IntRange:
    lo: int | Term | None = None
    hi: int | Term | None = None

    @staticmethod
    def bv32() -> "IntRange":
        return IntRange(0, (1 << 32) - 1)

    @staticmethod
    def bv64() -> "IntRange":
        return IntRange(0, (1 << 64) - 1)

    @staticmethod
    def bv128() -> "IntRange":
        return IntRange(0, (1 << 128) - 1)

    @staticmethod
    def bv256() -> "IntRange":
        return IntRange(0, _BV256_MAX)

    @staticmethod
    def u64() -> "IntRange":
        return IntRange.bv64()


@dataclass(frozen=True)
class VCFact:
    kind: FactKind
    term: Term | None
    scope: Scope | None = None
    name: str | None = None
    comment: str | None = None
    origin: str | None = None
    placement: FactPlacement = FactPlacement.SCOPED
    block: str | None = None
    stmt_id: str | int | None = None


def sanitize_name(raw: str) -> str:
    out = re.sub(r"[^A-Za-z0-9_]", "_", raw)
    if not out:
        return "_"
    if out[0].isdigit():
        return "_" + out
    return out


def _is_pow2(n: int) -> int | None:
    if n <= 0 or n & (n - 1):
        return None
    return n.bit_length() - 1


def _common_bv_max_width(value: int) -> int | None:
    if value < 0:
        return None
    for width in _COMMON_BV_WIDTHS:
        if value == (1 << width) - 1:
            return width
    return None


def _near_pow2(value: int) -> tuple[int, int] | None:
    if value <= 0:
        return None
    width = value.bit_length()
    candidates = (width - 1, width)
    best: tuple[int, int] | None = None
    for pow_k in candidates:
        if pow_k <= 0:
            continue
        delta = value - (1 << pow_k)
        if abs(delta) >= _NEAR_POW2_DELTA_LIMIT:
            continue
        if delta == 0:
            continue
        if best is None or abs(delta) < abs(best[1]):
            best = (pow_k, delta)
    return best


class BlockBuilder:
    def __init__(self, vc: "VCBuilder", scope: Scope) -> None:
        self.vc = vc
        self.scope = scope

    def def_(
        self,
        lhs: Term,
        rhs: Term,
        *,
        name: str | None = None,
        inline: bool = False,
        placement: FactPlacement = FactPlacement.SCOPED,
    ) -> None:
        if inline:
            self.vc.inline_def(lhs, rhs)
            self._bind_direct_result(rhs, lhs)
            return
        self.vc.fact(
            FactKind.DEF,
            eq(lhs, rhs),
            scope=self.scope,
            name=name or self.vc.auto_name("def", lhs.text),
            origin="def",
            placement=placement,
        )
        self._bind_direct_result(rhs, lhs)

    def _bind_direct_result(self, rhs: Term, lhs: Term) -> None:
        site = rhs.direct_callsite
        if site is not None and hasattr(site, "bound_result"):
            site.bound_result = lhs

    def assume(self, phi: Term, *, name: str | None = None) -> None:
        self.vc.fact(
            FactKind.ASSUME,
            phi,
            scope=self.scope,
            name=name or self.vc.auto_name("assume"),
            origin="assume",
        )

    def assert_(self, phi: Term, *, name: str | None = None) -> None:
        self.vc.fact(
            FactKind.ASSERT,
            phi,
            scope=self.scope,
            name=name or self.vc.auto_name("assert"),
            origin="assert",
        )

    def range(
        self,
        x: Term,
        r: IntRange | None = None,
        *,
        lo: int | Term | None = None,
        hi: int | Term | None = None,
        name: str | None = None,
    ) -> None:
        self.vc.range(x, r, lo=lo, hi=hi, scope=self.scope, name=name)


class VCBuilder:
    def __init__(self, config: VCConfig | None = None) -> None:
        self.config = config or VCConfig()
        self.const_decls: OrderedDict[str, ConstDecl] = OrderedDict()
        self.fun_decls: OrderedDict[str, FunDecl] = OrderedDict()
        self.define_funs: OrderedDict[str, DefineFun] = OrderedDict()
        self.lemma_defs: OrderedDict[str, DefineFun] = OrderedDict()
        self.facts: list[VCFact] = []
        self.call_sites: list[CallSite] = []
        self.scope_stack: list[Scope] = []
        self.stmt_stack: list[StmtContext] = []
        self.ops = Ops(self)
        self.bytemap = UfDefineFunBytemap(self, self.config.bytemap)
        self._finalized = False

    def const(self, name: str, sort: Sort) -> Term:
        self.const_decls.setdefault(name, ConstDecl(name, sort))
        return Term(name, sort)

    def declare_fun(self, name: str, args: Sequence[Sort], ret: Sort) -> None:
        self.fun_decls.setdefault(name, FunDecl(name, tuple(args), ret))

    def define_fun(
        self,
        name: str,
        params: Sequence[tuple[str, Sort]],
        ret: Sort,
        body: Term,
    ) -> None:
        self.define_funs.setdefault(name, DefineFun(name, tuple(params), ret, body))

    def inline_def(self, lhs: Term, rhs: Term) -> None:
        self.const_decls.pop(lhs.text, None)
        self.define_fun(lhs.text, (), lhs.sort, rhs)

    def define_int_const(self, name: str, value: int | Term | str) -> Term:
        if isinstance(value, Term):
            body = value
        else:
            body = term(str(value), Int)
        self.define_fun(name, (), Int, body)
        return term(name, Int)

    def int_lit(self, value: int) -> Term:
        if abs(value) < (1 << 16):
            return term(str(value), Int)
        if value == _BV256_MOD:
            return self.bv256_mod()
        if value == _BV256_MAX:
            return self.bv256_max()
        max_width = _common_bv_max_width(value)
        if max_width is not None:
            return self.bv_max(max_width)
        pow_k = _is_pow2(value)
        if pow_k is not None:
            return self.pow2_const(pow_k)
        near = _near_pow2(value)
        if near is not None:
            pow_k, delta = near
            return self._near_pow2_const(pow_k, delta)
        return term(str(value), Int)

    def pow2_const(self, width: int) -> Term:
        return self.define_int_const(f"POW2_{width}", 1 << width)

    def _near_pow2_const(self, pow_k: int, delta: int) -> Term:
        op = "+" if delta > 0 else "-"
        sign_name = "PLUS" if delta > 0 else "MINUS"
        delta_abs = abs(delta)
        delta_pow_k = _is_pow2(delta_abs)
        if delta_abs <= _SMALL_INT_INLINE_LIMIT:
            delta_term = term(str(delta_abs), Int)
            delta_name = str(delta_abs)
        elif delta_pow_k is not None:
            delta_term = self.pow2_const(delta_pow_k)
            delta_name = f"POW2_{delta_pow_k}"
        else:
            delta_term = self.int_lit(delta_abs)
            delta_name = str(delta_abs)
        return self.define_int_const(
            f"POW2_{pow_k}_{sign_name}_{delta_name}",
            app(op, [self.pow2_const(pow_k), delta_term], Int),
        )

    def bv256_mod(self) -> Term:
        return self.define_int_const("BV256_MOD", _BV256_MOD)

    def bv256_max(self) -> Term:
        return self.define_int_const(
            "BV256_MAX",
            app("-", [self.bv256_mod(), self.int_lit(1)], Int),
        )

    def bv_mod(self, width: int) -> Term:
        if width == 256:
            return self.bv256_mod()
        self._check_common_bv_width(width)
        return self.define_int_const(f"BV{width}_MOD", 1 << width)

    def bv_max(self, width: int) -> Term:
        if width == 256:
            return self.bv256_max()
        self._check_common_bv_width(width)
        return self.define_int_const(
            f"BV{width}_MAX",
            app("-", [self.bv_mod(width), self.int_lit(1)], Int),
        )

    def bv_range(self, width: int, x: Term) -> Term:
        self.require_bv_range_define_fun(width)
        return app(f"int.in_bv{width}", [x], Bool)

    def require_bv_range_define_fun(self, width: int) -> None:
        self._check_common_bv_width(width)
        x = term("x", Int)
        self.define_fun(
            f"int.in_bv{width}",
            (("x", Int),),
            Bool,
            and_(le(self.int_lit(0), x), le(x, self.bv_max(width))),
        )

    @contextmanager
    def block(self, name: str, guard: Term | None = None) -> Iterator[BlockBuilder]:
        if guard is None:
            guard = self.const(f"BLK_{sanitize_name(name)}", Bool)
        scope = Scope(name=name, guard=guard)
        self.scope_stack.append(scope)
        try:
            yield BlockBuilder(self, scope)
        finally:
            self.scope_stack.pop()

    @contextmanager
    def stmt(
        self,
        stmt_id: str | int | None,
        comment: str | None = None,
    ) -> Iterator[None]:
        block = self.current_scope().name if self.current_scope() else None
        self.stmt_stack.append(StmtContext(block=block, stmt_id=stmt_id, comment=comment))
        try:
            yield
        finally:
            self.stmt_stack.pop()

    def current_scope(self) -> Scope | None:
        return self.scope_stack[-1] if self.scope_stack else None

    def current_stmt(self) -> StmtContext | None:
        return self.stmt_stack[-1] if self.stmt_stack else None

    def assert_(
        self,
        phi: Term,
        *,
        name: str | None = None,
        scope: Scope | Literal["current"] | None = "current",
        comment: str | None = None,
        origin: str | None = None,
    ) -> None:
        self.fact(
            FactKind.ASSERT,
            phi,
            scope=scope,
            name=name,
            comment=comment,
            origin=origin,
        )

    def fact(
        self,
        kind: FactKind,
        phi: Term,
        *,
        name: str | None = None,
        scope: Scope | Literal["current"] | None = "current",
        comment: str | None = None,
        origin: str | None = None,
        placement: FactPlacement = FactPlacement.SCOPED,
    ) -> None:
        if phi.text == "true":
            return
        resolved = self.current_scope() if scope == "current" else scope
        stmt = self.current_stmt()
        self.facts.append(
            VCFact(
                kind,
                phi,
                scope=resolved,
                name=name,
                comment=self._fact_comment(comment, stmt),
                origin=origin,
                placement=placement,
                block=self._fact_block(resolved, stmt),
                stmt_id=stmt.stmt_id if stmt else None,
            )
        )

    def section(self, title: str) -> None:
        self.facts.append(
            VCFact(
                FactKind.CFG,
                None,
                scope=None,
                name=None,
                comment=title,
                origin="section",
                placement=FactPlacement.GLOBAL,
            )
        )

    def raw_fact(
        self,
        raw: str,
        *,
        kind: FactKind = FactKind.CFG,
        name: str | None = None,
        comment: str | None = None,
        origin: str | None = None,
    ) -> None:
        self.fact(
            kind,
            term(raw, Bool),
            scope=None,
            name=name,
            comment=comment,
            origin=origin or kind.name.lower(),
            placement=FactPlacement.GLOBAL,
        )

    def cfg_fact(
        self,
        phi: Term,
        *,
        name: str | None = None,
        comment: str | None = None,
        origin: str | None = "cfg",
    ) -> None:
        self.fact(
            FactKind.CFG,
            phi,
            scope=None,
            name=name,
            comment=comment,
            origin=origin,
            placement=FactPlacement.GLOBAL,
        )

    def range(
        self,
        x: Term,
        r: IntRange | None = None,
        *,
        lo: int | Term | None = None,
        hi: int | Term | None = None,
        scope: Scope | Literal["current"] | None = "current",
        name: str | None = None,
        placement: FactPlacement = FactPlacement.SCOPED,
    ) -> None:
        if r is not None:
            lo, hi = r.lo, r.hi
        width = self._common_bv_width(lo, hi)
        if width is not None:
            constraint = self.bv_range(width, x)
        else:
            constraints: list[Term] = []
            if lo is not None:
                constraints.append(le(self._literal_or_term(lo), x))
            if hi is not None:
                constraints.append(le(x, self._literal_or_term(hi)))
            if lo is not None and hi is not None:
                constraint = app("<=", [self._literal_or_term(lo), x, self._literal_or_term(hi)], Bool)
            else:
                constraint = and_(*constraints)
        self.fact(
            FactKind.RANGE,
            constraint,
            scope=scope,
            name=name or self.auto_name("range", x.text),
            origin="range",
            placement=placement,
        )

    def _common_bv_width(self, lo: int | Term | None, hi: int | Term | None) -> int | None:
        if lo != 0 or not isinstance(hi, int):
            return None
        for width in _COMMON_BV_WIDTHS:
            if hi == (1 << width) - 1:
                return width
        return None

    def _check_common_bv_width(self, width: int) -> None:
        if width not in _COMMON_BV_WIDTHS:
            known = ", ".join(str(w) for w in _COMMON_BV_WIDTHS)
            raise ValueError(f"unsupported common bv width {width}; expected one of {known}")

    def _literal_or_term(self, value: int | Term) -> Term:
        if isinstance(value, Term):
            return value
        return self.int_lit(value)

    def _fact_comment(self, comment: str | None, stmt: StmtContext | None) -> str | None:
        if comment is not None:
            return comment
        if self.config.annotate_with_cmds and stmt is not None:
            return stmt.comment
        return None

    def _fact_block(self, scope: Scope | None, stmt: StmtContext | None) -> str | None:
        if stmt is not None:
            return stmt.block
        if scope is not None:
            return scope.name
        return None

    def op_config(self, name: str, default: OpConfig) -> OpConfig:
        return self.config.op_models.get(name, default)

    def record_call(self, op_name: str, args: tuple[Term, ...], raw_result: Term) -> CallSite:
        scope = self.current_scope()
        stmt = self.current_stmt()
        call = CallSite(
            id=len(self.call_sites),
            op_name=op_name,
            args=args,
            raw_result=raw_result,
            bound_result=None,
            scope=scope,
            block=scope.name if scope else None,
            stmt_id=stmt.stmt_id if stmt else None,
        )
        self.call_sites.append(call)
        return call

    def require_lemma_def(self, lemma: LemmaSchema) -> None:
        self.lemma_defs.setdefault(lemma.name, lemma.define_fun(self))

    def generate_lemma_instances(self) -> None:
        for call in self.call_sites:
            cfg = self.op_config(call.op_name, self.ops.by_name(call.op_name).default_config)
            if not cfg.instantiate_lemmas:
                continue
            op = self.ops.by_name(call.op_name)
            for lemma_key in cfg.lemmas:
                lemma = op.lemmas[lemma_key]
                self.require_lemma_def(lemma)
                args = lemma.instance_args(call)
                phi = app(lemma.name, args, Bool)
                if cfg.lemma_scope in {"callsite", "none"}:
                    scope = None
                else:
                    raise ValueError(f"unknown lemma_scope {cfg.lemma_scope!r}")
                self.facts.append(
                    VCFact(
                        FactKind.LEMMA,
                        phi,
                        scope=scope,
                        name=self.lemma_instance_name(lemma.name, call),
                        origin="lemma-instance",
                        placement=FactPlacement.GLOBAL,
                        block=call.block,
                        stmt_id=call.stmt_id,
                    )
                )

    def dynamic_def(
        self,
        lhs: Term,
        cases: Sequence[tuple[Term, Term]],
        *,
        guarded: bool = False,
        name: str | None = None,
    ) -> None:
        if not cases:
            raise ValueError("dynamic_def requires at least one case")
        if len(cases) == 1:
            guard, rhs = cases[0]
            if guarded:
                self.fact(
                    FactKind.DEF,
                    eq(lhs, rhs),
                    scope=Scope(name=f"dynamic_{lhs.text}_0", guard=guard),
                    name=name or self.auto_name("dynamic_def", lhs.text),
                    origin="dynamic-def",
                )
            else:
                self.fact(
                    FactKind.DEF,
                    eq(lhs, rhs),
                    scope=None,
                    name=name or self.auto_name("dynamic_def", lhs.text),
                    origin="dynamic-def",
                    placement=FactPlacement.GLOBAL,
                )
            return
        if guarded:
            for i, (guard, rhs) in enumerate(cases):
                self.fact(
                    FactKind.DEF,
                    eq(lhs, rhs),
                    scope=Scope(name=f"dynamic_{lhs.text}_{i}", guard=guard),
                    name=f"{name}_{i}" if name else self.auto_name("dynamic_def", f"{lhs.text}_{i}"),
                    origin="dynamic-def",
                )
            return
        value = cases[-1][1]
        for guard, rhs in reversed(cases[:-1]):
            value = app("ite", [guard, rhs, value], lhs.sort)
        self.fact(
            FactKind.DEF,
            eq(lhs, value),
            scope=None,
            name=name or self.auto_name("dynamic_def", lhs.text),
            origin="dynamic-def",
            placement=FactPlacement.GLOBAL,
        )

    def assert_failure_objective(
        self,
        exit_var: Term,
        assert_block_guard: Term,
        assert_predicate: Term,
        *,
        name: str | None = None,
    ) -> None:
        self.const(exit_var.text, exit_var.sort)
        self.fact(
            FactKind.ASSERT,
            app("=>", [exit_var, and_(assert_block_guard, not_(assert_predicate))], Bool),
            scope=None,
            name=name or "assert_failure_objective",
            origin="assert-failure-objective",
            placement=FactPlacement.GLOBAL,
        )
        self.fact(
            FactKind.ASSERT,
            exit_var,
            scope=None,
            name=f"{name}_reachable" if name else "assert_failure_reachable",
            origin="assert-failure-objective",
            placement=FactPlacement.GLOBAL,
        )

    def auto_name(self, kind: str, subject: str | None = None) -> str:
        parts: list[str] = []
        scope = self.current_scope()
        stmt = self.current_stmt()
        if scope:
            parts.append(scope.name)
        if stmt and stmt.stmt_id is not None:
            parts.append(str(stmt.stmt_id))
        parts.append(kind)
        if subject:
            parts.append(subject)
        return "_".join(sanitize_name(p) for p in parts)

    def lemma_instance_name(self, lemma_name: str, call: CallSite) -> str:
        parts = [p for p in [call.block, call.stmt_id, lemma_name, call.id] if p is not None]
        return "_".join(sanitize_name(str(p)) for p in parts)

    def finalize(self) -> None:
        if self._finalized:
            return
        self.generate_lemma_instances()
        self.bytemap.finalize()
        self._finalized = True

    def lower_facts_to_assertions(self) -> tuple[Assertion, ...]:
        if self.config.fact_lowerer is not None:
            return self.config.fact_lowerer.lower(self)
        grouped_kinds = self.config.assertion_policy.grouped_kinds
        if not grouped_kinds:
            return tuple(self._assertion_from_fact(f) for f in self.facts)

        grouped: OrderedDict[Scope | None, list[VCFact]] = OrderedDict()
        for fact in self.facts:
            if fact.kind not in grouped_kinds:
                continue
            grouped.setdefault(self._effective_scope(fact), []).append(fact)

        emitted_groups: set[Scope | None] = set()
        assertions: list[Assertion] = []
        for fact in self.facts:
            if fact.kind not in grouped_kinds:
                assertions.append(self._assertion_from_fact(fact))
                continue
            scope = self._effective_scope(fact)
            if scope in emitted_groups:
                continue
            emitted_groups.add(scope)
            assertions.append(self._grouped_assertion(grouped[scope]))
        return tuple(assertions)

    def _assertion_from_fact(self, fact: VCFact) -> Assertion:
        return Assertion(
            fact.term,
            scope=self._effective_scope(fact),
            name=fact.name,
            comment=fact.comment,
            origin=fact.origin,
            block=fact.block,
        )

    def _effective_scope(self, fact: VCFact) -> Scope | None:
        if fact.placement is FactPlacement.GLOBAL:
            return None
        if (
            fact.placement is FactPlacement.ELIGIBLE_GLOBAL
            and self.config.globalize_eligible_facts
        ):
            return None
        return fact.scope

    def _grouped_assertion(self, facts: list[VCFact]) -> Assertion:
        first = facts[0]
        origin = "+".join(dict.fromkeys(f.origin or f.kind.name.lower() for f in facts))
        return Assertion(
            and_(*(f.term for f in facts)),
            scope=self._effective_scope(first),
            name=None,
            comment=None,
            origin=f"grouped:{origin}",
            block=first.block,
        )

    def script(self) -> VCScript:
        self.finalize()
        assertions = self.lower_facts_to_assertions()
        return VCScript(
            logic=self.config.logic,
            const_decls=tuple(self.const_decls.values()),
            fun_decls=tuple(self.fun_decls.values()),
            define_funs=tuple(self.define_funs.values()),
            lemma_defs=tuple(self.lemma_defs.values()),
            assertions=assertions,
            comments=("vc: semantic-event SMT builder",),
            produce_models=self.config.produce_models,
            produce_unsat_cores=self.config.produce_unsat_cores,
            check_sat=self.config.check_sat,
        )
