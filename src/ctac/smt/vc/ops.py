from __future__ import annotations

from dataclasses import dataclass
from typing import Protocol, Sequence

from ctac.smt.vc.config import OpConfig, OpMode
from ctac.smt.vc.script import DefineFun
from ctac.smt.vc.terms import (
    Bool,
    Int,
    Term,
    add,
    and_,
    app,
    div,
    ge,
    gt,
    implies,
    le,
    lt,
    mul,
    term,
)


class _Builder(Protocol):
    def op_config(self, name: str, default: OpConfig) -> OpConfig: ...

    def declare_fun(self, name: str, args: Sequence, ret) -> None: ...

    def define_fun(self, name: str, params: Sequence[tuple[str, object]], ret, body: Term) -> None: ...

    def record_call(self, op_name: str, args: tuple[Term, ...], raw_result: Term): ...

    def require_lemma_def(self, lemma: "LemmaSchema") -> None: ...

    def int_lit(self, value: int) -> Term: ...


@dataclass
class CallSite:
    id: int
    op_name: str
    args: tuple[Term, ...]
    raw_result: Term
    bound_result: Term | None
    scope: object | None
    block: str | None
    stmt_id: str | int | None

    def result_for_lemma(self) -> Term:
        return self.bound_result or self.raw_result


class LemmaSchema:
    name: str
    params: tuple[tuple[str, object], ...]

    def body(self, vc: _Builder, params: tuple[Term, ...]) -> Term:
        raise NotImplementedError

    def instance_args(self, call: CallSite) -> tuple[Term, ...]:
        raise NotImplementedError

    def define_fun(self, vc: _Builder) -> DefineFun:
        params = tuple((name, sort) for name, sort in self.params)
        body_terms = tuple(term(name, sort) for name, sort in params)
        body = self.body(vc, body_terms)
        return DefineFun(self.name, params, Bool, body)


class OpModel:
    name: str
    default_config: OpConfig
    lemmas: dict[str, LemmaSchema]

    def __init__(self, vc: _Builder) -> None:
        self.vc = vc

    def config(self) -> OpConfig:
        return self.vc.op_config(self.name, self.default_config)

    def __call__(self, *args: Term) -> Term:
        raise NotImplementedError


class IntMulDivBoundsLemma(LemmaSchema):
    name = "lemma_int_mul_div_bounds"
    params = (("a", Int), ("b", Int), ("c", Int), ("r", Int))

    def body(self, vc: _Builder, params: tuple[Term, ...]) -> Term:
        a, b, c, r = params
        zero = vc.int_lit(0)
        one = vc.int_lit(1)
        prod = mul(a, b)
        return implies(
            gt(c, zero),
            and_(
                le(mul(c, r), prod),
                lt(prod, mul(c, add(r, one))),
            ),
        )

    def instance_args(self, call: CallSite) -> tuple[Term, ...]:
        a, b, c = call.args
        return (a, b, c, call.result_for_lemma())


class IntMulDivOp(OpModel):
    name = "int.mul_div"
    default_config = OpConfig(
        mode=OpMode.UF,
        lemmas=("bounds",),
        instantiate_lemmas=True,
    )
    lemmas = {"bounds": IntMulDivBoundsLemma()}

    def __call__(self, a: Term, b: Term, c: Term) -> Term:
        cfg = self.config()
        if cfg.mode is OpMode.INLINE:
            return div(mul(a, b), c)
        if cfg.mode is OpMode.DEFINE_FUN:
            self._require_define_fun()
            return app("int_mul_div", [a, b, c], Int)
        if cfg.mode is OpMode.UF:
            self.vc.declare_fun("int_mul_div", (Int, Int, Int), Int)
            raw = app("int_mul_div", [a, b, c], Int)
            call = self.vc.record_call(self.name, (a, b, c), raw)
            return Term(
                raw.text,
                raw.sort,
                callsites=raw.callsites + (call,),
                direct_callsite=call,
            )
        raise ValueError(cfg.mode)

    def _require_define_fun(self) -> None:
        a = term("a", Int)
        b = term("b", Int)
        c = term("c", Int)
        self.vc.define_fun(
            "int_mul_div",
            (("a", Int), ("b", Int), ("c", Int)),
            Int,
            div(mul(a, b), c),
        )


class IntCeilDivBoundsLemma(LemmaSchema):
    name = "lemma_int_ceil_div_bounds"
    params = (("a", Int), ("b", Int), ("r", Int))

    def body(self, vc: _Builder, params: tuple[Term, ...]) -> Term:
        a, b, r = params
        zero = vc.int_lit(0)
        return implies(
            gt(b, zero),
            and_(
                ge(mul(b, r), a),
                lt(mul(b, r), add(a, b)),
            ),
        )

    def instance_args(self, call: CallSite) -> tuple[Term, ...]:
        a, b = call.args
        return (a, b, call.result_for_lemma())


class IntCeilDivOp(OpModel):
    name = "int.ceil_div"
    default_config = OpConfig(
        mode=OpMode.UF,
        lemmas=("bounds",),
        instantiate_lemmas=True,
    )
    lemmas = {"bounds": IntCeilDivBoundsLemma()}

    def __call__(self, a: Term, b: Term) -> Term:
        cfg = self.config()
        if cfg.mode is OpMode.INLINE:
            return div(add(a, b), b)
        if cfg.mode is OpMode.DEFINE_FUN:
            self._require_define_fun()
            return app("int_ceil_div", [a, b], Int)
        if cfg.mode is OpMode.UF:
            self.vc.declare_fun("int_ceil_div", (Int, Int), Int)
            raw = app("int_ceil_div", [a, b], Int)
            call = self.vc.record_call(self.name, (a, b), raw)
            return Term(
                raw.text,
                raw.sort,
                callsites=raw.callsites + (call,),
                direct_callsite=call,
            )
        raise ValueError(cfg.mode)

    def _require_define_fun(self) -> None:
        a = term("a", Int)
        b = term("b", Int)
        self.vc.define_fun(
            "int_ceil_div",
            (("a", Int), ("b", Int)),
            Int,
            div(add(a, b), b),
        )


class Bv256Ops:
    def __init__(self, vc: _Builder) -> None:
        self.vc = vc

    def range(self, x: Term) -> Term:
        return and_(le(self.vc.int_lit(0), x), le(x, self.vc.bv256_max()))

    def add(self, a: Term, b: Term) -> Term:
        raw = add(a, b)
        return app(
            "ite",
            [
                le(raw, self.vc.bv256_max()),
                raw,
                app("-", [raw, self.vc.bv256_mod()], Int),
            ],
            Int,
        )


class Ops:
    def __init__(self, vc: _Builder) -> None:
        self.int_mul_div = IntMulDivOp(vc)
        self.int_ceil_div = IntCeilDivOp(vc)
        self.bv256 = Bv256Ops(vc)
        self._by_name = {
            self.int_mul_div.name: self.int_mul_div,
            self.int_ceil_div.name: self.int_ceil_div,
        }

    def by_name(self, name: str) -> OpModel:
        return self._by_name[name]
