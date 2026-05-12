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
    mod,
    mul,
    sub,
    term,
)

_LEMMA_BOUNDS = "bounds"
_LEMMA_BV256_RANGE = "bv256_range"


class _OpName:
    INT_MUL_DIV = "int.mul_div"
    INT_CEIL_DIV = "int.ceil_div"

    @staticmethod
    def narrow(width: int) -> str:
        return f"narrow.bv{width}"


class _SmtName:
    INT_MUL_DIV = "int_mul_div"
    INT_CEIL_DIV = "int_ceil_div"
    BV256_ADD = "int.bv256_add"
    BV256_SUB = "int.bv256_sub"
    BV256_MUL = "int.bv256_mul"
    BV256_DIV = "int.bv256_div"
    BV256_MOD = "int.bv256_mod"
    BV256_SHL = "int.bv256_shl"
    BV256_LSHR = "int.bv256_lshr"
    BV256_AND = "int.bv256_and"
    BV256_XOR = "int.bv256_xor"
    BV256_OR = "int.bv256_or"
    ITE = "ite"

    @staticmethod
    def narrow(width: int) -> str:
        return f"narrow.bv{width}"


class _LemmaName:
    INT_MUL_DIV_BOUNDS = "lemma_int_mul_div_bounds"
    INT_CEIL_DIV_BOUNDS = "lemma_int_ceil_div_bounds"

    @staticmethod
    def narrow_range(width: int) -> str:
        return f"lemma_narrow_bv{width}_range"


_A = "a"
_B = "b"
_C = "c"
_R = "r"
_X = "x"
_Y = "y"
_BINARY_PARAMS = ((_X, Int), (_Y, Int))


class _Builder(Protocol):
    def op_config(self, name: str, default: OpConfig) -> OpConfig: ...

    def declare_fun(self, name: str, args: Sequence, ret) -> None: ...

    def define_fun(self, name: str, params: Sequence[tuple[str, object]], ret, body: Term) -> None: ...

    def record_call(self, op_name: str, args: tuple[Term, ...], raw_result: Term): ...

    def require_lemma_def(self, lemma: "LemmaSchema") -> None: ...

    def int_lit(self, value: int) -> Term: ...

    def bv256_mod(self) -> Term: ...

    def bv256_max(self) -> Term: ...

    def bv_range(self, width: int, x: Term) -> Term: ...


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
    name = _LemmaName.INT_MUL_DIV_BOUNDS
    params = ((_A, Int), (_B, Int), (_C, Int), (_R, Int))

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
    name = _OpName.INT_MUL_DIV
    default_config = OpConfig(
        mode=OpMode.UF,
        lemmas=(_LEMMA_BOUNDS,),
        instantiate_lemmas=True,
    )
    lemmas = {_LEMMA_BOUNDS: IntMulDivBoundsLemma()}

    def __call__(self, a: Term, b: Term, c: Term) -> Term:
        cfg = self.config()
        if cfg.mode is OpMode.INLINE:
            return div(mul(a, b), c)
        if cfg.mode is OpMode.DEFINE_FUN:
            self._require_define_fun()
            return app(_SmtName.INT_MUL_DIV, [a, b, c], Int)
        if cfg.mode is OpMode.UF:
            self.vc.declare_fun(_SmtName.INT_MUL_DIV, (Int, Int, Int), Int)
            raw = app(_SmtName.INT_MUL_DIV, [a, b, c], Int)
            call = self.vc.record_call(self.name, (a, b, c), raw)
            return Term(
                raw.text,
                raw.sort,
                callsites=raw.callsites + (call,),
                direct_callsite=call,
            )
        raise ValueError(cfg.mode)

    def _require_define_fun(self) -> None:
        a = term(_A, Int)
        b = term(_B, Int)
        c = term(_C, Int)
        self.vc.define_fun(
            _SmtName.INT_MUL_DIV,
            ((_A, Int), (_B, Int), (_C, Int)),
            Int,
            div(mul(a, b), c),
        )


class IntCeilDivBoundsLemma(LemmaSchema):
    name = _LemmaName.INT_CEIL_DIV_BOUNDS
    params = ((_A, Int), (_B, Int), (_R, Int))

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
    name = _OpName.INT_CEIL_DIV
    default_config = OpConfig(
        mode=OpMode.UF,
        lemmas=(_LEMMA_BOUNDS,),
        instantiate_lemmas=True,
    )
    lemmas = {_LEMMA_BOUNDS: IntCeilDivBoundsLemma()}

    def __call__(self, a: Term, b: Term) -> Term:
        cfg = self.config()
        if cfg.mode is OpMode.INLINE:
            return div(add(a, b), b)
        if cfg.mode is OpMode.DEFINE_FUN:
            self._require_define_fun()
            return app(_SmtName.INT_CEIL_DIV, [a, b], Int)
        if cfg.mode is OpMode.UF:
            self.vc.declare_fun(_SmtName.INT_CEIL_DIV, (Int, Int), Int)
            raw = app(_SmtName.INT_CEIL_DIV, [a, b], Int)
            call = self.vc.record_call(self.name, (a, b), raw)
            return Term(
                raw.text,
                raw.sort,
                callsites=raw.callsites + (call,),
                direct_callsite=call,
            )
        raise ValueError(cfg.mode)

    def _require_define_fun(self) -> None:
        a = term(_A, Int)
        b = term(_B, Int)
        self.vc.define_fun(
            _SmtName.INT_CEIL_DIV,
            ((_A, Int), (_B, Int)),
            Int,
            div(add(a, b), b),
        )


class NarrowRangeLemma(LemmaSchema):
    params = ((_R, Int),)

    def __init__(self, width: int) -> None:
        self.width = width
        self.name = _LemmaName.narrow_range(width)

    def body(self, vc: _Builder, params: tuple[Term, ...]) -> Term:
        (r,) = params
        return vc.bv_range(self.width, r)

    def instance_args(self, call: CallSite) -> tuple[Term, ...]:
        return (call.result_for_lemma(),)


class NarrowOp(OpModel):
    def __init__(self, vc: _Builder, width: int) -> None:
        super().__init__(vc)
        self.width = width
        self.name = _OpName.narrow(width)
        self.default_config = OpConfig(
            mode=OpMode.DEFINE_FUN,
            lemmas=(_LEMMA_BV256_RANGE,),
            instantiate_lemmas=True,
        )
        self.lemmas = {_LEMMA_BV256_RANGE: NarrowRangeLemma(width)}

    def __call__(self, x: Term) -> Term:
        cfg = self.config()
        if cfg.mode is not OpMode.DEFINE_FUN:
            raise ValueError(f"{self.name} supports only DEFINE_FUN mode")
        smt_name = _SmtName.narrow(self.width)
        self.vc.define_fun(smt_name, ((_X, Int),), Int, term(_X, Int))
        raw = app(smt_name, [x], Int)
        call = self.vc.record_call(self.name, (x,), raw)
        return Term(
            raw.text,
            raw.sort,
            callsites=raw.callsites + (call,),
            direct_callsite=call,
        )


class NarrowOps:
    def __init__(self, vc: _Builder) -> None:
        self.bv32 = NarrowOp(vc, 32)
        self.bv64 = NarrowOp(vc, 64)
        self.bv128 = NarrowOp(vc, 128)
        self.bv256 = NarrowOp(vc, 256)

    def __call__(self, x: Term) -> Term:
        return self.bv256(x)

    def models(self) -> tuple[NarrowOp, ...]:
        return (self.bv32, self.bv64, self.bv128, self.bv256)


class Bv256Ops:
    def __init__(self, vc: _Builder) -> None:
        self.vc = vc

    def range(self, x: Term) -> Term:
        return self.vc.bv_range(256, x)

    def add(self, a: Term, b: Term) -> Term:
        self._require_add_define_fun()
        return app(_SmtName.BV256_ADD, [a, b], Int)

    def sub(self, a: Term, b: Term) -> Term:
        self._require_sub_define_fun()
        return app(_SmtName.BV256_SUB, [a, b], Int)

    def mul(self, a: Term, b: Term) -> Term:
        x, y = self._binary_args()
        self._require_binary_define_fun(
            _SmtName.BV256_MUL,
            mod(mul(x, y), self.vc.bv256_mod()),
        )
        return app(_SmtName.BV256_MUL, [a, b], Int)

    def div(self, a: Term, b: Term) -> Term:
        x, y = self._binary_args()
        self._require_binary_define_fun(_SmtName.BV256_DIV, div(x, y))
        return app(_SmtName.BV256_DIV, [a, b], Int)

    def mod(self, a: Term, b: Term) -> Term:
        x, y = self._binary_args()
        self._require_binary_define_fun(_SmtName.BV256_MOD, mod(x, y))
        return app(_SmtName.BV256_MOD, [a, b], Int)

    def shl(self, a: Term, b: Term) -> Term:
        return self._uf(_SmtName.BV256_SHL, a, b)

    def lshr(self, a: Term, b: Term) -> Term:
        return self._uf(_SmtName.BV256_LSHR, a, b)

    def and_(self, a: Term, b: Term) -> Term:
        return self._uf(_SmtName.BV256_AND, a, b)

    def xor(self, a: Term, b: Term) -> Term:
        return self._uf(_SmtName.BV256_XOR, a, b)

    def or_(self, a: Term, b: Term) -> Term:
        return self._uf(_SmtName.BV256_OR, a, b)

    def _require_add_define_fun(self) -> None:
        x, y = self._binary_args()
        raw = add(x, y)
        self.vc.define_fun(
            _SmtName.BV256_ADD,
            _BINARY_PARAMS,
            Int,
            app(
                _SmtName.ITE,
                [
                    le(raw, self.vc.bv256_max()),
                    raw,
                    app("-", [raw, self.vc.bv256_mod()], Int),
                ],
                Int,
            ),
        )

    def _require_sub_define_fun(self) -> None:
        x, y = self._binary_args()
        raw = sub(x, y)
        self.vc.define_fun(
            _SmtName.BV256_SUB,
            _BINARY_PARAMS,
            Int,
            app(
                _SmtName.ITE,
                [
                    ge(raw, self.vc.int_lit(0)),
                    raw,
                    add(raw, self.vc.bv256_mod()),
                ],
                Int,
            ),
        )

    def _require_binary_define_fun(self, name: str, body: Term) -> None:
        self.vc.define_fun(name, _BINARY_PARAMS, Int, body)

    def _binary_args(self) -> tuple[Term, Term]:
        return term(_X, Int), term(_Y, Int)

    def _uf(self, name: str, a: Term, b: Term) -> Term:
        self.vc.declare_fun(name, (Int, Int), Int)
        return app(name, [a, b], Int)


class Ops:
    def __init__(self, vc: _Builder) -> None:
        self.int_mul_div = IntMulDivOp(vc)
        self.int_ceil_div = IntCeilDivOp(vc)
        self.narrow = NarrowOps(vc)
        self.bv256 = Bv256Ops(vc)
        self._by_name = {
            self.int_mul_div.name: self.int_mul_div,
            self.int_ceil_div.name: self.int_ceil_div,
        }
        self._by_name.update((op.name, op) for op in self.narrow.models())

    def by_name(self, name: str) -> OpModel:
        return self._by_name[name]
