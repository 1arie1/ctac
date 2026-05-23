from __future__ import annotations

from dataclasses import dataclass
from typing import Protocol, Sequence

from ctac.ast.bit_mask import high_mask_clear_low_k, low_mask_width, shifted_contiguous_mask
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
    eq,
    ge,
    gt,
    implies,
    le,
    lt,
    mod,
    mul,
    not_,
    or_,
    sub,
    term,
)

_LEMMA_BOUNDS = "bounds"
_LEMMA_BOOL = "bool"
_LEMMA_BV256_RANGE = "bv256_range"


class _OpName:
    INT_MUL_DIV = "int.muldiv"
    INT_MUL_DIV_CEIL = "int.mul_div_ceil"
    INT_CEIL_DIV = "int.ceil_div"
    BV256_AND = "int.bv256_and"
    BV256_XOR = "int.bv256_xor"
    BV256_OR = "int.bv256_or"

    @staticmethod
    def narrow(width: int) -> str:
        return f"narrow.bv{width}"


class _SmtName:
    INT_MUL_DIV = "int.muldiv"
    INT_MUL_DIV_CEIL = "int_mul_div_ceil"
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
    TO_S256 = "to_s256"
    FROM_S256 = "from_s256"
    BV256_IS_NEG = "bv256.is_neg"
    BV256_SLT = "bv256.slt"
    BV256_SLE = "bv256.sle"
    ITE = "ite"

    @staticmethod
    def narrow(width: int) -> str:
        return f"narrow.bv{width}"

    @staticmethod
    def bv256_shl_const(k: int) -> str:
        return f"bv256.shl_{k}"

    @staticmethod
    def bv256_lshr_const(k: int) -> str:
        return f"bv256.lshr_{k}"

    @staticmethod
    def bv256_and_low_mask(k: int) -> str:
        return f"bv256.and_{_hex_mask_suffix((1 << k) - 1)}"

    @staticmethod
    def bv256_and_clear_low(k: int) -> str:
        return f"bv256.and_clear_low_{k}"

    @staticmethod
    def bv256_and_slice(lo: int, width: int) -> str:
        return f"bv256.and_slice_{lo}_{width}"


class _LemmaName:
    INT_MUL_DIV_BOUNDS = "lemma_int_mul_div_bounds"
    INT_MUL_DIV_CEIL_BOUNDS = "lemma_int_mul_div_ceil_bounds"
    INT_CEIL_DIV_BOUNDS = "lemma_int_ceil_div_bounds"
    BV256_AND_BOOL = "lemma_bv256_and_bool"
    BV256_XOR_BOOL = "lemma_bv256_xor_bool"
    BV256_OR_BOOL = "lemma_bv256_or_bool"

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


def _hex_mask_suffix(value: int) -> str:
    return f"{value:X}"


def _literal_value(term_: Term, vc: "_Builder | None" = None) -> int | None:
    """Return the integer value of ``term_`` if it's a literal or a
    named 0-ary define-fun bound to one. Returns ``None`` otherwise.

    The named-constant lookup matters for sea: ``int_lit`` routes
    large constants (``BV64_MAX``, ``POW2_14``, ``POW2_256_MINUS_16384``,
    ...) through ``define_int_const``, so their term text is the name
    rather than the literal. Without the lookup the ``shl``/``lshr``/
    ``and_`` const-fold special cases miss and the op falls through
    to a UF, leaving z3 free to pick wrong values.
    """
    text = term_.text
    try:
        return int(text, 0)
    except ValueError:
        pass
    if vc is not None:
        named = getattr(vc, "named_int_consts", None)
        if named is not None:
            return named.get(text)
    return None


class _Builder(Protocol):
    def op_config(self, name: str, default: OpConfig) -> OpConfig: ...

    def declare_fun(self, name: str, args: Sequence, ret) -> None: ...

    def define_fun(self, name: str, params: Sequence[tuple[str, object]], ret, body: Term) -> None: ...

    def record_call(self, op_name: str, args: tuple[Term, ...], raw_result: Term): ...

    def require_lemma_def(self, lemma: "LemmaSchema") -> None: ...

    def int_lit(self, value: int) -> Term: ...

    def define_int_const(self, name: str, value: int | Term | str) -> Term: ...

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
    # Rule 7: set to True when this call's bound_result is the LHS of
    # a scoped (block-guarded) static def. Partial axioms whose target
    # is such an LHS can stay global without unsoundness — when the
    # block is bypassed, the LHS is free and the axiom is trivially
    # satisfied. Provides loose bounds to NLA without leaking
    # constraints onto shared upstream variables.
    bound_def_scoped: bool = False

    def result_for_lemma(self) -> Term:
        return self.bound_result or self.raw_result


class LemmaSchema:
    name: str
    params: tuple[tuple[str, object], ...]
    # Rule 1 / 4: an axiom is `partial` if it is restricting (e.g.
    # narrow-range, bytemap select_range) rather than defining (e.g.
    # bvxor-bool, muldiv-bounds). Partial axioms imply preconditions
    # on the operator's arguments after inlining, so they must be
    # guarded by the callsite's block unless rule 7 applies. Total
    # axioms add no constraint on arguments and are safe to emit
    # globally.
    partial: bool = False

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


# Lemma: if c > 0 and r = int.muldiv(a, b, c), then r is the floor
# quotient of a*b by c: c*r <= a*b < c*(r + 1).
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


# Lemma: if c > 0 and r = int.mul_div_ceil(a, b, c), then r is the
# ceiling quotient of a*b by c: c*r >= a*b and c*r < a*b + c.
class IntMulDivCeilBoundsLemma(LemmaSchema):
    name = _LemmaName.INT_MUL_DIV_CEIL_BOUNDS
    params = ((_A, Int), (_B, Int), (_C, Int), (_R, Int))

    def body(self, vc: _Builder, params: tuple[Term, ...]) -> Term:
        a, b, c, r = params
        zero = vc.int_lit(0)
        prod = mul(a, b)
        return implies(
            gt(c, zero),
            and_(
                ge(mul(c, r), prod),
                lt(mul(c, r), add(prod, c)),
            ),
        )

    def instance_args(self, call: CallSite) -> tuple[Term, ...]:
        a, b, c = call.args
        return (a, b, c, call.result_for_lemma())


class IntMulDivCeilOp(OpModel):
    name = _OpName.INT_MUL_DIV_CEIL
    default_config = OpConfig(
        mode=OpMode.UF,
        lemmas=(_LEMMA_BOUNDS,),
        instantiate_lemmas=True,
    )
    lemmas = {_LEMMA_BOUNDS: IntMulDivCeilBoundsLemma()}

    def __call__(self, a: Term, b: Term, c: Term) -> Term:
        cfg = self.config()
        if cfg.mode is OpMode.INLINE:
            return _mul_div_ceil_body(self.vc, a, b, c)
        if cfg.mode is OpMode.DEFINE_FUN:
            self._require_define_fun()
            return app(_SmtName.INT_MUL_DIV_CEIL, [a, b, c], Int)
        if cfg.mode is OpMode.UF:
            self.vc.declare_fun(
                _SmtName.INT_MUL_DIV_CEIL, (Int, Int, Int), Int
            )
            raw = app(_SmtName.INT_MUL_DIV_CEIL, [a, b, c], Int)
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
            _SmtName.INT_MUL_DIV_CEIL,
            ((_A, Int), (_B, Int), (_C, Int)),
            Int,
            _mul_div_ceil_body(self.vc, a, b, c),
        )


def _mul_div_ceil_body(vc: _Builder, a: Term, b: Term, c: Term) -> Term:
    """``ceil(a*b/c) = (a*b + c - 1) / c`` for ``a, b >= 0, c > 0``.

    Same Knuth-identity reasoning as in ``_ceil_div_body``; the
    bounds lemma is what nails the value in UF mode (the production
    path), this expression matters only for INLINE / DEFINE_FUN.
    """
    one = vc.int_lit(1)
    return div(add(mul(a, b), sub(c, one)), c)


# Lemma: if b > 0 and r = int.ceil_div(a, b), then r is the ceiling
# quotient of a by b: b*r >= a and b*r < a + b.
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
            return _ceil_div_body(self.vc, a, b)
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
            _ceil_div_body(self.vc, a, b),
        )


def _ceil_div_body(vc: _Builder, a: Term, b: Term) -> Term:
    """``ceil(a/b) = (a + b - 1) / b`` for ``a >= 0, b > 0``.

    Not ``(a + b) / b`` — that's off-by-one when ``b | a`` (gives
    ``r + 1`` instead of ``r``). The bounds lemma
    ``b*r >= a AND b*r < a + b`` pins the right value, so the UF mode
    is sound regardless; this expression matters for INLINE and
    DEFINE_FUN modes.
    """
    one = vc.int_lit(1)
    return div(add(a, sub(b, one)), b)


# Lemma: if r is the result of narrow.bvN(x), then r is in the unsigned
# N-bit range: 0 <= r <= 2^N - 1.
#
# This is a *partial* axiom — it asserts a range on the narrow result
# without defining it (narrow.bvN is encoded as identity). Combined
# with the def `R = narrow.bvN(B)`, inlining turns the range into a
# constraint on B. When the surrounding block is bypassed on the
# chosen path the originating TAC never executes that arithmetic, so
# this axiom must be guarded unless rule 7 applies (the axiom's target
# is the LHS of a scoped def — then the LHS is free when the block
# is bypassed and the axiom is trivially satisfied). See journal/
# 2026-05/2026-05-17-sea-partial-defs-unsoundness.md.
class NarrowRangeLemma(LemmaSchema):
    params = ((_R, Int),)
    partial = True

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


class Bv256BoolLemma(LemmaSchema):
    params = ((_X, Int), (_Y, Int))
    smt_name: str

    def bool_domain(self, vc: _Builder, x: Term, y: Term) -> Term:
        zero = vc.int_lit(0)
        one = vc.int_lit(1)
        return and_(le(zero, x), le(x, one), le(zero, y), le(y, one))

    def instance_args(self, call: CallSite) -> tuple[Term, ...]:
        return call.args


# Lemma: if x and y are Boolean integers (0 or 1), then int.bv256_and(x, y)
# is Boolean and: it is 1 exactly when both x and y are 1.
class Bv256AndBoolLemma(Bv256BoolLemma):
    name = _LemmaName.BV256_AND_BOOL
    smt_name = _SmtName.BV256_AND

    def body(self, vc: _Builder, params: tuple[Term, ...]) -> Term:
        x, y = params
        zero = vc.int_lit(0)
        one = vc.int_lit(1)
        return implies(
            self.bool_domain(vc, x, y),
            eq(
                app(self.smt_name, [x, y], Int),
                app(_SmtName.ITE, [and_(eq(x, one), eq(y, one)), one, zero], Int),
            ),
        )


# Lemma: if x and y are Boolean integers (0 or 1), then int.bv256_xor(x, y)
# is Boolean xor: it is 0 when x = y and 1 otherwise.
class Bv256XorBoolLemma(Bv256BoolLemma):
    name = _LemmaName.BV256_XOR_BOOL
    smt_name = _SmtName.BV256_XOR

    def body(self, vc: _Builder, params: tuple[Term, ...]) -> Term:
        x, y = params
        zero = vc.int_lit(0)
        one = vc.int_lit(1)
        return implies(
            self.bool_domain(vc, x, y),
            eq(
                app(self.smt_name, [x, y], Int),
                app(_SmtName.ITE, [eq(x, y), zero, one], Int),
            ),
        )


# Lemma: if x and y are Boolean integers (0 or 1), then int.bv256_or(x, y)
# is Boolean or: it is 0 exactly when both x and y are 0.
class Bv256OrBoolLemma(Bv256BoolLemma):
    name = _LemmaName.BV256_OR_BOOL
    smt_name = _SmtName.BV256_OR

    def body(self, vc: _Builder, params: tuple[Term, ...]) -> Term:
        x, y = params
        zero = vc.int_lit(0)
        one = vc.int_lit(1)
        return implies(
            self.bool_domain(vc, x, y),
            eq(
                app(self.smt_name, [x, y], Int),
                app(_SmtName.ITE, [and_(eq(x, zero), eq(y, zero)), zero, one], Int),
            ),
        )


class Bv256BitwiseBoolOp(OpModel):
    default_config = OpConfig(
        mode=OpMode.UF,
        lemmas=(_LEMMA_BOOL,),
        instantiate_lemmas=True,
    )

    def __init__(self, vc: _Builder, *, name: str, smt_name: str, lemma: LemmaSchema) -> None:
        super().__init__(vc)
        self.name = name
        self.smt_name = smt_name
        self.lemmas = {_LEMMA_BOOL: lemma}

    def __call__(self, a: Term, b: Term) -> Term:
        cfg = self.config()
        if cfg.mode is not OpMode.UF:
            raise ValueError(f"{self.name} supports only UF mode")
        self.vc.declare_fun(self.smt_name, (Int, Int), Int)
        raw = app(self.smt_name, [a, b], Int)
        call = self.vc.record_call(self.name, (a, b), raw)
        return Term(
            raw.text,
            raw.sort,
            callsites=raw.callsites + (call,),
            direct_callsite=call,
        )


class Bv256Ops:
    def __init__(self, vc: _Builder) -> None:
        self.vc = vc
        self.and_model = Bv256BitwiseBoolOp(
            vc,
            name=_OpName.BV256_AND,
            smt_name=_SmtName.BV256_AND,
            lemma=Bv256AndBoolLemma(),
        )
        self.xor_model = Bv256BitwiseBoolOp(
            vc,
            name=_OpName.BV256_XOR,
            smt_name=_SmtName.BV256_XOR,
            lemma=Bv256XorBoolLemma(),
        )
        self.or_model = Bv256BitwiseBoolOp(
            vc,
            name=_OpName.BV256_OR,
            smt_name=_SmtName.BV256_OR,
            lemma=Bv256OrBoolLemma(),
        )

    def range(self, x: Term) -> Term:
        return self.vc.bv_range(256, x)

    def wrap_twos_complement(self, x: Term) -> Term:
        s = term("s", Int)
        self.vc.define_fun(
            _SmtName.TO_S256,
            (("s", Int),),
            Int,
            app(
                _SmtName.ITE,
                [
                    ge(s, self.vc.int_lit(0)),
                    s,
                    add(s, self.vc.bv256_mod()),
                ],
                Int,
            ),
        )
        return app(_SmtName.TO_S256, [x], Int)

    def unwrap_twos_complement(self, x: Term) -> Term:
        b = term("b", Int)
        half = self.vc.define_int_const(
            "BV256_HALF",
            div(self.vc.bv256_mod(), self.vc.int_lit(2)),
        )
        self.vc.define_fun(
            _SmtName.FROM_S256,
            (("b", Int),),
            Int,
            app(_SmtName.ITE, [lt(b, half), b, sub(b, self.vc.bv256_mod())], Int),
        )
        return app(_SmtName.FROM_S256, [x], Int)

    # ----- Signed comparisons -----
    #
    # The Int-domain encoding stores a bv256 value as a non-negative
    # integer in ``[0, 2^256)``. Reading a value as signed: anything
    # ``>= 2^255`` is "negative" (top bit set). The three define-funs
    # below give the solver direct case-split shape — empirically
    # cheaper than ``from_s256(x) <op> from_s256(y)``, which inlines
    # to a 4-way Ite combination.

    def _require_is_neg_define_fun(self) -> None:
        x = term(_X, Int)
        half = self.vc.define_int_const(
            "BV256_HALF",
            div(self.vc.bv256_mod(), self.vc.int_lit(2)),
        )
        self.vc.define_fun(
            _SmtName.BV256_IS_NEG,
            ((_X, Int),),
            Bool,
            ge(x, half),
        )

    def is_neg(self, x: Term) -> Term:
        """``bv256.is_neg(x)``: true iff ``x >= 2^255`` — the bv256
        top bit interpretation of "negative two's-complement value."""
        self._require_is_neg_define_fun()
        return app(_SmtName.BV256_IS_NEG, [x], Bool)

    def _require_signed_compare_define_fun(self, name: str, strict: bool) -> None:
        self._require_is_neg_define_fun()
        x, y = self._binary_args()
        nx = app(_SmtName.BV256_IS_NEG, [x], Bool)
        ny = app(_SmtName.BV256_IS_NEG, [y], Bool)
        # x is "negative", y is "positive" -> x < y.
        cross = and_(nx, not_(ny))
        # same sign -> compare raw int values.
        same_sign = eq(nx, ny)
        magnitude = lt(x, y) if strict else le(x, y)
        body = or_(cross, and_(same_sign, magnitude))
        self.vc.define_fun(name, ((_X, Int), (_Y, Int)), Bool, body)

    def slt(self, a: Term, b: Term) -> Term:
        """``bv256.slt(a, b)``: signed less-than over bv256-as-Int."""
        self._require_signed_compare_define_fun(_SmtName.BV256_SLT, strict=True)
        return app(_SmtName.BV256_SLT, [a, b], Bool)

    def sle(self, a: Term, b: Term) -> Term:
        """``bv256.sle(a, b)``: signed less-or-equal over bv256-as-Int."""
        self._require_signed_compare_define_fun(_SmtName.BV256_SLE, strict=False)
        return app(_SmtName.BV256_SLE, [a, b], Bool)

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
        k = _literal_value(b, self.vc)
        if k is not None:
            return self.shl_const(a, k)
        return self._uf(_SmtName.BV256_SHL, a, b)

    def shl_const(self, a: Term, k: int) -> Term:
        if k < 0:
            raise ValueError("negative shift is unsupported")
        name = _SmtName.bv256_shl_const(k)
        x = term(_X, Int)
        # bv256 shl wraps: ``(x * 2^k) mod 2^256``. The rewriter's
        # SHIFT_LEFT_TO_INT_MUL only fires when range proves
        # ``x * 2^k < 2^256`` (so the mod is identity there), but the
        # encoder must remain sound for shifts the rewriter didn't
        # convert.
        body = mul(x, self._pow2(k))
        if k > 0:
            body = mod(body, self.vc.bv256_mod())
        self.vc.define_fun(name, ((_X, Int),), Int, body)
        return app(name, [a], Int)

    def lshr(self, a: Term, b: Term) -> Term:
        k = _literal_value(b, self.vc)
        if k is not None:
            return self.lshr_const(a, k)
        return self._uf(_SmtName.BV256_LSHR, a, b)

    def lshr_const(self, a: Term, k: int) -> Term:
        if k < 0:
            raise ValueError("negative shift is unsupported")
        name = _SmtName.bv256_lshr_const(k)
        x = term(_X, Int)
        self.vc.define_fun(name, ((_X, Int),), Int, div(x, self._pow2(k)))
        return app(name, [a], Int)

    def and_(self, a: Term, b: Term) -> Term:
        a_value = _literal_value(a, self.vc)
        if a_value is not None:
            return self.and_mask(b, a_value)
        b_value = _literal_value(b, self.vc)
        if b_value is not None:
            return self.and_mask(a, b_value)
        return self.and_model(a, b)

    def and_mask(self, x: Term, mask: int) -> Term:
        low_width = low_mask_width(mask)
        if low_width is not None:
            return self.and_low_mask(x, low_width)
        clear_low = high_mask_clear_low_k(mask)
        if clear_low is not None:
            return self.and_clear_low(x, clear_low)
        slice_mask = shifted_contiguous_mask(mask)
        if slice_mask is not None:
            lo, width = slice_mask
            if lo > 0:
                return self.and_slice(x, lo, width)
        return self._uf(_SmtName.BV256_AND, x, self.vc.int_lit(mask))

    def and_low_mask(self, x: Term, width: int) -> Term:
        if width < 0:
            raise ValueError("negative mask width is unsupported")
        name = _SmtName.bv256_and_low_mask(width)
        arg = term(_X, Int)
        self.vc.define_fun(name, ((_X, Int),), Int, mod(arg, self._pow2(width)))
        return app(name, [x], Int)

    def and_clear_low(self, x: Term, width: int) -> Term:
        if width < 0:
            raise ValueError("negative mask width is unsupported")
        name = _SmtName.bv256_and_clear_low(width)
        arg = term(_X, Int)
        pow_width = self._pow2(width)
        self.vc.define_fun(name, ((_X, Int),), Int, mul(div(arg, pow_width), pow_width))
        return app(name, [x], Int)

    def and_slice(self, x: Term, lo: int, width: int) -> Term:
        if lo < 0 or width < 0:
            raise ValueError("negative mask offset or width is unsupported")
        name = _SmtName.bv256_and_slice(lo, width)
        arg = term(_X, Int)
        pow_lo = self._pow2(lo)
        pow_width = self._pow2(width)
        body = mul(mod(div(arg, pow_lo), pow_width), pow_lo)
        self.vc.define_fun(name, ((_X, Int),), Int, body)
        return app(name, [x], Int)

    def _pow2(self, k: int) -> Term:
        return self.vc.define_int_const(f"POW2_{k}", 1 << k)

    def xor(self, a: Term, b: Term) -> Term:
        return self.xor_model(a, b)

    def or_(self, a: Term, b: Term) -> Term:
        return self.or_model(a, b)

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
        self.int_mul_div_ceil = IntMulDivCeilOp(vc)
        self.int_ceil_div = IntCeilDivOp(vc)
        self.narrow = NarrowOps(vc)
        self.bv256 = Bv256Ops(vc)
        self._by_name = {
            self.int_mul_div.name: self.int_mul_div,
            self.int_mul_div_ceil.name: self.int_mul_div_ceil,
            self.int_ceil_div.name: self.int_ceil_div,
            self.bv256.and_model.name: self.bv256.and_model,
            self.bv256.xor_model.name: self.bv256.xor_model,
            self.bv256.or_model.name: self.bv256.or_model,
        }
        self._by_name.update((op.name, op) for op in self.narrow.models())

    def by_name(self, name: str) -> OpModel:
        return self._by_name[name]

    def is_partial(self, name: str) -> bool:
        """An op is *partial* (rule 2) if applying it instantiates a
        partial axiom — i.e. some lemma in its default config has
        `partial=True`. Used by the encoder to enforce rule 5: a
        static def whose RHS contains a partial-operator callsite
        must be emitted SCOPED, regardless of --guard-statics."""
        op = self._by_name.get(name)
        if op is None:
            return False
        for lemma_key in op.default_config.lemmas:
            if op.lemmas[lemma_key].partial:
                return True
        return False
