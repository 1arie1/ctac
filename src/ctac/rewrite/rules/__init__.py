"""Rule library for the TAC rewriter.

Exported: :data:`default_pipeline` — the ordered tuple of rules used by
``ctac rw`` by default.
"""

from ctac.rewrite.framework import Rule
from ctac.rewrite.rules.and_lift_eq import AND_LIFT_EQ_DECREMENT
from ctac.rewrite.rules.bitfield import (
    N1_SHIFTED_BWAND,
    N2_LOW_MASK,
    N3_HIGH_MASK,
    N4_SHR_CONST,
)
from ctac.rewrite.rules.bv_to_int import (
    ADD_BV_MAX_TO_ITE,
    ADD_BV_TO_INT,
    MUL_BV_TO_INT,
    SUB_BV_TO_INT,
)
from ctac.rewrite.rules.ceil_div_knuth import CEIL_DIV_KNUTH
from ctac.rewrite.rules.ceil_to_multiple import CEIL_TO_MULTIPLE
from ctac.rewrite.rules.int_mul_div_ceil import INT_MUL_DIV_CEIL
from ctac.rewrite.rules.chunk_merge import CHUNK_MERGE, SHIFT_LEFT_TO_INT_MUL
from ctac.rewrite.rules.ceildiv import R6_CEILDIV
from ctac.rewrite.rules.bv_max_to_ite_validation import ADD_BV_MAX_TO_ITE_CASES
from ctac.rewrite.rules.ceildiv_validation import R6_CASES
from ctac.rewrite.rules.bool_fold import BOOL_CONST_FOLD, XOR_BOOL_INT_EQ
from ctac.rewrite.rules.copyprop import CP_ALIAS
from ctac.rewrite.rules.cse import CSE
from ctac.rewrite.rules.havoc_equate_fold import HAVOC_EQUATE_FOLD
from ctac.rewrite.rules.havoc_equate_subst import HAVOC_EQUATE_SUBST
from ctac.rewrite.rules.mod_identity_cp import MOD_IDENTITY_CP
from ctac.rewrite.rules.mod_over_ite import MOD_OVER_ITE
from ctac.rewrite.rules.muldiv_to_full_product_div import (
    MULDIV_TO_FULL_PRODUCT_DIV,
)
from ctac.rewrite.rules.mul_div import CHUNKED_MUL_BY_2N, MUL_DIV_TO_MULDIV, CHUNKED_U128_LT
from ctac.rewrite.rules.div import (
    R1_BITFIELD_STRIP,
    R2_DIV_FUSE,
    R3_DIV_MUL_CANCEL,
    R4_DIV_IN_CMP,
)
from ctac.rewrite.rules.div_purify import R4A_DIV_PURIFY
from ctac.rewrite.rules.div_purify_validation import R4A_CASES
from ctac.rewrite.rules.div_validation import R4_CASES
from ctac.rewrite.rules.div_validation_r1 import R1_CASES
from ctac.rewrite.validation import ValidationCase
from ctac.rewrite.rules.ite_purify import ITE_PURIFY
from ctac.rewrite.rules.purify_assert import PURIFY_ASSERT
from ctac.rewrite.rules.purify_assume import PURIFY_ASSUME
from ctac.rewrite.rules.range_fold import RANGE_FOLD
from ctac.rewrite.rules.sar_to_shr import SAR_TO_SHR_NONNEG
from ctac.rewrite.rules.select_over_store import SELECT_OVER_STORE
from ctac.rewrite.rules.sign_extend import (
    FROM_S64_ZERO_TEST,
    NEG_S64_DOUBLE,
    NEG_S64_LOW_CHUNK,
    NEG_S64_SIGN_TEST,
    NEG_S64_ZERO_TEST,
    SIGN_EXTEND_UNWRAP,
    SIGNED_CMP_NEG_ONE,
    WRAP_COMPARE_LIFT,
)
from ctac.rewrite.rules.store_eq import STORE_EQ_NORM, normalize_store_eq
from ctac.rewrite.rules.ite import (
    ADD_ITE_DIST,
    ADD_SUB_ZERO_FOLD,
    ARITH_CONST_FOLD,
    BOOL_ABSORB,
    CMP_RANGE_FOLD,
    DE_MORGAN,
    EQ_CONST_FOLD,
    EQ_ITE_DIST,
    EQ_REFLEXIVE,
    INT_MUL_EQ_ZERO,
    ITE_BOOL,
    ITE_COND_FOLD,
    ITE_SAME,
    ITE_SAME_COND_NESTED,
    ITE_SHARED_LEAF,
    ITE_ZERO_OR_SELF,
    LAND_EQ_CONST_PRUNE,
    MUL_ZERO_ONE_FOLD,
    SUB_ITE_DIST_LEFT,
    SUB_ITE_DIST_RIGHT,
)

# Phase 1 — chain recognition.
#
# Multi-command idioms (currently just R6's ceiling-division chain)
# need to be recognized BEFORE distribution rules can rewrite their
# constituent expressions. The rewrite driver does bottom-up
# traversal: at each iteration it visits subexpressions before parents.
# If a distribution rule (e.g. SUB_ITE_DIST_RIGHT) is in the same
# pipeline, it can fire on a sub-expression of the chain (rewriting
# `Sub(R_high, Ite(c, 1, 0))` into `Ite(c, Sub(R_high, 1), R_high)`)
# at a position deeper in the AST than where R6 would match — so by
# the time R6 looks at the chain's outer node, the chain has already
# been distorted past its recognizer's pattern.
#
# Splitting R6 + the bit-op canonicalizers it depends on into a
# dedicated phase guarantees they see the unmolested input.
chain_recognition_pipeline: tuple[Rule, ...] = (
    # Bit-op canonicalization: produce Mod / Div / Mul(Div(..), 2^k) so
    # downstream matchers see canonical forms.
    N2_LOW_MASK,
    N3_HIGH_MASK,
    N4_SHR_CONST,
    N1_SHIFTED_BWAND,
    # Multi-command chain recognizers. Run here, before any rule that
    # could rewrite chain interior expressions.
    R6_CEILDIV,
)


# Phase 2 — general simplification. Bit-op canonicalizers also live
# here so any chains that emerged in phase 1's output keep getting
# normalized within the fixed-point loop.
simplify_pipeline: tuple[Rule, ...] = (
    N2_LOW_MASK,
    N3_HIGH_MASK,
    N4_SHR_CONST,
    N1_SHIFTED_BWAND,
    # Existing const-divisor div rules + bitfield strip.
    R2_DIV_FUSE,
    R3_DIV_MUL_CANCEL,
    # Note: R4_DIV_IN_CMP (Div-in-comparison -> Euclidean bounds) is
    # *not* here. It's a div-purification step that emits SMT-level
    # constraints rather than a structural simplification, so it runs
    # in its own late phase (`div_purify_pipeline`) after the
    # cancellation rules above have reached fixpoint. Running R4 here
    # was unsound w.r.t. the per-iteration `static_defs` snapshot:
    # when R3 cancelled `Div(narrow(2^32 * X), 2^32)` to `X` on
    # cmd N, R4 on a later cmd in the same iteration could still
    # see the stale `Div(...)` via `lookthrough` and emit Euclidean
    # bounds on a `Div` that R3 had already eliminated.
    R1_BITFIELD_STRIP,
    # Recognize SBF's chunk-extended u64 mul-by-2^N idiom; lifts to
    # a clean `IntMul(R, 2^N)`. Composes with MUL_DIV_TO_MULDIV next.
    # Lives here (not in chain_recognition_pipeline) because R6's
    # ceildiv chain has interior `IntDiv(IntMul(...), c)` shapes that
    # would otherwise get pre-empted by MUL_DIV_TO_MULDIV before R6
    # gets to match the outer ceildiv shape.
    CHUNKED_MUL_BY_2N,
    # IntDiv(IntMul(a, b), c) -> IntMulDiv(a, b, c). The encoder
    # axiomatizes IntMulDiv with Euclidean bounds; this rule lifts
    # the syntactic composition into the axiomatized concept.
    MUL_DIV_TO_MULDIV,
    # Eliminate "dummy" havoc'd vars whose only role is to mediate
    # an equality assume. Substitutes R -> X across all R-using
    # assumes; the post-substitution `Eq(X, X)` collapses via
    # EQ_REFLEXIVE; DCE clears the now-unused havoc def.
    HAVOC_EQUATE_SUBST,
    # NOTE: ``HAVOC_EQUATE_FOLD`` is intentionally NOT in this
    # pipeline. It produces sound rewrites but rw-eq's per-command
    # walker cannot verify them: FOLD removes the LHS's bound-on-R
    # assume and the equality, replacing them with a single
    # bound-on-X assume in the RHS. rw-eq, walking LHS and RHS in
    # source order, sees the LHS's bound-on-R as a lhs-only assume
    # (rule 4b) and emits a CHK that asserts ``R <= K`` from
    # whatever context precedes it — at that point R is just
    # havoc'd, the constraint isn't yet available, so the CHK is
    # SAT-able and rw-eq reports unsoundness. The fact really
    # follows from the LHS's later equality assume, but
    # ua-strategy-split truncates after each assertion so the
    # equality is unreachable in the CHK's VC.
    #
    # Making rw-eq trail-aware would close this, but rw-eq is the
    # soundness gate and we keep it as simple as possible. The
    # ``materialize_havoc_equate_bounds`` pass below achieves the
    # same downstream benefit (bound on X visible to range
    # inference) without removing anything, so rw-eq trivially
    # admits the new RHS-only assume.
    # Boolean / Ite simplification.
    EQ_REFLEXIVE,
    EQ_CONST_FOLD,
    # Strip nonzero-const multipliers from Eq(_, 0) so downstream
    # ITE folds can see the underlying zero-test.
    INT_MUL_EQ_ZERO,
    EQ_ITE_DIST,
    # Distribute Add/Sub over Ite operands so per-branch simplification
    # (constant folding, range-driven narrowing) can fire independently.
    ADD_ITE_DIST,
    SUB_ITE_DIST_LEFT,
    SUB_ITE_DIST_RIGHT,
    # Retire +/-0 arms left by the distribution rules above.
    ADD_SUB_ZERO_FOLD,
    # Const-const arithmetic / bitwise folds (Add/Sub/Mul/Div/Mod/BWAnd).
    # Int variants are non-modular; bv variants wrap mod 2^256.
    ARITH_CONST_FOLD,
    # Multiplicative absorb / identity: X*0 -> 0, X*1 -> X (both Mul
    # and IntMul, both arg orderings).
    MUL_ZERO_ONE_FOLD,
    # Distribute Mod over Ite when both arms simplify under
    # path-refined ranges. Strict cost gate: only fires when both
    # arms reduce, so the distribution shrinks rather than just
    # duplicating the Mod.
    MOD_OVER_ITE,
    ITE_SAME,
    # Collapse Ite(Eq(X,0), 0, X) -> X and Ite(Eq(X,0), X, 0) -> 0.
    # Lookthrough on the cond catches the typical `B = X == 0; Ite(B, ...)`
    # shape, including after INT_MUL_EQ_ZERO normalizes `R == 0` where
    # `R = IntMul(X, K)`.
    ITE_ZERO_OR_SELF,
    ITE_SHARED_LEAF,
    # Prune nested Ites that re-test the outer's exact condition
    # (saturating-sub lowerings emit them); unconditionally sound.
    ITE_SAME_COND_NESTED,
    # Lift the chunked-u128 lexicographic compare ladder to a single
    # positional compare; chunk-extract sides collapse to their wide
    # source. Range-gated (lo parts must be inside the radix).
    CHUNKED_U128_LT,
    # Bool-const fold: `Ite(true, X, _) -> X`, `Ite(false, _, Y) -> Y`,
    # plus LNot/LAnd/LOr/Eq over Bool ConstExpr operands. Universally
    # sound; cheap (top-level pattern match). Useful both for inputs
    # that arrive with literal-bool guards and after substitutions
    # introduced by `ctac pin --bind`.
    BOOL_CONST_FOLD,
    # The 0/1-int XOR carry-consistency check is boolean equality;
    # folding it drops the bv256_xor UF axiom from the VC.
    XOR_BOOL_INT_EQ,
    ITE_BOOL,
    # ``LAnd(Ge(X, c), Eq(IntSub(X, c), 0)) -> Eq(X, c)``. Recovers the
    # singleton-equality shape that ``ADD_BV_MAX_TO_ITE`` + ``EqIte`` +
    # ``IteBool`` produce when an outer ``Eq(_, 0)`` distributes through
    # an unfolded ``Add(BV256_MAX, X)`` decrement. Must run after
    # ``ITE_BOOL`` (which produces this LAnd shape) and before
    # ``EqIte`` / ``SelectOverStore`` re-pick up the simplified Eq.
    AND_LIFT_EQ_DECREMENT,
    # Range-driven Ite folding: decide `cond` via interval inference
    # and collapse to the then/else branch. Paired with ADD_BV_MAX_TO_ITE
    # below, which always emits an Ite; COND_FOLD collapses it when the
    # operand's range makes the condition decidable.
    ITE_COND_FOLD,
    # LAnd with a pinning Eq(x, c) conjunct decides sibling
    # const-comparisons (!(x == 0) && (x == 1) -> x == 1).
    LAND_EQ_CONST_PRUNE,
    # Same evaluator, any expression position: comparisons inside
    # LAnd/LOr/assign RHS fold to bool literals when range decides
    # them (the vacuous `X >= 0` conjunct on bv-typed X).
    CMP_RANGE_FOLD,
    BOOL_ABSORB,
    DE_MORGAN,
    # Range-safe narrowing: Mul/Add -> IntMul/IntAdd when interval
    # inference proves the result fits in [0, 2^256). Must run after the
    # div / bitfield rules so that the Mul(Div(..)) shapes they produce
    # become the canonical input here.
    MUL_BV_TO_INT,
    ADD_BV_TO_INT,
    SUB_BV_TO_INT,
    # ShiftLeft(X, K) -> IntMul(X, 2^K) when range proves X * 2^K
    # fits bv256. Exposes the multiplicative form to ChunkMerge.
    SHIFT_LEFT_TO_INT_MUL,
    # narrow(IntAdd(IntMul(Div(T, K), K), Mod(T, K))) -> T. The
    # Euclidean-division identity that collapses (lift, op, split)
    # round-trips back to the wide register.
    CHUNK_MERGE,
    # SymRef R -> X when R's def is Mod(X, M) and range proves
    # X in [0, M-1]. CP-style alias when Mod is structurally
    # identity but the program kept the Mod for the SBF
    # narrow-to-N-bits check shape.
    MOD_IDENTITY_CP,
    # IntMulDiv(A, B, K) -> Div(V, M*K) when V = narrow(IntMul(A, W))
    # is a static def with W ≡ M*B (M a positive const). Recognizes
    # the "muldiv-style" high chunk of a u64×u46→u128 product as
    # the canonical Div(V, 2^N) shape that CHUNK_MERGE consumes.
    MULDIV_TO_FULL_PRODUCT_DIV,
    # Ite(Eq(V%K,0), (V/K)*K, narrow(K+(V/K)*K)%2^64) ->
    # K *int IntCeilDiv(V, K). The SBF-chunked "ceil to multiple of K"
    # idiom; the disjunctive wrap-guard assume is required and scanned
    # for in the host block. Runs here so the floor-mul and Mod shapes
    # above (CHUNK_MERGE, MOD_IDENTITY_CP, MULDIV_TO_FULL_PRODUCT_DIV)
    # have already normalized the chain interior.
    CEIL_TO_MULTIPLE,
    # IntDiv(IntSub(narrow(IntAdd(V, W)), 1), W) -> IntCeilDiv(V, W).
    # The Knuth ceil-div idiom that emerges from the u128 carry-add +
    # decrement chain. Runs here so CHUNK_MERGE has already collapsed
    # the chunked H reconstruction to the bare three-line form, and
    # MOD_IDENTITY_CP has cleared any path-redundant Mods that would
    # otherwise mask the IntAdd shape.
    CEIL_DIV_KNUTH,
    # IntCeilDiv(narrow(IntMul(A, B)), W) -> IntMulDivCeil(A, B, W).
    # Folds the narrow-wrapped product + ceil-div chain to the
    # IntMulDivCeil concept, mirroring MULDIV_TO_FULL_PRODUCT_DIV for
    # the ceil-div variant. Runs after CEIL_DIV_KNUTH so the IntCeilDiv
    # is already in scope on the relevant chains.
    INT_MUL_DIV_CEIL,
    # Recognize the ``unwrap_twos_complement_256(SignExtend(b, x))``
    # idiom and lift it to an Int-domain Ite over linear arms. Runs
    # after MUL/ADD/SUB_BV_TO_INT so operand ``x`` is in canonical
    # narrowed form; before RANGE_FOLD so the emitted Ite can collapse
    # when range pins the sign-bit condition.
    SIGN_EXTEND_UNWRAP,
    # Collapse the saturating-sub "negated i64 is zero" round trip
    # Eq(Ite(Eq(y, 2^63), x, wrap_256(-from_s64(y))), 0) -> Eq(y, 0)
    # when y = Mod(x, 2^64). Runs after SIGN_EXTEND_UNWRAP so a
    # from_s64 arriving as unwrap(SignExtend(7, y)) is already in
    # the Ite form this matcher recognizes.
    NEG_S64_ZERO_TEST,
    # The bare from_s64 zero test (no wrap round trip), living deep
    # inside the i128 negation's no-overflow assumes.
    FROM_S64_ZERO_TEST,
    # The other negation-gadget consumers: Mod(gadget, 2^64) (the
    # negated low chunk -- both arms agree, no x gate) and the signed
    # zero-threshold tests (gated on range(x) < 2^255 for the
    # pass-through edge arm).
    NEG_S64_LOW_CHUNK,
    NEG_S64_SIGN_TEST,
    # Normalize signed compares against -1 to the zero threshold the
    # sign-test rule matches (x <=s -1 -> x <s 0).
    SIGNED_CMP_NEG_ONE,
    # The abs lowering's double negation: gadget-of-gadget collapses
    # to the 64->256 sign extension of the chunk (i64::MIN edge
    # unextended).
    NEG_S64_DOUBLE,
    # Lift Cmp(wrap_256(v), c) to an Int-domain predicate on v, gated
    # on range(v) within (c - 2^256, 2^256). Runs with the s64-family
    # rules so the re-encoded i64 comparisons (to_s256(I) < 10) lose
    # the mod-2^256 opacity before ITE/bool folding.
    WRAP_COMPARE_LIFT,
    # ShiftRightArithmetical(x, k) -> ShiftRightLogical(x, k) when
    # range proves x's top bit is zero (the typical shape after
    # ``Mod(_, 2^64)``). The sea encoder lowers LSHR natively.
    SAR_TO_SHR_NONNEG,
    # Collapse expressions whose range is a singleton to the
    # corresponding ConstExpr. Runs after the narrowing rules so that
    # IntAdd / IntSub / ... produced above get folded to constants
    # when their ranges pin (e.g. Sub(X, Y) with equality assume).
    RANGE_FOLD,
    # Express Add(BV256_MAX, X) — the bv256 two's-complement decrement —
    # as an explicit Ite. ITE_COND_FOLD above collapses it whenever
    # range analysis decides `X >= 1`.
    ADD_BV_MAX_TO_ITE,
    # Fold Select(M, k) through M's def chain when the resolution is
    # clean — Store-key hit, constant-disjoint peel, or Ite-of-bytemaps
    # with shared-root convergence. Memoizes on (M, k) per iteration so
    # parallel arms of an Ite-of-bytemaps share sub-walks. Conservative
    # on symbolic keys (bails rather than synthesize Ite-on-equality).
    SELECT_OVER_STORE,
    # CP propagates aliases (Y := X). CSE deliberately runs in its own
    # phase (driven by the CLI), not here: CSE's RHS index is built once
    # per iteration, and rules that mutate registered RHSes (CP and the
    # simplifications above) shift canonical equivalence underneath the
    # snapshot. Isolating CSE makes the snapshot-correctness invariant
    # something we can actually rely on.
    CP_ALIAS,
)

# Stand-alone CSE phase. Runs CSE iteratively to fixed point with no
# other rule alongside it, so the per-iteration RHS index is stable
# (no other rule rewrites a registered RHS mid-iter and shifts canon
# equivalence). Driven by the CLI early (after chain recognition) and
# late (after ITE_PURIFY etc.) — see ``commands_rw.py``.
cse_pipeline: tuple[Rule, ...] = (CSE,)

# Final-step ``Div``-in-comparison simplification. ``R4_DIV_IN_CMP``
# rewrites ``Cmp(Div(A, B), C) -> LAnd(Ge(A, B*C), Lt(A, B*(C+1)))``
# (and friends). The output is an SMT-friendly Euclidean-bounds shape
# but destroys the syntactic ``Div`` that downstream rewriters and
# concept-recognizers (ceil-div reconstruction, IntCeilDiv lifting)
# rely on for matching. The CLI runs this as the VERY LAST phase,
# after every other simplification and purification has settled, so
# intermediate phases see Div in its natural form.
#
# Paired with the const-folding rules so R4's output (which contains
# nested ``IntMul(K, 0)``, ``IntAdd(0, 1)``, ``IntMul(K, 1)`` shapes
# from the ``C=0`` / ``C+1`` instantiations) collapses cleanly to the
# numeric bounds in the same fixed-point loop.
final_div_in_cmp_pipeline: tuple[Rule, ...] = (
    R4_DIV_IN_CMP,
    ARITH_CONST_FOLD,
    MUL_ZERO_ONE_FOLD,
    ADD_SUB_ZERO_FOLD,
)

# Div-purification by fresh-quotient introduction (``R4A``). Lives
# in its own phase, gated by ``--purify-div``; runs after simplify
# reaches fixpoint so the cancellation rules (R2/R3) see the natural
# Div shape first.
div_purify_pipeline: tuple[Rule, ...] = (R4A_DIV_PURIFY,)

# Full pipeline: chain recognition + simplification + purification. The
# CLI drives these as separate phases so chain recognizers see the
# unmolested input, distribution rules don't pre-empt R6, and the
# div-in-cmp simplification fires only at the very end.
purify_pipeline: tuple[Rule, ...] = (
    simplify_pipeline + div_purify_pipeline + final_div_in_cmp_pipeline
)

default_pipeline: tuple[Rule, ...] = purify_pipeline


# Validation cases collected from per-rule sibling files. Single source of
# truth for `ctac rw-valid`. Rules without an entry here have no soundness
# spec yet — the CLI reports them as "missing" so coverage gaps are visible.
validation_cases: tuple[ValidationCase, ...] = (
    R1_CASES + R4_CASES + R4A_CASES + R6_CASES + ADD_BV_MAX_TO_ITE_CASES
)

# Every rule name the rewriter exports, so `ctac rw-valid` can list the
# ones that don't yet have a spec.
all_rule_names: tuple[str, ...] = (
    N1_SHIFTED_BWAND.name,
    N2_LOW_MASK.name,
    N3_HIGH_MASK.name,
    N4_SHR_CONST.name,
    R1_BITFIELD_STRIP.name,
    R2_DIV_FUSE.name,
    R3_DIV_MUL_CANCEL.name,
    R4_DIV_IN_CMP.name,
    R4A_DIV_PURIFY.name,
    R6_CEILDIV.name,
    CHUNKED_MUL_BY_2N.name,
    CHUNKED_U128_LT.name,
    MUL_DIV_TO_MULDIV.name,
    HAVOC_EQUATE_SUBST.name,
    HAVOC_EQUATE_FOLD.name,
    EQ_REFLEXIVE.name,
    EQ_CONST_FOLD.name,
    ARITH_CONST_FOLD.name,
    MOD_OVER_ITE.name,
    MUL_ZERO_ONE_FOLD.name,
    INT_MUL_EQ_ZERO.name,
    EQ_ITE_DIST.name,
    ADD_ITE_DIST.name,
    SUB_ITE_DIST_LEFT.name,
    SUB_ITE_DIST_RIGHT.name,
    ADD_SUB_ZERO_FOLD.name,
    ITE_SAME.name,
    ITE_SAME_COND_NESTED.name,
    ITE_SHARED_LEAF.name,
    ITE_ZERO_OR_SELF.name,
    BOOL_CONST_FOLD.name,
    XOR_BOOL_INT_EQ.name,
    ITE_BOOL.name,
    AND_LIFT_EQ_DECREMENT.name,
    ITE_COND_FOLD.name,
    CMP_RANGE_FOLD.name,
    LAND_EQ_CONST_PRUNE.name,
    BOOL_ABSORB.name,
    DE_MORGAN.name,
    MUL_BV_TO_INT.name,
    ADD_BV_TO_INT.name,
    SUB_BV_TO_INT.name,
    SHIFT_LEFT_TO_INT_MUL.name,
    CHUNK_MERGE.name,
    MOD_IDENTITY_CP.name,
    MULDIV_TO_FULL_PRODUCT_DIV.name,
    CEIL_TO_MULTIPLE.name,
    CEIL_DIV_KNUTH.name,
    INT_MUL_DIV_CEIL.name,
    RANGE_FOLD.name,
    ADD_BV_MAX_TO_ITE.name,
    SAR_TO_SHR_NONNEG.name,
    SELECT_OVER_STORE.name,
    SIGN_EXTEND_UNWRAP.name,
    NEG_S64_ZERO_TEST.name,
    FROM_S64_ZERO_TEST.name,
    NEG_S64_LOW_CHUNK.name,
    NEG_S64_SIGN_TEST.name,
    NEG_S64_DOUBLE.name,
    SIGNED_CMP_NEG_ONE.name,
    WRAP_COMPARE_LIFT.name,
    CSE.name,
    CP_ALIAS.name,
    ITE_PURIFY.name,
    PURIFY_ASSERT.name,
    PURIFY_ASSUME.name,
    STORE_EQ_NORM.name,
)

__all__ = [
    "ADD_BV_MAX_TO_ITE",
    "ADD_BV_TO_INT",
    "ADD_ITE_DIST",
    "ADD_SUB_ZERO_FOLD",
    "AND_LIFT_EQ_DECREMENT",
    "ARITH_CONST_FOLD",
    "BOOL_ABSORB",
    "BOOL_CONST_FOLD",
    "CEIL_DIV_KNUTH",
    "CEIL_TO_MULTIPLE",
    "INT_MUL_DIV_CEIL",
    "CHUNK_MERGE",
    "CHUNKED_MUL_BY_2N",
    "CHUNKED_U128_LT",
    "CMP_RANGE_FOLD",
    "CP_ALIAS",
    "CSE",
    "DE_MORGAN",
    "EQ_CONST_FOLD",
    "EQ_ITE_DIST",
    "EQ_REFLEXIVE",
    "FROM_S64_ZERO_TEST",
    "HAVOC_EQUATE_FOLD",
    "HAVOC_EQUATE_SUBST",
    "INT_MUL_EQ_ZERO",
    "ITE_BOOL",
    "ITE_COND_FOLD",
    "ITE_PURIFY",
    "ITE_SAME",
    "ITE_SAME_COND_NESTED",
    "ITE_SHARED_LEAF",
    "ITE_ZERO_OR_SELF",
    "LAND_EQ_CONST_PRUNE",
    "MOD_IDENTITY_CP",
    "MOD_OVER_ITE",
    "MULDIV_TO_FULL_PRODUCT_DIV",
    "MUL_BV_TO_INT",
    "MUL_DIV_TO_MULDIV",
    "MUL_ZERO_ONE_FOLD",
    "N1_SHIFTED_BWAND",
    "N2_LOW_MASK",
    "N3_HIGH_MASK",
    "N4_SHR_CONST",
    "NEG_S64_DOUBLE",
    "NEG_S64_LOW_CHUNK",
    "NEG_S64_SIGN_TEST",
    "NEG_S64_ZERO_TEST",
    "PURIFY_ASSERT",
    "PURIFY_ASSUME",
    "R1_BITFIELD_STRIP",
    "R2_DIV_FUSE",
    "R3_DIV_MUL_CANCEL",
    "R4_DIV_IN_CMP",
    "R4A_DIV_PURIFY",
    "R6_CEILDIV",
    "RANGE_FOLD",
    "SAR_TO_SHR_NONNEG",
    "SELECT_OVER_STORE",
    "SHIFT_LEFT_TO_INT_MUL",
    "SIGNED_CMP_NEG_ONE",
    "SIGN_EXTEND_UNWRAP",
    "STORE_EQ_NORM",
    "SUB_BV_TO_INT",
    "SUB_ITE_DIST_LEFT",
    "SUB_ITE_DIST_RIGHT",
    "WRAP_COMPARE_LIFT",
    "XOR_BOOL_INT_EQ",
    "ValidationCase",
    "all_rule_names",
    "cse_pipeline",
    "default_pipeline",
    "div_purify_pipeline",
    "final_div_in_cmp_pipeline",
    "normalize_store_eq",
    "purify_pipeline",
    "simplify_pipeline",
    "validation_cases",
]
