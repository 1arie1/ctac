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
from ctac.rewrite.rules.ceildiv import R6_CEILDIV
from ctac.rewrite.rules.bv_max_to_ite_validation import ADD_BV_MAX_TO_ITE_CASES
from ctac.rewrite.rules.ceildiv_validation import R6_CASES
from ctac.rewrite.rules.bool_fold import BOOL_CONST_FOLD
from ctac.rewrite.rules.copyprop import CP_ALIAS
from ctac.rewrite.rules.cse import CSE
from ctac.rewrite.rules.havoc_equate_fold import HAVOC_EQUATE_FOLD
from ctac.rewrite.rules.havoc_equate_subst import HAVOC_EQUATE_SUBST
from ctac.rewrite.rules.mul_div import CHUNKED_MUL_BY_2N, MUL_DIV_TO_MULDIV
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
from ctac.rewrite.rules.select_over_store import SELECT_OVER_STORE
from ctac.rewrite.rules.store_eq import STORE_EQ_NORM, normalize_store_eq
from ctac.rewrite.rules.ite import (
    ADD_ITE_DIST,
    BOOL_ABSORB,
    DE_MORGAN,
    EQ_CONST_FOLD,
    EQ_ITE_DIST,
    EQ_REFLEXIVE,
    ITE_BOOL,
    ITE_COND_FOLD,
    ITE_SAME,
    ITE_SHARED_LEAF,
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
    # Sister rule to HAVOC_EQUATE_SUBST: when SUBST can't fire
    # because X's def is later than R's uses (e.g. SBF-frontend
    # "pre-allocate slot R, later equate to nondet result X" shape),
    # FOLD drops R + its constraints and rewrites the equality assume
    # to a conjunction of the moved constraints. Soundness via
    # same-block restriction.
    HAVOC_EQUATE_FOLD,
    # Boolean / Ite simplification.
    EQ_REFLEXIVE,
    EQ_CONST_FOLD,
    EQ_ITE_DIST,
    # Distribute Add/Sub over Ite operands so per-branch simplification
    # (constant folding, range-driven narrowing) can fire independently.
    ADD_ITE_DIST,
    SUB_ITE_DIST_LEFT,
    SUB_ITE_DIST_RIGHT,
    ITE_SAME,
    ITE_SHARED_LEAF,
    # Bool-const fold: `Ite(true, X, _) -> X`, `Ite(false, _, Y) -> Y`,
    # plus LNot/LAnd/LOr/Eq over Bool ConstExpr operands. Universally
    # sound; cheap (top-level pattern match). Useful both for inputs
    # that arrive with literal-bool guards and after substitutions
    # introduced by `ctac pin --bind`.
    BOOL_CONST_FOLD,
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
    BOOL_ABSORB,
    DE_MORGAN,
    # Range-safe narrowing: Mul/Add -> IntMul/IntAdd when interval
    # inference proves the result fits in [0, 2^256). Must run after the
    # div / bitfield rules so that the Mul(Div(..)) shapes they produce
    # become the canonical input here.
    MUL_BV_TO_INT,
    ADD_BV_TO_INT,
    SUB_BV_TO_INT,
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

# Div-purification phase: SMT-level rewrites that replace ``Div`` (or
# its uses in comparisons) with their Euclidean-bounds expansion.
# These rules don't enable further structural simplification on their
# own — their output is a constraint shape sea_vc consumes — so they
# run AFTER ``simplify_pipeline`` has reached fixpoint, never
# alongside the cancellation rules (R2/R3). Mixing R4 with R3 in the
# same phase produced unsound R4 firings against R3's stale
# ``static_defs`` snapshot (R3 eliminated the Div on cmd N, R4 on
# cmd M > N still saw the pre-R3 Div via ``lookthrough``).
# R4A_DIV_PURIFY is appended in ``purify_pipeline`` (gated by
# ``--purify-div``) since it depends on a non-constant divisor that
# only the CLI can know is desired.
div_purify_pipeline: tuple[Rule, ...] = (R4_DIV_IN_CMP,)

# Full pipeline: chain recognition + simplification + purification. The
# CLI drives these as separate phases so chain recognizers see the
# unmolested input, distribution rules don't pre-empt R6, and the
# div-purification rules fire only after simplify reaches fixpoint.
purify_pipeline: tuple[Rule, ...] = (
    simplify_pipeline + div_purify_pipeline + (R4A_DIV_PURIFY,)
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
    MUL_DIV_TO_MULDIV.name,
    HAVOC_EQUATE_SUBST.name,
    HAVOC_EQUATE_FOLD.name,
    EQ_REFLEXIVE.name,
    EQ_CONST_FOLD.name,
    EQ_ITE_DIST.name,
    ADD_ITE_DIST.name,
    SUB_ITE_DIST_LEFT.name,
    SUB_ITE_DIST_RIGHT.name,
    ITE_SAME.name,
    ITE_SHARED_LEAF.name,
    BOOL_CONST_FOLD.name,
    ITE_BOOL.name,
    AND_LIFT_EQ_DECREMENT.name,
    ITE_COND_FOLD.name,
    BOOL_ABSORB.name,
    DE_MORGAN.name,
    MUL_BV_TO_INT.name,
    ADD_BV_TO_INT.name,
    SUB_BV_TO_INT.name,
    RANGE_FOLD.name,
    ADD_BV_MAX_TO_ITE.name,
    SELECT_OVER_STORE.name,
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
    "AND_LIFT_EQ_DECREMENT",
    "BOOL_ABSORB",
    "BOOL_CONST_FOLD",
    "CHUNKED_MUL_BY_2N",
    "CP_ALIAS",
    "CSE",
    "DE_MORGAN",
    "EQ_CONST_FOLD",
    "EQ_ITE_DIST",
    "EQ_REFLEXIVE",
    "HAVOC_EQUATE_FOLD",
    "HAVOC_EQUATE_SUBST",
    "ITE_BOOL",
    "ITE_COND_FOLD",
    "ITE_PURIFY",
    "ITE_SAME",
    "ITE_SHARED_LEAF",
    "MUL_BV_TO_INT",
    "MUL_DIV_TO_MULDIV",
    "N1_SHIFTED_BWAND",
    "N2_LOW_MASK",
    "N3_HIGH_MASK",
    "N4_SHR_CONST",
    "PURIFY_ASSERT",
    "PURIFY_ASSUME",
    "R1_BITFIELD_STRIP",
    "R2_DIV_FUSE",
    "R3_DIV_MUL_CANCEL",
    "R4_DIV_IN_CMP",
    "R4A_DIV_PURIFY",
    "R6_CEILDIV",
    "RANGE_FOLD",
    "SELECT_OVER_STORE",
    "STORE_EQ_NORM",
    "SUB_BV_TO_INT",
    "SUB_ITE_DIST_LEFT",
    "SUB_ITE_DIST_RIGHT",
    "ValidationCase",
    "all_rule_names",
    "cse_pipeline",
    "default_pipeline",
    "div_purify_pipeline",
    "normalize_store_eq",
    "purify_pipeline",
    "simplify_pipeline",
    "validation_cases",
]
